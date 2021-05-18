use franklin_crypto::{
	bellman::{plonk::better_better_cs::cs::*, Engine, Field, SynthesisError},
	plonk::circuit::allocated_num::{Num::Constant, *},
};

fn pow<E: Engine, CS: ConstraintSystem<E>>(
	cs: &mut CS,
	x: &Num<E>,
	alpha: u32,
) -> Result<Num<E>, SynthesisError> {
	if alpha == 0 {
		Ok(Num::one())
	} else {
		let mut y = *x;

		let len = 31 - alpha.leading_zeros();
		for i in (0..len).rev() {
			y = y.mul(cs, &y)?;

			if alpha & (1 << i) != 0 {
				y = y.mul(cs, &x)?;
			}
		}

		Ok(y)
	}
}

fn inv_pow<E: Engine, CS: ConstraintSystem<E>>(
	cs: &mut CS,
	x: &Num<E>,
	alpha: u32,
	alpha_inv: &[u64],
) -> Result<Num<E>, SynthesisError> {
	let y = x.get_value().as_ref().map(|x| x.pow(alpha_inv));
	let y = Num::alloc(cs, y)?;

	let z = pow(cs, &y, alpha)?;
	z.enforce_equal(cs, x)?;

	Ok(y)
}

fn vec_add<E: Engine, CS: ConstraintSystem<E>>(
	cs: &mut CS,
	x: &Vec<Num<E>>,
	y: &Vec<Num<E>>,
) -> Result<Vec<Num<E>>, SynthesisError> {
	if x.len() == y.len() {
		x.iter().zip(y.iter()).map(|(x, y)| x.add(cs, y)).collect()
	} else {
		Err(SynthesisError::AssignmentMissing)
	}
}

fn vec_add_constant<E: Engine, CS: ConstraintSystem<E>>(
	cs: &mut CS,
	x: &Vec<Num<E>>,
	y: &Vec<E::Fr>,
) -> Result<Vec<Num<E>>, SynthesisError> {
	if x.len() == y.len() {
		x.iter()
			.zip(y.iter().map(|y| Constant(*y)))
			.map(|(x, y)| x.add(cs, &y))
			.collect()
	} else {
		Err(SynthesisError::AssignmentMissing)
	}
}

fn vec_pow<E: Engine, CS: ConstraintSystem<E>>(
	cs: &mut CS,
	x: &Vec<Num<E>>,
	alpha: u32,
) -> Result<Vec<Num<E>>, SynthesisError> {
	x.iter().map(|x| pow(cs, x, alpha)).collect()
}

fn vec_inv_pow<E: Engine, CS: ConstraintSystem<E>>(
	cs: &mut CS,
	x: &Vec<Num<E>>,
	alpha: u32,
	alpha_inv: &[u64],
) -> Result<Vec<Num<E>>, SynthesisError> {
	x.iter().map(|x| inv_pow(cs, x, alpha, alpha_inv)).collect()
}

fn mat_vec_mul<E: Engine, CS: ConstraintSystem<E>>(
	cs: &mut CS,
	mat: &Vec<Vec<E::Fr>>,
	x: &Vec<Num<E>>,
) -> Result<Vec<Num<E>>, SynthesisError> {
	mat.iter()
		.map(|row| {
			if row.len() > 0 && row.len() == x.len() {
				let mut sum = x[0].mul(cs, &Constant(row[0]))?;
				for i in 1..row.len() {
					let a = x[i].mul(cs, &Constant(row[i]))?;
					sum = sum.add(cs, &a)?
				}
				Ok(sum)
			} else {
				Err(SynthesisError::AssignmentMissing)
			}
		})
		.collect()
}

pub struct RescueCircuit<'a, E: Engine> {
	pub params: &'a super::Params<E::Fr>,
	pub key: Vec<Option<E::Fr>>,
	pub plain_text: Vec<Option<E::Fr>>,
	pub cipher_text: Vec<E::Fr>,
}

impl<E: Engine> Circuit<E> for RescueCircuit<'_, E> {
	type MainGate = Width4MainGateWithDNext;

	fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
		Ok(vec![Self::MainGate::default().into_internal()])
	}

	fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
		let mut x: Vec<Num<E>> = self
			.plain_text
			.iter()
			.map(|x| Num::alloc(cs, *x))
			.collect::<Result<Vec<Num<E>>, SynthesisError>>()?;

		let mut k: Vec<Num<E>> = self
			.key
			.iter()
			.map(|k| Num::alloc(cs, *k))
			.collect::<Result<Vec<Num<E>>, SynthesisError>>()?;

		k = vec_add_constant(cs, &k, &self.params.constants_init)?;
		x = vec_add(cs, &x, &k)?;

		for (constant_0, constant_1) in self.params.round_constants.iter() {
			k = vec_inv_pow(cs, &k, self.params.alpha, &self.params.alpha_inv)?;
			k = mat_vec_mul(cs, &self.params.mat, &k)?;
			k = vec_add_constant(cs, &k, constant_0)?;

			x = vec_inv_pow(cs, &x, self.params.alpha, &self.params.alpha_inv)?;
			x = mat_vec_mul(cs, &self.params.mat, &x)?;
			x = vec_add(cs, &x, &k)?;

			k = vec_pow(cs, &k, self.params.alpha)?;
			k = mat_vec_mul(cs, &self.params.mat, &k)?;
			k = vec_add_constant(cs, &k, constant_1)?;

			x = vec_pow(cs, &x, self.params.alpha)?;
			x = mat_vec_mul(cs, &self.params.mat, &x)?;
			x = vec_add(cs, &x, &k)?;
		}

		for (cipher_text, x) in self
			.cipher_text
			.iter()
			.map(|cipher_text| Constant(*cipher_text))
			.zip(x.iter())
		{
			x.enforce_equal(cs, &cipher_text)?;
		}

		Ok(())
	}
}
