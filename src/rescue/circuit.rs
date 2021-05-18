use franklin_crypto::{
	bellman::{plonk::better_better_cs::cs::*, Engine, Field, PrimeField, SynthesisError},
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

fn rescue_cipher<E: Engine, CS: ConstraintSystem<E>>(
	cs: &mut CS,
	params: &super::Params<E::Fr>,
	k: &Vec<Num<E>>,
	x: &Vec<Num<E>>,
) -> Result<Vec<Num<E>>, SynthesisError> {
	let mut k = vec_add_constant(cs, &k, &params.constants_init)?;
	let mut x = vec_add(cs, &x, &k)?;

	for (constant_0, constant_1) in params.round_constants.iter() {
		k = vec_inv_pow(cs, &k, params.alpha, &params.alpha_inv)?;
		k = mat_vec_mul(cs, &params.mat, &k)?;
		k = vec_add_constant(cs, &k, constant_0)?;

		x = vec_inv_pow(cs, &x, params.alpha, &params.alpha_inv)?;
		x = mat_vec_mul(cs, &params.mat, &x)?;
		x = vec_add(cs, &x, &k)?;

		k = vec_pow(cs, &k, params.alpha)?;
		k = mat_vec_mul(cs, &params.mat, &k)?;
		k = vec_add_constant(cs, &k, constant_1)?;

		x = vec_pow(cs, &x, params.alpha)?;
		x = mat_vec_mul(cs, &params.mat, &x)?;
		x = vec_add(cs, &x, &k)?;
	}

	Ok(x)
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
		let k: Vec<Num<E>> = self
			.key
			.iter()
			.map(|k| Num::alloc(cs, *k))
			.collect::<Result<Vec<Num<E>>, SynthesisError>>()?;

		let x: Vec<Num<E>> = self
			.plain_text
			.iter()
			.map(|x| Num::alloc(cs, *x))
			.collect::<Result<Vec<Num<E>>, SynthesisError>>()?;

		let x = rescue_cipher(cs, self.params, &k, &x)?;

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

pub struct RescueStreamCTRCircuit<'a, E: Engine> {
	pub params: &'a super::Params<E::Fr>,
	pub key: Vec<Option<E::Fr>>,
	pub nonce: Vec<Option<E::Fr>>,
	pub plain_text: Vec<Option<E::Fr>>,
	pub cipher_text: Vec<E::Fr>,
}

impl<E: Engine> Circuit<E> for RescueStreamCTRCircuit<'_, E> {
	type MainGate = Width4MainGateWithDNext;

	fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
		Ok(vec![Self::MainGate::default().into_internal()])
	}

	fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
		let key: Vec<Num<E>> = self
			.key
			.iter()
			.map(|key| Num::alloc(cs, *key))
			.collect::<Result<Vec<Num<E>>, SynthesisError>>()?;

		let mut input: Vec<Num<E>> = self
			.nonce
			.iter()
			.map(|nonce| Num::alloc(cs, *nonce))
			.collect::<Result<Vec<Num<E>>, SynthesisError>>()?;

		input.push(Constant(E::Fr::zero()));
		assert!(input.len() == self.params.m);

		let mut cipher_text: Vec<Num<E>> = vec![];

		for (chunk, ctr) in self.plain_text.chunks(self.params.m).zip(0..) {
			let ctr = E::Fr::from_str(&ctr.to_string()).unwrap();
			input[self.params.m - 1] = Constant(ctr);

			let key_stream = rescue_cipher(cs, self.params, &key, &input)?;

			let mut plain_text: Vec<Num<E>> = chunk
				.iter()
				.map(|chunk| Num::alloc(cs, *chunk))
				.collect::<Result<Vec<Num<E>>, SynthesisError>>()?;

			for _ in chunk.len()..self.params.m {
				plain_text.push(Num::alloc(cs, Some(E::Fr::zero()))?);
			}

			let mut cipher_stream = vec_add(cs, &plain_text, &key_stream)?;
			cipher_text.append(&mut cipher_stream);
		}

		for (x, y) in self
			.cipher_text
			.iter()
			.map(|cipher_text| Constant(*cipher_text))
			.zip(cipher_text.iter())
		{
			x.enforce_equal(cs, &y)?;
		}

		Ok(())
	}
}
