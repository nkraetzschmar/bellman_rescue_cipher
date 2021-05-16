use bellman::{Circuit, ConstraintSystem, Engine, Field, SynthesisError, Variable};

fn pow<E: Engine, CS: ConstraintSystem<E>>(
	mut cs: CS,
	x_val: &Option<E::Fr>,
	x: &Variable,
	alpha: u32,
) -> Result<(Option<E::Fr>, Variable), SynthesisError> {
	if alpha == 0 {
		Ok((Some(E::Fr::one()), CS::one()))
	} else {
		let mut y_val = *x_val;
		let mut y = *x;

		let len = 31 - alpha.leading_zeros();
		for i in (0..len).rev() {
			y_val = y_val.map(|mut y| {
				y.square();
				y
			});
			let y_2 = cs.alloc(|| "y_2", || y_val.ok_or(SynthesisError::AssignmentMissing))?;
			cs.enforce(|| "y_2 = y * y", |lc| lc + y, |lc| lc + y, |lc| lc + y_2);
			y = y_2;

			if alpha & (1 << i) != 0 {
				y_val = y_val.and_then(|mut y| {
					x_val.as_ref().map(|x| {
						y.mul_assign(x);
						y
					})
				});
				let y_x = cs.alloc(|| "y_x", || y_val.ok_or(SynthesisError::AssignmentMissing))?;
				cs.enforce(|| "y_x = y * x", |lc| lc + y, |lc| lc + *x, |lc| lc + y_x);
				y = y_x;
			}
		}

		Ok((y_val, y))
	}
}

fn inv_pow<E: Engine, CS: ConstraintSystem<E>>(
	mut cs: CS,
	x_val: &Option<E::Fr>,
	x: &Variable,
	alpha: u32,
	alpha_inv: &[u64],
) -> Result<(Option<E::Fr>, Variable), SynthesisError> {
	let y_val = x_val.as_ref().map(|x| x.pow(alpha_inv));
	let y = cs.alloc(|| "y", || y_val.ok_or(SynthesisError::AssignmentMissing))?;
	let (_, z) = pow(cs.namespace(|| "pow"), &y_val, &y, alpha)?;

	cs.enforce(|| "z = x", |lc| lc + z, |lc| lc + CS::one(), |lc| lc + *x);

	Ok((y_val, y))
}

fn vec_add<E: Engine, CS: ConstraintSystem<E>>(
	mut cs: CS,
	x: &Vec<(Option<E::Fr>, Variable)>,
	y: &Vec<(Option<E::Fr>, Variable)>,
) -> Result<Vec<(Option<E::Fr>, Variable)>, SynthesisError> {
	if x.len() == y.len() {
		x.iter()
			.zip(y.iter())
			.map(|((x_val, x), (y_val, y))| {
				let z_val = x_val.as_ref().and_then(|x| {
					y_val.as_ref().map(|y| {
						let mut x = *x;
						x.add_assign(y);
						x
					})
				});
				let z = cs.alloc(|| "z", || z_val.ok_or(SynthesisError::AssignmentMissing))?;
				cs.enforce(
					|| "x + y = z",
					|lc| lc + *x + *y,
					|lc| lc + CS::one(),
					|lc| lc + z,
				);

				Ok((z_val, z))
			})
			.collect()
	} else {
		Err(SynthesisError::AssignmentMissing)
	}
}

fn vec_add_const<E: Engine, CS: ConstraintSystem<E>>(
	mut cs: CS,
	x: &Vec<(Option<E::Fr>, Variable)>,
	y: &Vec<E::Fr>,
) -> Result<Vec<(Option<E::Fr>, Variable)>, SynthesisError> {
	if x.len() == y.len() {
		x.iter()
			.zip(y.iter())
			.map(|((x_val, x), y)| {
				let z_val = x_val.as_ref().map(|x| {
					let mut x = *x;
					x.add_assign(y);
					x
				});
				let z = cs.alloc(|| "z", || z_val.ok_or(SynthesisError::AssignmentMissing))?;
				cs.enforce(
					|| "x + y = z",
					|lc| lc + *x + (*y, CS::one()),
					|lc| lc + CS::one(),
					|lc| lc + z,
				);

				Ok((z_val, z))
			})
			.collect()
	} else {
		Err(SynthesisError::AssignmentMissing)
	}
}

fn vec_pow<E: Engine, CS: ConstraintSystem<E>>(
	mut cs: CS,
	x: &Vec<(Option<E::Fr>, Variable)>,
	alpha: u32,
) -> Result<Vec<(Option<E::Fr>, Variable)>, SynthesisError> {
	x.iter()
		.map(|(x_val, x)| pow(cs.namespace(|| "pow"), x_val, x, alpha))
		.collect()
}

fn vec_inv_pow<E: Engine, CS: ConstraintSystem<E>>(
	mut cs: CS,
	x: &Vec<(Option<E::Fr>, Variable)>,
	alpha: u32,
	alpha_inv: &[u64],
) -> Result<Vec<(Option<E::Fr>, Variable)>, SynthesisError> {
	x.iter()
		.map(|(x_val, x)| inv_pow(cs.namespace(|| "inv_pow"), x_val, x, alpha, alpha_inv))
		.collect()
}

fn mat_vec_mul<E: Engine, CS: ConstraintSystem<E>>(
	mut cs: CS,
	mat: &Vec<Vec<E::Fr>>,
	x: &Vec<(Option<E::Fr>, Variable)>,
) -> Result<Vec<(Option<E::Fr>, Variable)>, SynthesisError> {
	mat.iter()
		.map(|row| {
			if row.len() == x.len() {
				let y_val = x
					.iter()
					.map(|(x_val, _)| x_val)
					.zip(row.iter())
					.map(|(x, y)| {
						x.as_ref().map(|x| {
							let mut x = *x;
							x.mul_assign(y);
							x
						})
					})
					.fold(Some(E::Fr::zero()), |x, y| {
						x.and_then(|mut x| {
							y.map(|y| {
								x.add_assign(&y);
								x
							})
						})
					});
				let y = cs.alloc(|| "y", || y_val.ok_or(SynthesisError::AssignmentMissing))?;

				cs.enforce(
					|| "sum(x[i] * s[i]) = y",
					|lc| {
						x.iter()
							.map(|(_, x)| x)
							.zip(row)
							.fold(lc, |lc, (x, s)| lc + (*s, *x))
					},
					|lc| lc + CS::one(),
					|lc| lc + y,
				);

				Ok((y_val, y))
			} else {
				Err(SynthesisError::AssignmentMissing)
			}
		})
		.collect()
}

pub struct RescueCircuit<'a, E: Engine> {
	pub params: &'a super::Params<E::Fr>,
	pub x: Vec<Option<E::Fr>>,
	pub k: Vec<Option<E::Fr>>,
}

impl<E: Engine> Circuit<E> for RescueCircuit<'_, E> {
	fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
		let mut x: Vec<(Option<E::Fr>, Variable)> = self
			.x
			.iter()
			.map(|x| {
				let x_val = *x;
				let x = cs.alloc(|| "x", || x_val.ok_or(SynthesisError::AssignmentMissing))?;
				Ok((x_val, x))
			})
			.collect::<Result<Vec<(Option<E::Fr>, Variable)>, SynthesisError>>()?;

		let mut k: Vec<(Option<E::Fr>, Variable)> = self
			.k
			.iter()
			.map(|k| {
				let k_val = *k;
				let k = cs.alloc(|| "k", || k_val.ok_or(SynthesisError::AssignmentMissing))?;
				Ok((k_val, k))
			})
			.collect::<Result<Vec<(Option<E::Fr>, Variable)>, SynthesisError>>()?;

		k = vec_add_const(cs.namespace(|| "vec_add"), &k, &self.params.constants_init)?;
		x = vec_add(cs.namespace(|| "vec_add"), &x, &k)?;

		for (constant_0, constant_1) in self.params.round_constants.iter() {
			k = vec_inv_pow(
				cs.namespace(|| "vec_inv_pow"),
				&k,
				self.params.alpha,
				&self.params.alpha_inv,
			)?;
			k = mat_vec_mul(cs.namespace(|| "mat_vec_mul"), &self.params.mat, &k)?;
			k = vec_add_const(cs.namespace(|| "vec_add"), &k, constant_0)?;

			x = vec_inv_pow(
				cs.namespace(|| "vec_inv_pow"),
				&x,
				self.params.alpha,
				&self.params.alpha_inv,
			)?;
			x = mat_vec_mul(cs.namespace(|| "mat_vec_mul"), &self.params.mat, &x)?;
			x = vec_add(cs.namespace(|| "vec_add"), &x, &k)?;

			k = vec_pow(cs.namespace(|| "vec_pow"), &k, self.params.alpha)?;
			k = mat_vec_mul(cs.namespace(|| "mat_vec_mul"), &self.params.mat, &k)?;
			k = vec_add_const(cs.namespace(|| "vec_add"), &k, constant_1)?;

			x = vec_pow(cs.namespace(|| "vec_pow"), &x, self.params.alpha)?;
			x = mat_vec_mul(cs.namespace(|| "mat_vec_mul"), &self.params.mat, &x)?;
			x = vec_add(cs.namespace(|| "vec_add"), &x, &k)?;
		}

		for (x_val, x) in x.iter() {
			let out =
				cs.alloc_input(|| "out", || x_val.ok_or(SynthesisError::AssignmentMissing))?;
			cs.enforce(
				|| "x_val = out",
				|lc| lc + *x,
				|lc| lc + CS::one(),
				|lc| lc + out,
			);
		}

		Ok(())
	}
}
