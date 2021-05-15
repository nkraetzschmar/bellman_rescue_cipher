extern crate rand;
extern crate num_integer;
extern crate num_traits;
extern crate num_bigint;
extern crate bellman;

use rand::thread_rng;
use num_integer::{Integer, ExtendedGcd};
use num_traits::{One};
use num_bigint::{BigUint, ToBigInt};
use bellman::{
	Field,
	PrimeField,
	Engine,
	Variable,
	Circuit,
	ConstraintSystem,
	SynthesisError,
	bls12_381::{
		Bls12,
		Fr
	},
	groth16::{
		generate_random_parameters,
		prepare_verifying_key,
		create_random_proof,
		verify_proof
	}
};

fn pow<E: Engine, CS: ConstraintSystem<E>>(mut cs: CS, x_val: &Option<E::Fr>, x: &Variable, n: u32) -> Result<(Option<E::Fr>, Variable), SynthesisError> {
	match n {
		0 => { Ok((Some(E::Fr::one()), CS::one())) }
		_ => {
			let mut x_n_val = *x_val;
			let mut x_n = *x;

			let len = 31 - n.leading_zeros();
			for i in (0..len).rev() {
				let x_2_val = x_n_val.map(|mut x| { x.square(); x });
				let x_2 = cs.alloc(|| "x_2", || x_2_val.ok_or(SynthesisError::AssignmentMissing))?;
				cs.enforce(
					|| "x_2 = x_n * x_n",
					|lc| lc + x_n,
					|lc| lc + x_n,
					|lc| lc + x_2
				);

				if n & (1 << i) != 0 {
					let x_3_val = x_2_val.and_then(|mut x| x_val.as_ref().map(|y| { x.mul_assign(y); x }));
					let x_3 = cs.alloc(|| "x_3", || x_3_val.ok_or(SynthesisError::AssignmentMissing))?;
					cs.enforce(
						|| "x_3 = x * x_2",
						|lc| lc + *x,
						|lc| lc + x_2,
						|lc| lc + x_3
					);

					x_n_val = x_3_val;
					x_n = x_3;
				} else {
					x_n_val = x_2_val;
					x_n = x_2;
				}
			}

			Ok((x_n_val, x_n))
		}
	}
}

fn inv_pow<E: Engine, CS: ConstraintSystem<E>>(mut cs: CS, x_val: &Option<E::Fr>, x: &Variable, n: u32, n_inv: &[u64]) -> Result<(Option<E::Fr>, Variable), SynthesisError> {
	let y_val = x_val.map(|x| x.pow(n_inv));
	let y = cs.alloc(|| "y", || y_val.ok_or(SynthesisError::AssignmentMissing))?;
	let (_y_n_val, y_n) = pow(cs.namespace(|| "pow"), &y_val, &y, n)?;

	cs.enforce(
		|| "x = y_5",
		|lc| lc + y_n,
		|lc| lc + CS::one(),
		|lc| lc + *x
	);

	Ok((y_val, y))
}

fn vec_add<E: Engine, CS: ConstraintSystem<E>>(mut cs: CS, x: &[(Option<E::Fr>, Variable)], y: &[(Option<E::Fr>, Variable)]) -> Result<Vec<(Option<E::Fr>, Variable)>, SynthesisError> {
	if x.len() == y.len() {
		x.iter().zip(y.iter()).map(|((x_val, x), (y_val, y))| {
			let z_val = x_val.and_then(|mut x| y_val.as_ref().map(|y| { x.add_assign(y); x }));
			let z = cs.alloc(|| "z", || z_val.ok_or(SynthesisError::AssignmentMissing))?;
			cs.enforce(
				|| "x + y = z",
				|lc| lc + *x + *y,
				|lc| lc + CS::one(),
				|lc| lc + z
			);

			Ok((z_val, z))
		}).collect()
	} else {
		Err(SynthesisError::AssignmentMissing)
	}
}

fn vec_pow<E: Engine, CS: ConstraintSystem<E>>(mut cs: CS, x: &[(Option<E::Fr>, Variable)], n: u32) -> Result<Vec<(Option<E::Fr>, Variable)>, SynthesisError> {
	x.iter().map(|(x_val, x)| {
		pow(cs.namespace(|| "pow"), x_val, x, n)
	}).collect()
}

fn vec_inv_pow<E: Engine, CS: ConstraintSystem<E>>(mut cs: CS, x: &[(Option<E::Fr>, Variable)], n: u32, n_inv: &[u64]) -> Result<Vec<(Option<E::Fr>, Variable)>, SynthesisError> {
	x.iter().map(|(x_val, x)| {
		inv_pow(cs.namespace(|| "inv_pow"), x_val, x, n, n_inv)
	}).collect()
}

pub struct RescuePermutation<'a, E: Engine> {
	pub alpha: u32,
	pub alpha_inv: &'a [u64],
	pub x: Vec<Option<E::Fr>>,
	pub k: [Vec<Option<E::Fr>>; 2]
}

impl <E: Engine> Circuit<E> for RescuePermutation<'_, E> {
	fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
		let mut x: Vec<(Option<E::Fr>, Variable)> = Vec::with_capacity(self.x.len());
		for x_val in self.x.iter() {
			let x_var = cs.alloc(|| "x", || x_val.ok_or(SynthesisError::AssignmentMissing))?;
			x.push((*x_val, x_var));
		}

		let mut k: [Vec<(Option<E::Fr>, Variable)>; 2] = [Vec::with_capacity(self.k[0].len()), Vec::with_capacity(self.k[1].len())];
		for i in 0..2 {
			for k_val in self.k[i].iter() {
				let k_var = cs.alloc(|| "k", || k_val.ok_or(SynthesisError::AssignmentMissing))?;
				k[i].push((*k_val, k_var));
			}
		}

		let x = vec_inv_pow(cs.namespace(|| "vec_inv_pow"), &x, self.alpha, self.alpha_inv)?;
		let x = vec_add(cs.namespace(|| "vec_add"), &x, &k[0])?;
		let x = vec_pow(cs.namespace(|| "vec_pow"), &x, self.alpha)?;
		let x = vec_add(cs.namespace(|| "vec_add"), &x, &k[1])?;

		for (x_val, x) in x.into_iter() {
			let out = cs.alloc_input(|| "out", || x_val.ok_or(SynthesisError::AssignmentMissing))?;
			cs.enforce(
				|| "x_val = out",
				|lc| lc + x,
				|lc| lc + CS::one(),
				|lc| lc + out
			);
		}

		Ok(())
	}
}

fn main(){
	const M: usize = 8;
	const ALPHA: u32 = 5;

	let alpha_inv = {
		let modulus = BigUint::new(Fr::char().as_ref()
		                                     .iter()
		                                     .map(|x| vec![*x as u32, (*x >> 32) as u32])
		                                     .flatten()
		                                     .collect()) - 1u32;

		let ExtendedGcd{ gcd, x: alpha_inv, .. } = ALPHA.to_bigint().unwrap().extended_gcd(&modulus.to_bigint().unwrap());
		assert!(gcd.is_one());
		alpha_inv.to_biguint().unwrap().to_u64_digits()
	};

	let rng = &mut thread_rng();
	let c = RescuePermutation::<Bls12> {
		alpha: ALPHA,
		alpha_inv: &alpha_inv,
		x: vec![None; M],
		k: [vec![None; M], vec![None; M]]
	};
	let params = generate_random_parameters(c, rng).unwrap();

	let pvk = prepare_verifying_key(&params.vk);

	let x = Fr::from_str("3");
	let y = x.map(|x| x.pow(&alpha_inv));
	let z = y.map(|y| y.pow(&[ALPHA as u64]));
	assert!(x == z);

	let k = [Fr::from_str("11"), Fr::from_str("42")];

	let y = y.and_then(|mut y| k[0].map(|k| { y.add_assign(&k); y }));
	let y = y.map(|y| y.pow(&[ALPHA as u64]));
	let y = y.and_then(|mut y| k[1].map(|k| { y.add_assign(&k); y }));

	let c = RescuePermutation::<Bls12> {
		alpha: ALPHA,
		alpha_inv: &alpha_inv,
		x: vec![x; M],
		k: [vec![k[0]; M], vec![k[1]; M]]
	};
	let proof = create_random_proof(c, &params, rng).unwrap();

	let correct = verify_proof(&pvk, &proof, &[y.unwrap(); M]).unwrap();

	println!("{}", correct);
}
