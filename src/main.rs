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

fn pow_inv<E: Engine, CS: ConstraintSystem<E>>(mut cs: CS, x_val: &Option<E::Fr>, x: &Variable, n: u32, n_inv: &[u64]) -> Result<(Option<E::Fr>, Variable), SynthesisError> {
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

pub struct InvPow5<'a, E: Engine> {
	pub alpha: u32,
	pub alpha_inv: &'a [u64],
	pub x: Vec<Option<E::Fr>>
}

impl <E: Engine> Circuit<E> for InvPow5<'_, E> {
	fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
		for x_val in self.x.iter() {
			let x = cs.alloc(|| "x", || x_val.ok_or(SynthesisError::AssignmentMissing))?;
			let (y_val, y) = pow_inv(cs.namespace(|| "pow_inv"), &x_val, &x, self.alpha, &self.alpha_inv)?;

			let out = cs.alloc_input(|| "out", || y_val.ok_or(SynthesisError::AssignmentMissing))?;
			cs.enforce(
				|| "y_val = out",
				|lc| lc + y,
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
	let c = InvPow5::<Bls12> { alpha: ALPHA, alpha_inv: &alpha_inv, x: vec![None; M] };
	let params = generate_random_parameters(c, rng).unwrap();

	let pvk = prepare_verifying_key(&params.vk);

	let x = Fr::from_str("3");
	let y = x.map(|x| x.pow(&alpha_inv));
	let z = y.map(|x| x.pow(&[ALPHA as u64]));
	assert!(x == z);

	let c = InvPow5::<Bls12> { alpha: ALPHA, alpha_inv: &alpha_inv, x: vec![x; M] };
	let proof = create_random_proof(c, &params, rng).unwrap();

	let correct = verify_proof(&pvk, &proof, &[y.unwrap(); M]).unwrap();

	println!("{}", correct);
}
