extern crate rand;
extern crate bellman;

use rand::thread_rng;
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

fn pow<E: Engine, CS: ConstraintSystem<E>>(n: u32, mut cs: CS, x_val: &Option<E::Fr>, x: &Variable) -> Result<(Option<E::Fr>, Variable), SynthesisError> {
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
					|lc| lc + x_2,
				);

				if n & (1 << i) != 0 {
					let x_3_val = x_2_val.and_then(|mut x| x_val.as_ref().map(|y| { x.mul_assign(y); x }));
					let x_3 = cs.alloc(|| "x_3", || x_3_val.ok_or(SynthesisError::AssignmentMissing))?;
					cs.enforce(
						|| "x_3 = x * x_2",
						|lc| lc + *x,
						|lc| lc + x_2,
						|lc| lc + x_3,
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

fn inv<E: Engine, CS: ConstraintSystem<E>>(mut cs: CS, x_val: &Option<E::Fr>, x: &Variable) -> Result<(Option<E::Fr>, Variable), SynthesisError> {
	let x_inv_val = x_val.and_then(|x| x.inverse());
	let x_inv = cs.alloc(|| "x_inv", || x_inv_val.ok_or(SynthesisError::AssignmentMissing))?;
	cs.enforce(
		|| "x * x_inv = 1",
		|lc| lc + *x,
		|lc| lc + x_inv,
		|lc| lc + CS::one(),
	);

	Ok((x_inv_val, x_inv))
}

pub struct InvPow5<E: Engine> {
	pub x: Vec<Option<E::Fr>>
}

impl <E: Engine> Circuit<E> for InvPow5<E> {
	fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
		for x_val in self.x.iter() {
			let x = cs.alloc(|| "x", || x_val.ok_or(SynthesisError::AssignmentMissing))?;

			let (x_5_val, x_5) = pow(5, cs.namespace(|| "pow5"), &x_val, &x)?;
			let (x_5_inv_val, x_5_inv) = inv(cs.namespace(|| "inv"), &x_5_val, &x_5)?;

			let out = cs.alloc_input(|| "out", || x_5_inv_val.ok_or(SynthesisError::AssignmentMissing))?;
			cs.enforce(
				|| "x_5_inv = out",
				|lc| lc + x_5_inv,
				|lc| lc + CS::one(),
				|lc| lc + out,
			);
		}

		Ok(())
	}
}

fn main(){
	const M: usize = 8;

	let rng = &mut thread_rng();
	let c = InvPow5::<Bls12> { x: vec![None; M] };
	let params = generate_random_parameters(c, rng).unwrap();

	let pvk = prepare_verifying_key(&params.vk);

	let x = Fr::from_str("3");
	let x_5 = x.map(|x| x.pow(&[5]));
	let x_5_inv = x_5.and_then(|x| x.inverse());

	let c = InvPow5::<Bls12> { x: vec![x; M] };
	let proof = create_random_proof(c, &params, rng).unwrap();

	let correct = verify_proof(&pvk, &proof, &[x_5_inv.unwrap(); M]).unwrap();

	println!("{}", correct);
}
