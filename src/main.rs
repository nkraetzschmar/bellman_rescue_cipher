extern crate rand;
extern crate bellman;

use rand::thread_rng;
use bellman::{
	Field,
	PrimeField,
	Engine,
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

pub struct CubeDemo<E: Engine> {
	pub x: Option<E::Fr>,
}

impl <E: Engine> Circuit<E> for CubeDemo<E> {
	fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
		let x_val = self.x;
		let x = cs.alloc(|| "x", || x_val.ok_or(SynthesisError::AssignmentMissing))?;

		let x_2_val = x_val.map(|mut x| { x.square(); x });
		let x_2 = cs.alloc(|| "x_2", || x_2_val.ok_or(SynthesisError::AssignmentMissing))?;
		cs.enforce(
			|| "x_2 = x * x",
			|lc| lc + x,
			|lc| lc + x,
			|lc| lc + x_2,
		);

		let x_4_val = x_2_val.map(|mut x| { x.square(); x });
		let x_4 = cs.alloc(|| "x_4", || x_4_val.ok_or(SynthesisError::AssignmentMissing))?;
		cs.enforce(
			|| "x_4 = x_2 * x_2",
			|lc| lc + x_2,
			|lc| lc + x_2,
			|lc| lc + x_4,
		);

		let x_5_val = x_4_val.and_then(|mut x| x_val.as_ref().map(|y| { x.mul_assign(y); x }));
		let x_5 = cs.alloc(|| "x_5", || x_5_val.ok_or(SynthesisError::AssignmentMissing))?;
		cs.enforce(
			|| "x_5 = x * x_4",
			|lc| lc + x,
			|lc| lc + x_4,
			|lc| lc + x_5,
		);

		let out_val = x_5_val.and_then(|x| x.inverse());
		let tmp = x_5_val.and_then(|mut x| out_val.as_ref().map(|y| { x.mul_assign(y); x }));
		println!("{:?} {:?} {:?}", x_5_val, out_val, tmp);
		let out = cs.alloc_input(|| "out", || out_val.ok_or(SynthesisError::AssignmentMissing))?;
		cs.enforce(
			|| "x_5 * out = 1",
			|lc| lc + x_5,
			|lc| lc + out,
			|lc| lc + CS::one(),
		);

		Ok(())
	}
}

fn main(){
	let rng = &mut thread_rng();
	let c = CubeDemo::<Bls12> { x: None };
	let params = generate_random_parameters(c, rng).unwrap();

	let pvk = prepare_verifying_key(&params.vk);

	let x = Fr::from_str("3");
	let x_5_inv = x.as_ref().and_then(|x| {
		let mut x_5 = *x;
		x_5.square();
		x_5.square();
		x_5.mul_assign(x);
		x_5.inverse()
	});
	println!("{:?} {:?}", x, x_5_inv);

	let c = CubeDemo::<Bls12> { x: x };
	let proof = create_random_proof(c, &params, rng).unwrap();

	let correct = verify_proof(&pvk, &proof, &[x_5_inv.unwrap()]).unwrap();

	println!("{}", correct);
}
