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

fn mat_vec_mul<E: Engine, CS: ConstraintSystem<E>>(mut cs: CS, mat: &Vec<Vec<E::Fr>>, x: &[(Option<E::Fr>, Variable)]) -> Result<Vec<(Option<E::Fr>, Variable)>, SynthesisError> {
	mat.iter().map(|row| {
		if row.len() == x.len() {
			let y_val = x.iter().map(|(x_val, _)| x_val)
			             .zip(row)
			             .map(|(x, s)| x.map(|mut x| { x.mul_assign(s); x }))
			             .fold(Some(E::Fr::zero()), |x, y| x.and_then(|mut x| y.as_ref().map(|y| { x.add_assign(y); x })));
			let y = cs.alloc(|| "y", || y_val.ok_or(SynthesisError::AssignmentMissing))?;

			cs.enforce(
				|| "sum(x[i] * s[i]) = y",
				|lc| x.iter().map(|(_, x)| x).zip(row).fold(lc, |lc, (x, s)| lc + (*s, *x)),
				|lc| lc + CS::one(),
				|lc| lc + y
			);

			Ok((y_val, y))
		} else {
			Err(SynthesisError::AssignmentMissing)
		}
	}).collect()
}

pub struct RescuePermutation<'a, E: Engine> {
	pub alpha: u32,
	pub alpha_inv: &'a [u64],
	pub mat: &'a Vec<Vec<E::Fr>>,
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
		let x = mat_vec_mul(cs.namespace(|| "mat_vec_mul"), self.mat, &x)?;
		let x = vec_add(cs.namespace(|| "vec_add"), &x, &k[0])?;
		let x = vec_pow(cs.namespace(|| "vec_pow"), &x, self.alpha)?;
		let x = mat_vec_mul(cs.namespace(|| "mat_vec_mul"), self.mat, &x)?;
		let x = vec_add(cs.namespace(|| "vec_add"), &x, &k[1])?;

		for (x_val, x) in x.iter() {
			let out = cs.alloc_input(|| "out", || x_val.ok_or(SynthesisError::AssignmentMissing))?;
			cs.enforce(
				|| "x_val = out",
				|lc| lc + *x,
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

	let mat = vec![ // MDS matrix choosen with https://github.com/KULeuven-COSIC/Marvellous rescue instance generator
		vec![Fr::from_str("52435875175126190479447740508185965837690552500527637362617122155198620207712").unwrap(), Fr::from_str("52435875175126190479447740508185965837690552500085682758291472545432070783713").unwrap(), Fr::from_str("52435875175126190479447740508185965837690180948849826184664541807331314824413").unwrap(), Fr::from_str("52435875175126190479447740508185965530807066141876982447594476749845975030113").unwrap(), Fr::from_str("52435875175126190479447740507933128785917572440565624616784716275136260809111").unwrap(), Fr::from_str("52435875175126190479447532273612099891825396755801234592013277091016627662113").unwrap(), Fr::from_str("52435875175126190307956157190266370280540209042396334073273195367138417459213").unwrap(), Fr::from_str("52435875174984959614955767732782448015237669214112699215508711121903592721313").unwrap()],
		vec![Fr::from_str("536650866211219273925600").unwrap(), Fr::from_str("515613692269202933647755503199").unwrap(), Fr::from_str("433476440298104899261833536690159200").unwrap(), Fr::from_str("358030300427067135115671589552167294279900").unwrap(), Fr::from_str("294976202349764657521544847870303251955215776800").unwrap(), Fr::from_str("242940041197869035334307998285435479980217794621064598").unwrap(), Fr::from_str("200073270930275021618366523711686384738412705261046460157600").unwrap(), Fr::from_str("164769141833752994340602057075908554923840928842777934475518194700").unwrap()],
		vec![Fr::from_str("52435875175126190479447740508185965837690552500527637744342169074491994429413").unwrap(), Fr::from_str("52435875175126190479447740508185965837690552500452444720022395830603555030113").unwrap(), Fr::from_str("52435875175126190479447740508185965837690489285741349859050823498439793177712").unwrap(), Fr::from_str("52435875175126190479447740508185965785478243046953023819707332880275475903713").unwrap(), Fr::from_str("52435875175126190479447740508142948840358898794190804687385132844859024774213").unwrap(), Fr::from_str("52435875175126190479447705079731081914661662425323950506782848741034664721313").unwrap(), Fr::from_str("52435875175126190450270636499114056327568661048905303832651360812403732219111").unwrap(), Fr::from_str("52435875175102161850505151033557526797726095208809924360976388507918655022113").unwrap()],
		vec![Fr::from_str("1601829739462939599200").unwrap(), Fr::from_str("1538959752186366920324604900").unwrap(), Fr::from_str("1293794257374577229492091189765600").unwrap(), Fr::from_str("1068609574404235613830498061588064473199").unwrap(), Fr::from_str("880412489571442593111651789590744869108477600").unwrap(), Fr::from_str("725100670268874704193827234209596714398656121669700").unwrap(), Fr::from_str("597156655230182355214109012159286033518673807873815296800").unwrap(), Fr::from_str("491784780262325151139842318511800901674445866929312789708474598").unwrap()],
		vec![Fr::from_str("52435875175126190479447740508185965837690552500527637822598986974511430316315").unwrap(), Fr::from_str("52435875175126190479447740508185965837690552500527633335611698032847356145313").unwrap(), Fr::from_str("52435875175126190479447740508185965837690552496755615421686831179828132329613").unwrap(), Fr::from_str("52435875175126190479447740508185965837687437017476286433602951169466353338913").unwrap(), Fr::from_str("52435875175126190479447740508185963270889909713009585015402529051929337524916").unwrap(), Fr::from_str("52435875175126190479447740506071969669554713688561857811926748520244264386913").unwrap(), Fr::from_str("52435875175126190479445999526678554192107365565196496679897686828258650764813").unwrap(), Fr::from_str("52435875175126189045672870317203987883412589907615787092660514874130483647713").unwrap()],
		vec![Fr::from_str("1945046876074400").unwrap(), Fr::from_str("1864129313105132651802").unwrap(), Fr::from_str("1566614274733553480574400800").unwrap(), Fr::from_str("1293880667489621465420674990505100").unwrap(), Fr::from_str("1066002585927312952418811166082250223200").unwrap(), Fr::from_str("877950291077021111126439137367328153814900403").unwrap(), Fr::from_str("723035854762618570178213345260223758442932269522400").unwrap(), Fr::from_str("595451827327505563414221142210957477534180517724387660300").unwrap()],
		vec![Fr::from_str("52435875175126190479447740508185965837690552500527637822603658699823189224613").unwrap(), Fr::from_str("52435875175126190479447740508185965837690552500527637822603549776390385338913").unwrap(), Fr::from_str("52435875175126190479447740508185965837690552500527637731260546277506185846315").unwrap(), Fr::from_str("52435875175126190479447740508185965837690552500452219820724468529348155025313").unwrap(), Fr::from_str("52435875175126190479447740508185965837690490367849870412821860029566077949813").unwrap(), Fr::from_str("52435875175126190479447740508185965786518948790785240928128406120353047647713").unwrap(), Fr::from_str("52435875175126190479447740508143823507314166635486048366791399742578476614916").unwrap(), Fr::from_str("52435875175126190479447705802127798595254008926481992687797739867574849026913").unwrap()],
		vec![Fr::from_str("960800").unwrap(), Fr::from_str("807744680100").unwrap(), Fr::from_str("667157540444234400").unwrap(), Fr::from_str("549661852436388016181802").unwrap(), Fr::from_str("452697105941691435357049202400").unwrap(), Fr::from_str("372818701621367349292382501162685300").unwrap(), Fr::from_str("307032604808067352305645854537522502703200").unwrap(), Fr::from_str("252854596323205247053675081227392663237129990403").unwrap()],
	];

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
		mat: &mat,
		x: vec![None; M],
		k: [vec![None; M], vec![None; M]]
	};
	let params = generate_random_parameters(c, rng).unwrap();

	let pvk = prepare_verifying_key(&params.vk);

	let x = vec![Fr::from_str("3").unwrap(); M];
	let y: Vec<Fr> = x.iter().map(|x| x.pow(&alpha_inv)).collect();
	let z: Vec<Fr> = y.iter().map(|y| y.pow(&[ALPHA as u64])).collect();
	for (x, z) in x.iter().zip(z) {
		let mut x = *x;
		x.sub_assign(&z);
		assert!(x.is_zero());
	}

	let k = [vec![Fr::from_str("11").unwrap(); M], vec![Fr::from_str("42").unwrap(); M]];

	let y: Vec<Fr> = mat.iter().map(|row| {
		assert!(row.len() == y.len());
		y.iter()
		.zip(row)
		.map(|(y, s)| { let mut y = *y; y.mul_assign(s); y })
		.fold(Fr::zero(), |mut x, y| { x.add_assign(&y); x })
	}).collect();

	let y: Vec<Fr> = y.iter().zip(k[0].iter()).map(|(y, k)| { let mut y = *y; y.add_assign(k); y }).collect();
	let y: Vec<Fr> = y.iter().map(|y| y.pow(&[ALPHA as u64])).collect();

	let y: Vec<Fr> = mat.iter().map(|row| {
		assert!(row.len() == y.len());
		y.iter()
		.zip(row)
		.map(|(y, s)| { let mut y = *y; y.mul_assign(s); y })
		.fold(Fr::zero(), |mut x, y| { x.add_assign(&y); x })
	}).collect();

	let y: Vec<Fr> = y.iter().zip(k[1].iter()).map(|(y, k)| { let mut y = *y; y.add_assign(k); y }).collect();

	let c = RescuePermutation::<Bls12> {
		alpha: ALPHA,
		alpha_inv: &alpha_inv,
		mat: &mat,
		x: x.iter().map(|x| Some(*x)).collect(),
		k: [k[0].iter().map(|k| Some(*k)).collect(), k[1].iter().map(|k| Some(*k)).collect()]
	};
	let proof = create_random_proof(c, &params, rng).unwrap();

	let correct = verify_proof(&pvk, &proof, &y).unwrap();

	println!("{}", correct);
}
