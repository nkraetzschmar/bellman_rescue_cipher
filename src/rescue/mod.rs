extern crate num_bigint;
extern crate num_integer;
extern crate num_traits;

use self::num_bigint::{BigInt, BigUint, ToBigInt};
use self::num_integer::{ExtendedGcd, Integer};
use self::num_traits::{One, Zero};
use super::PrimeField;

pub mod circuit;

fn vec_from_str<F: PrimeField>(str: &[&str]) -> Vec<F> {
	str.iter().map(|str| F::from_str(str).unwrap()).collect()
}

fn mat_from_str<F: PrimeField>(str: &[&[&str]]) -> Vec<Vec<F>> {
	str.iter().map(|str| vec_from_str(str)).collect()
}

fn vec_add<F: PrimeField>(x: &Vec<F>, y: &Vec<F>) -> Vec<F> {
	assert!(x.len() == y.len());

	x.iter()
		.zip(y.iter())
		.map(|(x, y)| {
			let mut x = *x;
			x.add_assign(y);
			x
		})
		.collect()
}

fn mat_vec_mul<F: PrimeField>(mat: &Vec<Vec<F>>, x: &Vec<F>) -> Vec<F> {
	mat.iter()
		.map(|row| {
			assert!(x.len() == row.len());

			x.iter()
				.zip(row.iter())
				.map(|(x, y)| {
					let mut x = *x;
					x.mul_assign(y);
					x
				})
				.fold(F::zero(), |mut x, y| {
					x.add_assign(&y);
					x
				})
		})
		.collect()
}

fn vec_pow<F: PrimeField>(x: &Vec<F>, alpha: &[u64]) -> Vec<F> {
	x.iter().map(|x| x.pow(alpha)).collect()
}

pub struct Params<F: PrimeField> {
	pub m: usize,
	pub alpha: u32,
	pub alpha_inv: Vec<u64>,
	pub mat: Vec<Vec<F>>,
	pub constants_init: Vec<F>,
	pub round_constants: Vec<(Vec<F>, Vec<F>)>,
}

impl<F: PrimeField> Params<F> {
	pub fn new(
		m: usize,
		rounds: usize,
		alpha: u32,
		mat: &[&[&str]],
		constants_init: &[&str],
		constants_mat: &[&[&str]],
		constants_add: &[&str],
	) -> Self {
		let mat = mat_from_str(mat);
		let constants_init = vec_from_str(constants_init);
		let constants_mat = mat_from_str(constants_mat);
		let constants_add = vec_from_str(constants_add);

		let mut round_constants: Vec<(Vec<F>, Vec<F>)> = Vec::with_capacity(rounds);
		for _ in 0..(rounds) {
			round_constants.push({
				let previous: &Vec<F> = round_constants
					.last()
					.map(|(_, previous)| previous)
					.unwrap_or(&constants_init);
				let mut constant_0 = mat_vec_mul(&constants_mat, previous);
				constant_0 = vec_add(&constant_0, &constants_add);

				let mut constant_1 = mat_vec_mul(&constants_mat, &constant_0);
				constant_1 = vec_add(&constant_1, &constants_add);

				(constant_0, constant_1)
			});
		}

		Self {
			m: m,
			alpha: alpha,
			alpha_inv: {
				let modulus = (BigUint::new(
					F::char()
						.as_ref()
						.iter()
						.flat_map(|x| vec![*x as u32, (*x >> 32) as u32])
						.collect(),
				) - 1u32)
					.to_bigint()
					.unwrap();
				let ExtendedGcd {
					gcd, x: alpha_inv, ..
				} = alpha.to_bigint().unwrap().extended_gcd(&modulus);
				assert!(gcd.is_one());

				(if alpha_inv >= BigInt::zero() {
					alpha_inv
				} else {
					alpha_inv + &modulus
				})
				.to_biguint()
				.unwrap()
				.to_u64_digits()
			},
			mat: mat,
			constants_init: constants_init,
			round_constants: round_constants,
		}
	}
}

pub fn block_enc<F: PrimeField>(params: &Params<F>, key: &Vec<F>, plain_text: &Vec<F>) -> Vec<F> {
	let mut k = key.clone();
	let mut x = plain_text.clone();

	k = vec_add(&k, &params.constants_init);
	x = vec_add(&x, &k);

	for (constant_0, constant_1) in params.round_constants.iter() {
		k = vec_pow(&k, &params.alpha_inv);
		k = mat_vec_mul(&params.mat, &k);
		k = vec_add(&k, constant_0);

		x = vec_pow(&x, &params.alpha_inv);
		x = mat_vec_mul(&params.mat, &x);
		x = vec_add(&x, &k);

		k = vec_pow(&k, &[params.alpha as u64]);
		k = mat_vec_mul(&params.mat, &k);
		k = vec_add(&k, constant_1);

		x = vec_pow(&x, &[params.alpha as u64]);
		x = mat_vec_mul(&params.mat, &x);
		x = vec_add(&x, &k);
	}

	x
}

/// stream cipher in CTR mode
/// using m-1 field elements as nonce and 1 element as counter
/// padding message with zeros to nearest multiple of m
pub fn stream_cipher_ctr<F: PrimeField>(
	params: &Params<F>,
	key: &Vec<F>,
	nonce: &Vec<F>,
	plain_text: &Vec<F>,
) -> Vec<F> {
	let mut cipher_text = vec![];

	let mut input = nonce.clone();
	input.push(F::zero());
	assert!(input.len() == params.m);

	for (chunk, ctr) in plain_text.chunks(params.m).zip(0..) {
		let ctr = F::from_str(&ctr.to_string()).unwrap();
		input[params.m - 1] = ctr;

		let key_stream = block_enc(params, key, &input);

		let mut plain_text = chunk.to_vec();
		for _ in chunk.len()..params.m {
			plain_text.push(F::zero());
		}

		let mut cipher_stream = vec_add(&plain_text, &key_stream);
		cipher_text.append(&mut cipher_stream);
	}

	cipher_text
}
