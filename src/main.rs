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

fn vec_add_const<E: Engine, CS: ConstraintSystem<E>>(mut cs: CS, x: &[(Option<E::Fr>, Variable)], y: &[E::Fr]) -> Result<Vec<(Option<E::Fr>, Variable)>, SynthesisError> {
	if x.len() == y.len() {
		x.iter().zip(y.iter()).map(|((x_val, x), y)| {
			let z_val = x_val.map(|mut x| { x.add_assign(y); x });
			let z = cs.alloc(|| "z", || z_val.ok_or(SynthesisError::AssignmentMissing))?;
			cs.enforce(
				|| "x + y = z",
				|lc| lc + *x + (*y, CS::one()),
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

pub struct RescueParams<E: Engine> {
	pub m: usize,
	pub alpha: u32,
	pub alpha_inv: Vec<u64>,
	pub mat: Vec<Vec<E::Fr>>,
	pub init_constants: Vec<E::Fr>,
	pub round_constants: Vec<[Vec<E::Fr>; 2]>
}

impl <E: Engine> RescueParams<E> {
	fn new(m: usize, rounds: usize, alpha: u32, mat: &[&[&str]], constants_init: &[&str], constants_mat: &[&[&str]], constants_add: &[&str]) -> Self {
		assert!(mat.len() == m);
		for row in mat.iter() {
			assert!(row.len() == m);
		}
		assert!(constants_init.len() == m);
		assert!(constants_mat.len() == m);
		for row in constants_mat.iter() {
			assert!(row.len() == m);
		}
		assert!(constants_add.len() == m);

		let constants_init: Vec<E::Fr> = constants_init.iter().map(|str| E::Fr::from_str(str).unwrap()).collect();
		let constants_mat: Vec<Vec<E::Fr>> = constants_mat.iter().map(|row| row.iter().map(|str| E::Fr::from_str(str).unwrap()).collect()).collect();
		let constants_add: Vec<E::Fr> = constants_add.iter().map(|str| E::Fr::from_str(str).unwrap()).collect();

		let mut constants: Vec<Vec<E::Fr>> = Vec::with_capacity(rounds * 2);
		constants.push(constants_init);

		for _ in 0..(2 * rounds) {
			constants.push(constants_mat.iter().map(|row| {
				constants.last().unwrap().iter()
				                         .zip(row)
				                         .map(|(x, s)| { let mut x = *x; x.mul_assign(s); x })
				                         .fold(E::Fr::zero(), |mut x, y| { x.add_assign(&y); x })
			}).zip(constants_add.iter()).map(|(mut x, y)| { x.add_assign(y); x }).collect());
		}

		let (constants_head, constants_tail) = constants.split_at(1);

		Self {
			m: m,
			alpha: alpha,
			alpha_inv: {
				let modulus = BigUint::new(E::Fr::char().as_ref()
				                                        .iter()
				                                        .map(|x| vec![*x as u32, (*x >> 32) as u32])
				                                        .flatten()
				                                        .collect()) - 1u32;

				let ExtendedGcd{ gcd, x: alpha_inv, .. } = alpha.to_bigint().unwrap().extended_gcd(&modulus.to_bigint().unwrap());
				assert!(gcd.is_one());
				alpha_inv.to_biguint().unwrap().to_u64_digits()
			},
			mat: mat.iter().map(|row| row.iter().map(|str| E::Fr::from_str(str).unwrap()).collect()).collect(),
			init_constants: constants_head[0].clone(),
			round_constants: constants_tail.chunks(2).map(|x| [x[0].clone(), x[1].clone()]).collect(),
		}
	}
}

pub struct RescuePermutation<'a, E: Engine> {
	pub params: &'a RescueParams<E>,
	pub x: Vec<Option<E::Fr>>,
	pub k: Vec<Option<E::Fr>>
}

impl <E: Engine> Circuit<E> for RescuePermutation<'_, E> {
	fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
		let mut x: Vec<(Option<E::Fr>, Variable)> = Vec::with_capacity(self.x.len());
		for x_val in self.x.iter() {
			let x_var = cs.alloc(|| "x", || x_val.ok_or(SynthesisError::AssignmentMissing))?;
			x.push((*x_val, x_var));
		}

		let mut k: Vec<(Option<E::Fr>, Variable)> = Vec::with_capacity(self.k.len());
		for k_val in self.k.iter() {
			let k_var = cs.alloc(|| "k", || k_val.ok_or(SynthesisError::AssignmentMissing))?;
			k.push((*k_val, k_var));
		}

		k = vec_add_const(cs.namespace(|| "vec_add"), &k, &self.params.init_constants)?;
		x = vec_add(cs.namespace(|| "vec_add"), &x, &k)?;

		for c in self.params.round_constants.iter() {
			k = vec_inv_pow(cs.namespace(|| "vec_inv_pow"), &k, self.params.alpha, &self.params.alpha_inv)?;
			k = mat_vec_mul(cs.namespace(|| "mat_vec_mul"), &self.params.mat, &k)?;
			k = vec_add_const(cs.namespace(|| "vec_add"), &k, &c[0])?;

			x = vec_inv_pow(cs.namespace(|| "vec_inv_pow"), &x, self.params.alpha, &self.params.alpha_inv)?;
			x = mat_vec_mul(cs.namespace(|| "mat_vec_mul"), &self.params.mat, &x)?;
			x = vec_add(cs.namespace(|| "vec_add"), &x, &k)?;

			k = vec_pow(cs.namespace(|| "vec_pow"), &k, self.params.alpha)?;
			k = mat_vec_mul(cs.namespace(|| "mat_vec_mul"), &self.params.mat, &k)?;
			k = vec_add_const(cs.namespace(|| "vec_add"), &k, &c[1])?;

			x = vec_pow(cs.namespace(|| "vec_pow"), &x, self.params.alpha)?;
			x = mat_vec_mul(cs.namespace(|| "mat_vec_mul"), &self.params.mat, &x)?;
			x = vec_add(cs.namespace(|| "vec_add"), &x, &k)?;
		}

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

fn rescue_cipher_block_enc<E: Engine>(params: &RescueParams<E>, k: &[E::Fr], x: &[E::Fr]) -> Vec<E::Fr> {
	let mut x = x.to_vec();
	let mut k = k.to_vec();

	k = k.iter().zip(params.init_constants.iter())
	            .map(|(k, c)| { let mut k = *k; k.add_assign(c); k })
	            .collect();

	x = x.iter().zip(k.iter())
	            .map(|(x, k)| { let mut x = *x; x.add_assign(k); x })
	            .collect();

	for c in params.round_constants.iter() {
		k = k.into_iter().map(|k| k.pow(&params.alpha_inv)).collect();
		k = params.mat.iter().map(|row| {
			k.iter().zip(row)
			        .map(|(k, s)| { let mut k = *k; k.mul_assign(s); k })
			        .fold(E::Fr::zero(), |mut a, b| { a.add_assign(&b); a })
		}).collect();
		k = k.iter().zip(c[0].iter())
		            .map(|(k, c)| { let mut k = *k; k.add_assign(c); k })
		            .collect();

		x = x.into_iter().map(|x| x.pow(&params.alpha_inv)).collect();
		x = params.mat.iter().map(|row| {
			x.iter().zip(row)
			        .map(|(x, s)| { let mut x = *x; x.mul_assign(s); x })
			        .fold(E::Fr::zero(), |mut a, b| { a.add_assign(&b); a })
		}).collect();
		x = x.iter().zip(k.iter())
		            .map(|(x, k)| { let mut x = *x; x.add_assign(k); x })
		            .collect();

		k = k.into_iter().map(|k| k.pow(&[params.alpha as u64])).collect();
		k = params.mat.iter().map(|row| {
			k.iter().zip(row)
			        .map(|(k, s)| { let mut k = *k; k.mul_assign(s); k })
			        .fold(E::Fr::zero(), |mut a, b| { a.add_assign(&b); a })
		}).collect();
		k = k.iter().zip(c[1].iter())
		            .map(|(k, c)| { let mut k = *k; k.add_assign(c); k })
		            .collect();

		x = x.into_iter().map(|x| x.pow(&[params.alpha as u64])).collect();
		x = params.mat.iter().map(|row| {
			x.iter().zip(row)
			        .map(|(x, s)| { let mut x = *x; x.mul_assign(s); x })
			        .fold(E::Fr::zero(), |mut a, b| { a.add_assign(&b); a })
		}).collect();
		x = x.iter().zip(k.iter())
		            .map(|(x, k)| { let mut x = *x; x.add_assign(k); x })
		            .collect();
	}

	x
}

fn main(){
	let rescue_params = RescueParams::<Bls12>::new( // parameters choosen with https://github.com/KULeuven-COSIC/Marvellous rescue instance generator for m=8 and alpha=5
		8,
		10,
		5,
		&[
			&["52435875175126190479447740508185965837690552500527637362617122155198620207712", "52435875175126190479447740508185965837690552500085682758291472545432070783713", "52435875175126190479447740508185965837690180948849826184664541807331314824413", "52435875175126190479447740508185965530807066141876982447594476749845975030113", "52435875175126190479447740507933128785917572440565624616784716275136260809111", "52435875175126190479447532273612099891825396755801234592013277091016627662113", "52435875175126190307956157190266370280540209042396334073273195367138417459213", "52435875174984959614955767732782448015237669214112699215508711121903592721313"],
			&["536650866211219273925600", "515613692269202933647755503199", "433476440298104899261833536690159200", "358030300427067135115671589552167294279900", "294976202349764657521544847870303251955215776800", "242940041197869035334307998285435479980217794621064598", "200073270930275021618366523711686384738412705261046460157600", "164769141833752994340602057075908554923840928842777934475518194700"],
			&["52435875175126190479447740508185965837690552500527637744342169074491994429413", "52435875175126190479447740508185965837690552500452444720022395830603555030113", "52435875175126190479447740508185965837690489285741349859050823498439793177712", "52435875175126190479447740508185965785478243046953023819707332880275475903713", "52435875175126190479447740508142948840358898794190804687385132844859024774213", "52435875175126190479447705079731081914661662425323950506782848741034664721313", "52435875175126190450270636499114056327568661048905303832651360812403732219111", "52435875175102161850505151033557526797726095208809924360976388507918655022113"],
			&["1601829739462939599200", "1538959752186366920324604900", "1293794257374577229492091189765600", "1068609574404235613830498061588064473199", "880412489571442593111651789590744869108477600", "725100670268874704193827234209596714398656121669700", "597156655230182355214109012159286033518673807873815296800", "491784780262325151139842318511800901674445866929312789708474598"],
			&["52435875175126190479447740508185965837690552500527637822598986974511430316315", "52435875175126190479447740508185965837690552500527633335611698032847356145313", "52435875175126190479447740508185965837690552496755615421686831179828132329613", "52435875175126190479447740508185965837687437017476286433602951169466353338913", "52435875175126190479447740508185963270889909713009585015402529051929337524916", "52435875175126190479447740506071969669554713688561857811926748520244264386913", "52435875175126190479445999526678554192107365565196496679897686828258650764813", "52435875175126189045672870317203987883412589907615787092660514874130483647713"],
			&["1945046876074400", "1864129313105132651802", "1566614274733553480574400800", "1293880667489621465420674990505100", "1066002585927312952418811166082250223200", "877950291077021111126439137367328153814900403", "723035854762618570178213345260223758442932269522400", "595451827327505563414221142210957477534180517724387660300"],
			&["52435875175126190479447740508185965837690552500527637822603658699823189224613", "52435875175126190479447740508185965837690552500527637822603549776390385338913", "52435875175126190479447740508185965837690552500527637731260546277506185846315", "52435875175126190479447740508185965837690552500452219820724468529348155025313", "52435875175126190479447740508185965837690490367849870412821860029566077949813", "52435875175126190479447740508185965786518948790785240928128406120353047647713", "52435875175126190479447740508143823507314166635486048366791399742578476614916", "52435875175126190479447705802127798595254008926481992687797739867574849026913"],
			&["960800", "807744680100", "667157540444234400", "549661852436388016181802", "452697105941691435357049202400", "372818701621367349292382501162685300", "307032604808067352305645854537522502703200", "252854596323205247053675081227392663237129990403"]
		],
		&[
			"30405145849443316777017704233468987151623907862080992787891715947142486158490",
			"8033645548191829236070991444153722282958585223001557362841559411932712651471",
			"31223656792747693585327947844936106446473522026232517256074892244282129419922",
			"3979744679242757459875191450396480492756693099300939337219693086640761997399",
			"44810883375572296303068879280426975245103324155563771882280039089397653829804",
			"45147451763687603285556784224296263716220502442512548913165210704007753873372",
			"26630309568536788035955894586713779788739613329326104659818231653150048800110",
			"18519050835707309585285908803629726678469076966739573501897836392068597644178"
		],
		&[
			&["20508694040621567351648110034447675442497630601368754313856884903339587777311", "21833126749675005420257511508741654628498211767962591705355382899857469438170", "10094259962876866855921243786568400951965635335279511958062644189442373357290", "19703017446530302026954081842172601421653728134317178448940156258115853425803", "10251498144790729877114984073212046753223574188577263253763854582885300616634", "23799697215770479455315980501436150478606639549341703710964277906023879274693", "3007859742890615231402252990001597094047140204544326329227026628202747223471", "28206680002640467010077105488518988050496606663258696654543362871739559141116"],
			&["3001386190657217866716811031197002190094834176598601007437349105366277408753", "3302832234223427084389235892793462946069958738751625733789554798277785616852", "33828191304584863092326289783666465913001308709873493077072772336792329272781", "39527082973012175895755035046102602497048600747962062191946750704586900696815", "28051483866417948291356906371063959987011977735069581088198413305545643762525", "940230548799789892304826428424685764994822279495712794369041189518965610982", "51086698257646416011541091115454938869982232807222651212625724712549497545484", "17476372527237931823914329908105757745889986759257828348803723712031461055028"],
			&["23134431890904997735913685390433273947519177060544011867815065124418348995661", "7910743581020883359489900822814213105822551758045258908574127548576902234202", "6452335108146897903818881932868089947456740590166061243393158685187431809297", "864592593827916191968939823230510547087468030011538620003456937932684270153", "47547237971610965741643776816276041546468880714675495834455049663798422970459", "10004118136888058764408398782965078987905732598601545000387602435395348015578", "41751554506863950612723183999266149980852802057217063263129581065630539355943", "28630474321717538333837377020183699597240697917209889448356171144508785456174"],
			&["6115004495058581461679543206759074864544621607268548532579497254868522377271", "21243894977772591201471537025484718343191521031976400555572885483218590131589", "45041997413027706817259847459339150044857486303862786066504692656477384634212", "27470784997401440527873117491491648618917178731169224172695655782836909456587", "15727889512233366173678288910052541942011398314931915379504905732056403429774", "38735642770160988646558665851699780362040365495569236048392437338602088553273", "25674443904336841085471025576243298034342945745312501862648562366760045958972", "29805985527256674172328299275985498307427134349584414242520238341690757131227"],
			&["50037773927083762587334378703585422467965799754556571675786298559577822179911", "42743634847095373052484582673598508267366889230468290806816742710347159010517", "25230888235592569579852739649291188114156065738304666311395543765414524475330", "42002841091982261997065600347708363763185486593633809122360419560455919175105", "43931531654669717610310619010443906344403177136136560739782207157719497645207", "29694508805731072667404746852521915932398571942121300519061765747685009528191", "26943417286698558533808735330410936269726297255153995312193764902443048356245", "48947900935312729259001041963506432646806526437377023081917518937002348779222"],
			&["23507304312311511887109790207045158920045990953696118472141495158285130418394", "11011384867675502419373543495684168563547050483640747139867027012943403807212", "38461500758995647726535412408855515510981971579100666084853631257057293340649", "17817729615096185819243002973156747967921191173839588684293234999724241670638", "48716716172570601302373142628882378282227533504475106840182803496996412994413", "619826202783867583665089064119829568230276070730921022879082487269206247488", "6660940849085335946898968744902387962185522421886248097422254215598728282504", "34185360325984066772770249218991687215036836107735688894357874224891419374186"],
			&["9363044131613248047596942085693554696645993662963662369571529235195478342020", "19240123362991953928100324777167488301280553661411740273438618205677256309598", "9470451260683743804118606048227885162315039868898184297565748977128471423031", "4974480500435435392168724945248898058609892761691907356513707581089275041139", "50176938194458050179047559109674425081752096848792255446594266840726367413473", "22552072656827098101139538641979489313577736315726812678275330819911117604705", "24462628655256926646900208870009260661603887188897570319246731012561635601741", "6737845359986135166569504688948426613904894721534889739703098556679909300118"],
			&["43100021861314388656907065385109832997528349137939100225667770671483460050779", "3090648587858130045904946378346824962294377039255631869610002763270248366031", "857927984035689951624214141866258307708598119699217176582554033302232372107", "25377414758830765892857285129102351324548712710244289383058909254835195730234", "44028847617821326663143729919645992858395644740275387499648826409282632377325", "11527292498297078376845496876100957213628117286014463992976654667787999698365", "9266996933133471914915220132230732992025930398574006900437463345849370051699", "18251166951461627391242940852899832825179034250855348416083457399482071263702"]
		],
		&[
			"48480459620207889873329870945947122707043300817648682280324760279314294056354",
			"50693297981862734812714008364651398150474388523610230924935557663241576460628",
			"19667728447804901677655001160019492200646889650350433169295305150522887383997",
			"38117840480035523671546232301803403437726118854279282983021883995594999271842",
			"45923624370222206037015566693200187425163713837456049001618866298038020793220",
			"19178953347553121443856831257445478454951427630760076190095481370092164338688",
			"27499429733755054495326400936940868844191039079536070355973935558073320284412",
			"30889128671349312391294613623771258074136946091227396298079764667634157446438"
		]
	);

	let rng = &mut thread_rng();
	let c = RescuePermutation::<Bls12> {
		params: &rescue_params,
		x: (0..rescue_params.m).map(|_| None).collect(),
		k: (0..rescue_params.m).map(|_| None).collect()
	};
	let params = generate_random_parameters(c, rng).unwrap();

	let pvk = prepare_verifying_key(&params.vk);

	let x: Vec<Fr> = (0..rescue_params.m).map(|i| Fr::from_str(&i.to_string()).unwrap()).collect();
	let k: Vec<Fr> = (0..rescue_params.m).map(|_| Fr::from_str("0").unwrap()).collect();

	let y = rescue_cipher_block_enc(&rescue_params, &k, &x);

	let c = RescuePermutation::<Bls12> {
		params: &rescue_params,
		x: x.iter().map(|x| Some(*x)).collect(),
		k: k.iter().map(|k| Some(*k)).collect()
	};
	let proof = create_random_proof(c, &params, rng).unwrap();

	let correct = verify_proof(&pvk, &proof, &y).unwrap();

	println!("{}", correct);
}
