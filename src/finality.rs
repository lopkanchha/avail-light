use std::collections::HashMap;

use codec::Encode;
use itertools::Itertools;
use serde::{Deserialize, Serialize};
use sp_core::{
	blake2_256,
	ed25519::{self, Public},
	Pair, H256,
};
use tracing::{info, warn};

use crate::types::{GrandpaJustification, SignerMessage};
use color_eyre::{eyre::eyre, Result};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ValidatorSet {
	pub set_id: u64,
	pub validator_set: Vec<Public>,
}

pub fn check_finality(
	validator_set: &ValidatorSet,
	justification: &GrandpaJustification,
) -> Result<()> {
	let ancestry_map: HashMap<H256, H256> = justification
		.votes_ancestries
		.iter()
		.map(|e| (Encode::using_encoded(e, blake2_256).into(), e.parent_hash))
		.collect();

	if !ancestry_map.is_empty() {
		info!("Votes ancestries found, mapping: {ancestry_map:?}");
	}

	// verify all the Signatures of the Justification signs,
	// verify the hash of the block and extract all the signer addresses
	let (failed_verifications, signer_addresses): (Vec<_>, Vec<_>) = justification
		.commit
		.precommits
		.iter()
		.partition_map(|precommit| {
			// form a message which is signed in the Justification, it's a triplet of a Precommit,
			// round number and set_id (taken from Substrate code)
			let signed_message = Encode::encode(&(
				&SignerMessage::PrecommitMessage(precommit.precommit.clone()),
				&justification.round,
				&validator_set.set_id, // Set ID is needed here.
			));
			let mut is_ok = <ed25519::Pair as Pair>::verify(
				&precommit.signature,
				signed_message,
				&precommit.id,
			);
			if !is_ok {
				warn!(
					"Signature verification fails with default set_id {}, trying alternatives.",
					validator_set.set_id
				);
				for set_id_m in (validator_set.set_id - 10)..(validator_set.set_id + 10) {
					let s_m = Encode::encode(&(
						&SignerMessage::PrecommitMessage(precommit.precommit.clone()),
						&justification.round,
						&set_id_m,
					));
					is_ok =
						<ed25519::Pair as Pair>::verify(&precommit.signature, &s_m, &precommit.id);
					if is_ok {
						info!("Signature match with set_id={set_id_m}");
						break;
					}
				}
			}

			let ancestry = confirm_ancestry(
				&precommit.precommit.target_hash,
				&justification.commit.target_hash,
				&ancestry_map,
			);
			(is_ok && ancestry)
				.then(|| precommit.clone().id)
				.ok_or_else(|| {
					eyre!(
				"Not signed by this signature! Sig id: {:?}, set_id: {}, justification: {:?}",
				&precommit.id,
				validator_set.set_id,
				justification
			)
				})
				.into()
		});

	if !failed_verifications.is_empty() {
		warn!("Failed verifications found: {failed_verifications:?}")
	}

	// match all the Signer addresses to the Current Validator Set
	let num_matched_addresses = signer_addresses
		.iter()
		.filter(|x| validator_set.validator_set.iter().any(|e| e.0.eq(&x.0)))
		.count();

	info!(
		"Number of matching signatures: {num_matched_addresses}/{} for block {}, set_id {}",
		validator_set.validator_set.len(),
		justification.commit.target_number,
		validator_set.set_id
	);

	is_signed_by_supermajority(num_matched_addresses, validator_set.validator_set.len())
		.then_some(())
		.ok_or(eyre!("Not signed by supermajority of validator set!"))
}

fn is_signed_by_supermajority(num_signatures: usize, validator_set_size: usize) -> bool {
	let supermajority = (validator_set_size * 2 / 3) + 1;
	num_signatures >= supermajority
}

fn confirm_ancestry(
	child_hash: &H256,
	root_hash: &H256,
	ancestry_map: &HashMap<H256, H256>,
) -> bool {
	if child_hash == root_hash {
		return true;
	}

	let mut curr_hash = child_hash;

	// We should be able to test it in at most ancestry_map.len() passes
	for _ in 0..ancestry_map.len() {
		if let Some(parent_hash) = ancestry_map.get(curr_hash) {
			if parent_hash == root_hash {
				return true;
			}
			curr_hash = parent_hash;
		} else {
			return false;
		}
	}

	false
}

#[cfg(test)]
mod tests {
	use avail_subxt::api::runtime_types::avail_core::data_lookup::compact::CompactDataLookup;
	use avail_subxt::api::runtime_types::avail_core::header::extension::v3::HeaderExtension as V3H;
	use avail_subxt::api::runtime_types::avail_core::header::extension::HeaderExtension;
	use avail_subxt::api::runtime_types::avail_core::kate_commitment::v3::KateCommitment;
	use avail_subxt::primitives::Header as DaHeader;
	use codec::{Decode, Encode};
	use hex::FromHex;
	use serde::Serialize;
	use sp_core::bytes::from_hex;
	use sp_core::ed25519::{self, Pair, Public, Signature};
	use sp_core::{blake2_256, Pair as PairT, H256};
	use subxt::config::substrate::Digest;
	use test_case::test_case;

	use crate::types::{Commit, GrandpaJustification, Precommit, SignedPrecommit, SignerMessage};

	use super::{check_finality, ValidatorSet};
	#[test_case(1, 1 => true)]
	#[test_case(1, 2 => false)]
	#[test_case(2, 2 => true)]
	#[test_case(2, 3 => false)]
	#[test_case(3, 3 => true)]
	#[test_case(3, 4 => true)]
	#[test_case(4, 5 => true)]
	#[test_case(66, 100 => false)]
	#[test_case(67, 100 => true)]
	fn check_supermajority_condition(num_signatures: usize, validator_set_size: usize) -> bool {
		use super::is_signed_by_supermajority;
		is_signed_by_supermajority(num_signatures, validator_set_size)
	}

	#[test_case("019150591418c44041725fc53bbe69fdfb5ec4ad7c35fa3f680db07f41e096988ac3fe0314ca9829fa44fc29e5507bd56f5fa4c45fc955030309bb662f70a10e", "f55c915b3e25a013931f5401a22c3481123584d9ce5a119cabf353bca5c43f05", 41911, "0501c3f8cbba5745aa58ff5f4d8dea89fc2326aa0c95d3eb6fb8070d77511ba9", 14, 9649   => true)]
	#[test_case("b7d22a1854a4836f3d4e7f1af03f8d762913afcf2aa5b20dbdfd23af3e046e80d7410281fdb185b820687a7abe1d201ff866759b00ed2cfc0bab210cea1f7b07", "b91026ef68a88f5ab767a2a7386ac0e7dbb4e62220df1f1c865595bf3afc990b", 39863, "07bc6fca05724fb6cac16fedb80688185ddc74746c7105bddb871cccc626e5e0", 12, 8628   => true)]
	#[test_case("f5a0393906f81082fe03f74eba1a403ce3d39596b0a74f25962d6c1bb2cfe351506a5d73de8d57ff9d0813234b17273f9ee955a95b69dbba5da5c80a8783990a", "97a44517c9cf63c57b71ed76470e46c83c709cdad1c5f443e584724f73b3ab50", 423568, "a9fd0c093f2ef51dbcad38f15103a1862f475b4dc35f3bc796aad1d7cad3364f", 188, 18122   => true)]

	fn check_sig(
		sig_hex: &str,
		target_hash_hex: &str,
		target_number: u32,
		sig_id_hex: &str,
		set_id: u64,
		round: u64,
	) -> bool {
		let sig = Signature(<[u8; 64]>::from_hex(sig_hex).unwrap());
		let precommit_message = Precommit {
			target_hash: <[u8; 32]>::from_hex(target_hash_hex).unwrap().into(),
			target_number,
		};
		let id: Public = Public(<[u8; 32]>::from_hex(sig_id_hex).unwrap());
		let signed_message = Encode::encode(&(
			&SignerMessage::PrecommitMessage(precommit_message),
			&round,
			&set_id,
		));

		<ed25519::Pair as PairT>::verify(&sig, signed_message, &id)
	}

	#[test]
	fn test_check_finality() {
		let set_id: u64 = 1;
		let round: u64 = 1;
		let validator_mnems = vec![
			"bottom drive obey lake curtain smoke basket hold race lonely fit walk//Alice",
			"bottom drive obey lake curtain smoke basket hold race lonely fit walk//Bob",
			"bottom drive obey lake curtain smoke basket hold race lonely fit walk//Charlie",
			"bottom drive obey lake curtain smoke basket hold race lonely fit walk//Dave",
		];

		let validator_pairs = validator_mnems
			.into_iter()
			.map(|e| <Pair as PairT>::from_string_with_seed(e, None).unwrap().0)
			.collect::<Vec<_>>();

		let validator_set = validator_pairs
			.clone()
			.into_iter()
			.map(|e| e.public())
			.collect::<Vec<_>>();
		let valset = ValidatorSet {
			set_id,
			validator_set,
		};

		let root_hash = DaHeader {
			parent_hash: H256::zero(),
			number: 1,
			state_root: H256::zero(),
			extrinsics_root: H256::zero(),
			digest: Digest { logs: vec![] },
			extension: HeaderExtension::V3(V3H {
				app_lookup: CompactDataLookup {
					size: 0,
					index: vec![],
				},
				commitment: KateCommitment {
					rows: 0,
					cols: 0,
					commitment: vec![],
					data_root: H256::zero(),
				},
			}),
		};
		let h_a = DaHeader {
			parent_hash: Encode::using_encoded(&root_hash, blake2_256).into(),
			number: 2,
			state_root: H256::random(),
			extrinsics_root: H256::zero(),
			digest: Digest { logs: vec![] },
			extension: HeaderExtension::V3(V3H {
				app_lookup: CompactDataLookup {
					size: 0,
					index: vec![],
				},
				commitment: KateCommitment {
					rows: 0,
					cols: 0,
					commitment: vec![],
					data_root: H256::zero(),
				},
			}),
		};
		let h_b = DaHeader {
			parent_hash: Encode::using_encoded(&h_a, blake2_256).into(),
			number: 3,
			state_root: H256::random(),
			extrinsics_root: H256::zero(),
			digest: Digest { logs: vec![] },
			extension: HeaderExtension::V3(V3H {
				app_lookup: CompactDataLookup {
					size: 0,
					index: vec![],
				},
				commitment: KateCommitment {
					rows: 0,
					cols: 0,
					commitment: vec![],
					data_root: H256::zero(),
				},
			}),
		};
		let h_c = DaHeader {
			parent_hash: Encode::using_encoded(&h_a, blake2_256).into(),
			number: 3,
			state_root: H256::random(),
			extrinsics_root: H256::zero(),
			digest: Digest { logs: vec![] },
			extension: HeaderExtension::V3(V3H {
				app_lookup: CompactDataLookup {
					size: 0,
					index: vec![],
				},
				commitment: KateCommitment {
					rows: 0,
					cols: 0,
					commitment: vec![],
					data_root: H256::zero(),
				},
			}),
		};
		let h_d = DaHeader {
			parent_hash: Encode::using_encoded(&root_hash, blake2_256).into(),
			number: 2,
			state_root: H256::random(),
			extrinsics_root: H256::zero(),
			digest: Digest { logs: vec![] },
			extension: HeaderExtension::V3(V3H {
				app_lookup: CompactDataLookup {
					size: 0,
					index: vec![],
				},
				commitment: KateCommitment {
					rows: 0,
					cols: 0,
					commitment: vec![],
					data_root: H256::zero(),
				},
			}),
		};
		let h_e = DaHeader {
			parent_hash: Encode::using_encoded(&h_d, blake2_256).into(),
			number: 3,
			state_root: H256::zero(),
			extrinsics_root: H256::zero(),
			digest: Digest { logs: vec![] },
			extension: HeaderExtension::V3(V3H {
				app_lookup: CompactDataLookup {
					size: 0,
					index: vec![],
				},
				commitment: KateCommitment {
					rows: 0,
					cols: 0,
					commitment: vec![],
					data_root: H256::zero(),
				},
			}),
		};
		let h_f = DaHeader {
			parent_hash: Encode::using_encoded(&h_c, blake2_256).into(),
			number: 4,
			state_root: H256::zero(),
			extrinsics_root: H256::zero(),
			digest: Digest { logs: vec![] },
			extension: HeaderExtension::V3(V3H {
				app_lookup: CompactDataLookup {
					size: 0,
					index: vec![],
				},
				commitment: KateCommitment {
					rows: 0,
					cols: 0,
					commitment: vec![],
					data_root: H256::zero(),
				},
			}),
		};

		let precommit_1 = Precommit {
			target_hash: Encode::using_encoded(&h_b, blake2_256).into(),
			target_number: h_b.number,
		};
		let precommit_2 = Precommit {
			target_hash: Encode::using_encoded(&h_c, blake2_256).into(),
			target_number: h_c.number,
		};
		let precommit_3 = Precommit {
			target_hash: Encode::using_encoded(&h_f, blake2_256).into(),
			target_number: h_f.number,
		};
		let precommit_4 = Precommit {
			target_hash: Encode::using_encoded(&h_e, blake2_256).into(),
			target_number: h_e.number,
		};

		let signed_message_1 = Encode::encode(&(
			&SignerMessage::PrecommitMessage(precommit_1.clone()),
			&round,
			&set_id,
		));
		let signed_message_2 = Encode::encode(&(
			&SignerMessage::PrecommitMessage(precommit_2.clone()),
			&round,
			&set_id,
		));
		let signed_message_3 = Encode::encode(&(
			&SignerMessage::PrecommitMessage(precommit_3.clone()),
			&round,
			&set_id,
		));
		let signed_message_4 = Encode::encode(&(
			&SignerMessage::PrecommitMessage(precommit_4.clone()),
			&round,
			&set_id,
		));

		let sig_1 = validator_pairs[0].sign(&signed_message_1);
		let sig_2 = validator_pairs[1].sign(&signed_message_2);
		let sig_3 = validator_pairs[2].sign(&signed_message_3);
		let sig_4 = validator_pairs[3].sign(&signed_message_4);

		let signed_precommit_1 = SignedPrecommit {
			precommit: precommit_1,
			signature: sig_1,
			id: validator_pairs[0].public(),
		};
		let signed_precommit_2 = SignedPrecommit {
			precommit: precommit_2,
			signature: sig_2,
			id: validator_pairs[1].public(),
		};
		let signed_precommit_3 = SignedPrecommit {
			precommit: precommit_3,
			signature: sig_3,
			id: validator_pairs[2].public(),
		};
		let signed_precommit_4 = SignedPrecommit {
			precommit: precommit_4,
			signature: sig_4,
			id: validator_pairs[3].public(),
		};

		let commit = Commit {
			target_hash: Encode::using_encoded(&root_hash, blake2_256).into(),
			target_number: root_hash.number,
			precommits: vec![
				signed_precommit_1,
				signed_precommit_2,
				signed_precommit_3,
				signed_precommit_4,
			],
		};
		let just = GrandpaJustification {
			round,
			commit,
			votes_ancestries: vec![
				h_a.clone(),
				h_b.clone(),
				h_c.clone(),
				h_d.clone(),
				h_e.clone(),
				h_f.clone(),
			],
		};
		let hashes: Vec<H256> = vec![h_a, h_b, h_c, h_d, h_e, h_f]
			.into_iter()
			.map(|e| Encode::using_encoded(&e, blake2_256).into())
			.collect::<Vec<_>>();
		// println!("votes_anc: {:?}", just.votes_ancestries);
		// println!("hashes: {:?}", hashes);

		#[derive(Clone, Debug, Serialize)]
		struct ValJust {
			validator_set: ValidatorSet,
			justification: GrandpaJustification,
		}
		let valjust = ValJust {
			justification: just.clone(),
			validator_set: valset.clone(),
		};

		let a = serde_json::to_string(&valjust).unwrap();
		println!("valjust:\n{a}");

		let _ = check_finality(&valset, &just).unwrap();
	}
	#[test_case(
		"c801000000000000b4ab92948e78b5e3115d2ce5ff2207e7d713a7fb33f4a9240e413c00954f244b01000000100ca43443bd45d344a7f29cdca19afac9a7cef5cc71c89cf4b65af672432fa6db030000004be6b2df16a0e47a13c45e90b4334835ff0fd8deab032fa0bb683cf51ca49c5e3f7d124a46ae172f7985a170f06e97fc8bf7b7ad2ddb8e6cbb2430b0b945fa0e88dc3417d5058ec4b4503e0c12ea1a0a89be200fe98922423d4334014fa6b0ee01816dbbf9fe6e645530b41adfaa5a105550559b5858fb0ea6aae6c5f64057a003000000cd4e6fd3a11c639458528a88fc48bc9e9d51fc5dbabc6e875479f08acce6f8c2d87d839590d43ee4e5a574dc614b4ce7e138edd059444b57c141b14d15b4bd02d17c2d7823ebf260fd138f2d7e27d114c0145d968b5ff5006125f2414fadae69c14d4d55d9562d3167335015343187e8a2c40eda6c0c8561308dbdd774fdb5c3040000004006be985cd77341333ec8e962389ce233fc2eb1e7889b7f60ebe61f4a64d5d456cdac29109abe374c77c32ffd08f42d1293879c7a579b77cfe67b044851c505439660b36c6c03afafca027b910b4fecf99801834c62a5e6006f27d978de234feef0e9c1641c7679146a69f0139ca8c784ddf6eae7d4b74732ff72256de6bb1f030000003ea2846fdabf39ebb71e6831c61aadb8e2afe7c0c16b3eb0a2991c7f264288f325e133c6099d30a99e918b860425e47a1cd9d1da3c354328462e9f2a8e1c130a5e639b43e0052c47447dac87d6fd2b6ec50bdd4d0f614e4299c665249bbd09d918b4ab92948e78b5e3115d2ce5ff2207e7d713a7fb33f4a9240e413c00954f244b089c866c30768c48a2e4010e9d7150d8900dd2b78adcf938023ad39bcaa83c35f50000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000417d61e53fdf8de08aa28a40f5afb875ea69783632e37e8fc9fe072f0ff93c0b0cff4293197a473fea5a88d5c7b60cc9d3c20f39f0ae105f6bb48bc51295a5a0cf0000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000417d61e53fdf8de08aa28a40f5afb875ea69783632e37e8fc9fe072f0ff93c0b0c3e448b65ca3948c1944892782b4c134bdde0592044595faede6227b57c3ceac00000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000b4ab92948e78b5e3115d2ce5ff2207e7d713a7fb33f4a9240e413c00954f244b0891ddbb28955a6c9619805b2507e1955ffa56585240a4c64d0fdb482110cd88f90000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000c41b431904f3f0a7bbee248329df9da724f865aa324fd390f0bb8f06ff8da0640c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000001816dbbf9fe6e645530b41adfaa5a105550559b5858fb0ea6aae6c5f64057a01000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000" => true;
	 	"Complex ancestry")]
	#[test_case(
	"c801000000000000b4ab92948e78b5e3115d2ce5ff2207e7d713a7fb33f4a9240e413c00954f244b01000000109b42e1ef9c3e0f5214acdafb08bd4b8051b0d910c3dd82f45b7b217ca33e876703000000e3e7fd7a535444b38afa92784363d6961e764c9c3493ce81f144765b0d4981e9ebdad80ce94961037c6daefeec8341e41c86b2fe37e9fa1b5a7e9808b346370388dc3417d5058ec4b4503e0c12ea1a0a89be200fe98922423d4334014fa6b0eef0eb6b95a658effa5ee02fdd6039ef79103650f0c9e745ccf8cd726eefff1daa03000000a6741fa9a1d62b4e2cada9801aeee2d42a3d9405273f5006d375afe29835a990d21a0e96d7a1e2bf98715c276b4f4bb0ed341c7f88754fc5a1ae48d079b48903d17c2d7823ebf260fd138f2d7e27d114c0145d968b5ff5006125f2414fadae69f5fd161e9c929ced34e8d4a7f75c8fcae437afd951eb88937b674253a1449a9c040000007b880b771e8e9593e800b0c939ca5bada3a0fa85a52eef501419c219a73715422177fabaff0202b01848cd27ab19155562726e82505b0c05d82edd4d92c05c04439660b36c6c03afafca027b910b4fecf99801834c62a5e6006f27d978de234f1558ce4a6a8fc0a92a390e485b54c5da6a9c9df7df762e9faf95a0f87225cd8203000000715a13d67cd6e93f9359a3f29c447d8f6c248c1db381ac4f45e72a1941dba98cfbb1a3ddf2e68e4cd4b5fe50006cd3ba6df37d0a20383f1ac2f150056d8c3c0a5e639b43e0052c47447dac87d6fd2b6ec50bdd4d0f614e4299c665249bbd09d914677375d8c80ab2edf460e0cc94d324220b10d096591196373dfb62dc7796d7820ce6cbe9ea2c71126d3848bd6788406fdeb957032873b1f40f44370d5ac3d699480000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000677375d8c80ab2edf460e0cc94d324220b10d096591196373dfb62dc7796d7820c32257dac982ea66d52157c716dc7b8d1bf7f53fddf5a70b7f18378fcdf8a3ebb0000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000b4ab92948e78b5e3115d2ce5ff2207e7d713a7fb33f4a9240e413c00954f244b085dd3965ed19e14bf34c4538bbb3104d4a9c7641b28136983ce86386e72f226da0000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000c484fbddff13f2426e0fd98d039b68fedfe8651b4d2b5bf540c1dc84a2fdac460c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000f0eb6b95a658effa5ee02fdd6039ef79103650f0c9e745ccf8cd726eefff1daa1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000" => false;
		"Missing ancestor negative case")]
	fn fin_test(justification_encoded: &str) -> bool {
		let just_enc = from_hex(justification_encoded).unwrap();
		let just: GrandpaJustification = Decode::decode(&mut &just_enc[..]).unwrap();
		let valset_json = r#"{
			"set_id": 123,
			"validator_set": [
			  "5FA9nQDVg267DEd8m1ZypXLBnvN7SFxYwV7ndqSYGiN9TTpu",
			  "5GoNkf6WdbxCFnPdAnYYQyCjAKPJgLNxXwPjwTh6DGg6gN3E",
			  "5DbKjhNLpqX3zqZdNBc9BGb4fHU1cRBaDhJUskrvkwfraDi6",
			  "5ECTwv6cZ5nJQPk6tWfaTrEk8YH2L7X1VT4EL5Tx2ikfFwb7"
			]
		  }"#;
		let valset: ValidatorSet = serde_json::from_str(&valset_json).unwrap();

		check_finality(&valset, &just).is_ok()
	}
}
