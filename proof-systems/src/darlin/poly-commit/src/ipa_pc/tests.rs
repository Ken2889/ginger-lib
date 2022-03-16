//! Tests the ipa_pc (extended and non-extended) using the Tweedle Dee as commitment group.
#![allow(non_camel_case_types)]

use algebra::{
    curves::tweedle::dee::DeeJacobian as TweedleDee,
    serialize_no_metadata, CanonicalSerialize, EndoMulCurve,
};
use blake2::Blake2s;
use digest::Digest;

use super::InnerProductArgPC;

use crate::ipa_pc::CommitterKey;
use crate::tests::TestUtils;
use crate::Error;
use crate::{
    DomainExtendedPolynomialCommitment, PCCommitterKey, PCParameters, PolynomialCommitment,
};
use rand::thread_rng;

impl<G: EndoMulCurve> TestUtils for CommitterKey<G> {
    fn randomize(&mut self) {
        let mut rng = thread_rng();
        self.comm_key = self
            .comm_key
            .iter()
            .map(|_| G::rand(&mut rng).into_affine().unwrap())
            .collect::<Vec<_>>();
    }
}

use crate::tests::*;

fn exec_tests<FN: Fn(Option<NegativeType>) -> Result<(), Error>>(test: FN) {
    // Positive case
    test(None).expect("test failed");

    // Negative cases
    match test(Some(NegativeType::Values)) {
        Err(Error::FailedSuccinctCheck) => {}
        Ok(_) => {
            panic!("test should fail")
        }
        Err(e) => {
            panic!("test failed for wrong reason: {:?}", e)
        }
    };

    match test(Some(NegativeType::Commitments)) {
        Err(Error::FailedSuccinctCheck) => {}
        Ok(_) => {
            panic!("test should fail")
        }
        Err(e) => {
            panic!("test failed for wrong reason: {:?}", e)
        }
    };
    match test(Some(NegativeType::CommitterKey)) {
        Err(Error::IncorrectProof) => {}
        Ok(_) => {
            panic!("test should fail")
        }
        Err(e) => {
            panic!("test failed for wrong reason: {:?}", e)
        }
    };
    match test(Some(NegativeType::VerifierKey)) {
        Err(Error::IncorrectProof) => {}
        Ok(_) => {
            panic!("test should fail")
        }
        Err(e) => {
            panic!("test failed for wrong reason: {:?}", e)
        }
    };
}

macro_rules! generate_pc_tests {
    ($pc_inst_name: ident, $pc: ty, $de_pc: ty, $digest: ty, $fs_rng: ty) => {
        paste::item! {

            #[test]
            fn [<constant_poly_test_ $pc_inst_name>]() {
                exec_tests(|test_type| constant_poly_test::<_, $pc, $digest>(test_type));
            }

            #[test]
            fn [<single_poly_test_ $pc_inst_name>]() {
                exec_tests(|test_type| single_poly_test::<_, $pc, $digest>(test_type));
            }

            #[test]
            fn [<two_poly_four_points_test_ $pc_inst_name>]() {
                exec_tests(|test_type| two_poly_four_points_test::<_, $pc, $digest>(test_type));
            }

            #[test]
            fn [<full_end_to_end_test_ $pc_inst_name>]() {
                exec_tests(|test_type| full_end_to_end_test::<_, $pc, $digest>(test_type));
            }

            #[test]
            fn [<segmented_test_ $pc_inst_name>]() {
                exec_tests(|test_type| segmented_test::<_, $de_pc, $digest>(test_type));
            }

            #[test]
            fn [<key_hash_test_ $pc_inst_name>]() {
                let max_degree = 1 << 7;
                let supported_degree = 1 << 5;

                let pp = $pc::setup::<$digest>(max_degree).unwrap();
                let (ck, _) = pp.trim(supported_degree).unwrap();

                assert!($pc::check_key::<$digest>(&ck, max_degree));
                assert!(!$pc::check_key::<$digest>(&ck, supported_degree));
                assert!(ck.get_hash() == pp.get_hash());

                let h = $digest::digest(&serialize_no_metadata![&ck.comm_key, &ck.h, &ck.s, ck.max_degree as u32].unwrap())
                    .to_vec();
                assert_ne!(h.as_slice(), ck.get_hash());
            }

            #[test]
            fn [<polycommit_round_reduce_test_ $pc_inst_name>]() {
                use algebra::fields::tweedle::Fr;
                use algebra::{Curve, Field, UniformRand};
                use rayon::prelude::*;
                use std::ops::Mul;
                let mut rng = &mut thread_rng();

                let round_challenge = Fr::rand(&mut rng);
                let round_challenge_inv = round_challenge.inverse().unwrap();

                let samples = 1 << 10;

                let mut coeffs_l = (0..samples).map(|_| Fr::rand(&mut rng)).collect::<Vec<_>>();

                let coeffs_r = (0..samples).map(|_| Fr::rand(&mut rng)).collect::<Vec<_>>();

                let mut z_l = (0..samples).map(|_| Fr::rand(&mut rng)).collect::<Vec<_>>();

                let z_r = (0..samples).map(|_| Fr::rand(&mut rng)).collect::<Vec<_>>();

                let mut key_proj_l = (0..samples)
                    .map(|_| TweedleDee::rand(&mut rng))
                    .collect::<Vec<_>>();

                let key_r = (0..samples)
                    .map(|_| TweedleDee::rand(&mut rng))
                    .collect::<Vec<_>>();

                let mut gpu_coeffs_l = coeffs_l.clone();
                let gpu_coeffs_r = coeffs_r.clone();
                let mut gpu_z_l = z_l.clone();
                let gpu_z_r = z_r.clone();
                let mut gpu_key_proj_l = key_proj_l.clone();
                let gpu_key_r = TweedleDee::batch_into_affine(key_r.as_slice()).unwrap();

                coeffs_l
                    .par_iter_mut()
                    .zip(coeffs_r)
                    .for_each(|(c_l, c_r)| *c_l += &(round_challenge_inv * &c_r));

                z_l.par_iter_mut()
                    .zip(z_r)
                    .for_each(|(z_l, z_r)| *z_l += &(round_challenge * &z_r));

                key_proj_l
                    .par_iter_mut()
                    .zip(key_r)
                    .for_each(|(k_l, k_r)| *k_l += &k_r.mul(&round_challenge));

                
                {
                    $pc::round_reduce(
                        round_challenge,
                        round_challenge_inv,
                        &mut gpu_coeffs_l,
                        &gpu_coeffs_r,
                        &mut gpu_z_l,
                        &gpu_z_r,
                        &mut gpu_key_proj_l,
                        gpu_key_r.as_slice(),
                    );
                }


                assert_eq!(coeffs_l, gpu_coeffs_l);
                assert_eq!(z_l, gpu_z_l);
                assert_eq!(key_proj_l, gpu_key_proj_l);
            }
        }
    };
}

type PC<G, FS> = InnerProductArgPC<G, FS>;

#[cfg(not(feature = "circuit-friendly"))]
mod chacha_fs {
    use super::*;
    use fiat_shamir::chacha20::FiatShamirChaChaRng;

    // The ipa_pc over the Tweedle Dee using a Chacha-Blake2s based Fiat-Shamir rng.
    type PC_DEE_CHACHA_BLAKE2S = PC<TweedleDee, FiatShamirChaChaRng<Blake2s>>;
    // its domain extended variant
    type PC_DEE_CHACHA_DE_BLAKE2S =
        DomainExtendedPolynomialCommitment<TweedleDee, PC_DEE_CHACHA_BLAKE2S>;

    generate_pc_tests!(
        pc_dee,
        PC_DEE_CHACHA_BLAKE2S,
        PC_DEE_CHACHA_DE_BLAKE2S,
        Blake2s,
        CHACHA_BLAKE2S_FS_RNG
    );
}

#[cfg(feature = "circuit-friendly")]
mod poseidon_fs {
    use super::*;
    use fiat_shamir::poseidon::{TweedleFqPoseidonFSRng, TweedleFrPoseidonFSRng};

    // The ipa_pc over the Tweedle Dee using a Poseidon based Fiat-Shamir rng.
    type PC_DEE<FS> = PC<TweedleDee, FS>;
    // its domain extended variant
    type PC_DEE_DE<FS> = DomainExtendedPolynomialCommitment<TweedleDee, PC_DEE<FS>>;
    
    generate_pc_tests!(pc_dee_tweedle_fq_poseidon_fs, PC_DEE::<TweedleFqPoseidonFSRng>, PC_DEE_DE::<TweedleFqPoseidonFSRng>, Blake2s, TweedleFqPoseidonFSRng);
    generate_pc_tests!(pc_dee_tweedle_fr_poseidon_fs, PC_DEE::<TweedleFrPoseidonFSRng>, PC_DEE_DE::<TweedleFrPoseidonFSRng>, Blake2s, TweedleFrPoseidonFSRng);
}
