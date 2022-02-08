//! Tests the ipa_pc (extended and non-extended) using the Tweedle Dee as commitment group.
#![allow(non_camel_case_types)]

use algebra::{
    curves::tweedle::dee::DeeJacobian as TweedleDee, fields::tweedle::{Fr, Fq},
    Curve, Field, UniformRand, EndoMulCurve, CanonicalSerialize, serialize_no_metadata};
use blake2::Blake2s;
use digest::Digest;

use super::InnerProductArgPC;
use crate::Error;
use fiat_shamir::{
    FiatShamirRng, FiatShamirRngSeed,
};
use crate::ipa_pc::CommitterKey;
use crate::tests::TestUtils;
use crate::{
    DomainExtendedPolynomialCommitment, PCCommitterKey, PCParameters, PolynomialCommitment,
};
use rand::thread_rng;
use rayon::prelude::*;
use std::ops::Mul;

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

                assert_eq!(coeffs_l, gpu_coeffs_l);
                assert_eq!(z_l, gpu_z_l);
                assert_eq!(key_proj_l, gpu_key_proj_l);
            }

            #[test]
            fn [<fiat_shamir_rng_test_ $pc_inst_name>]() {
                // Empty test
                {
                    let mut rng1 = $fs_rng::from_seed(
                        FiatShamirRngSeed::new().finalize().unwrap(),
                    ).unwrap();
                    let mut rng2 = $fs_rng::from_seed(
                        FiatShamirRngSeed::new().finalize().unwrap(),
                    ).unwrap();

                    assert_eq!(rng1.get_state(), rng2.get_state());

                    let a: Fq = rng1.squeeze();
                    let b = rng2.squeeze();

                    assert_eq!(a, b);
                    assert_eq!(rng1.get_state(), rng2.get_state());

                    rng1.absorb::<Fq, _>("ABSORBABLE_ELEM").unwrap();
                    rng2.absorb::<Fq, _>("ABSORBABLE_ELEM").unwrap();

                    assert_eq!(rng1.get_state(), rng2.get_state());

                    let a = rng1.squeeze_128_bits_challenge::<TweedleDee>();
                    let b = rng2.squeeze_128_bits_challenge::<TweedleDee>();

                    assert_eq!(a, b);
                    assert_eq!(rng1.get_state(), rng2.get_state());
                }

                // No cross protocol attacks possible
                {
                    let fs_rng_seed = {
                        let mut seed_builder = FiatShamirRngSeed::new();
                        seed_builder.add_bytes(b"TEST_SEED").unwrap();
                        seed_builder.finalize().unwrap()
                    };

                    let malicious_fs_rng_seed = {
                        let mut seed_builder = FiatShamirRngSeed::new();
                        seed_builder.add_bytes(b"TEST_").unwrap();
                        seed_builder.add_bytes(b"SEED").unwrap();
                        seed_builder.finalize().unwrap()
                    };

                    let mut fs_rng = $fs_rng::from_seed(fs_rng_seed).unwrap();
                    let mut malicious_fs_rng = $fs_rng::from_seed(malicious_fs_rng_seed).unwrap();

                    assert_ne!(fs_rng.get_state(), malicious_fs_rng.get_state());

                    let a: Fq = fs_rng.squeeze();
                    let b = malicious_fs_rng.squeeze();

                    assert_ne!(a, b);
                    assert_ne!(fs_rng.get_state(), malicious_fs_rng.get_state());

                    fs_rng.absorb::<Fq, _>("ABSORBABLE_ELEM").unwrap();
                    malicious_fs_rng.absorb::<Fq, _>("ABSORBABLE_ELEM").unwrap();

                    assert_ne!(fs_rng.get_state(), malicious_fs_rng.get_state());

                    let a = fs_rng.squeeze_128_bits_challenge::<TweedleDee>();
                    let b = malicious_fs_rng.squeeze_128_bits_challenge::<TweedleDee>();

                    assert_ne!(a, b);
                    assert_ne!(fs_rng.get_state(), malicious_fs_rng.get_state());
                }

                // set_state test
                {
                    let fs_rng_seed = {
                        let mut seed_builder = FiatShamirRngSeed::new();
                        seed_builder.add_bytes(b"TEST_SEED").unwrap();
                        seed_builder.finalize().unwrap()
                    };
                    let mut fs_rng = $fs_rng::from_seed(fs_rng_seed).unwrap();

                    let mut fs_rng_copy = $fs_rng::default();
                    fs_rng_copy.set_state(fs_rng.get_state().clone());

                    assert_eq!(fs_rng.get_state(), fs_rng_copy.get_state());

                    fs_rng.absorb::<Fq, _>("ABSORBABLE_ELEM").unwrap();
                    fs_rng_copy.absorb::<Fq, _>("ABSORBABLE_ELEM").unwrap();

                    assert_eq!(fs_rng.get_state(), fs_rng_copy.get_state());

                    let a = fs_rng.squeeze_128_bits_challenge::<TweedleDee>();
                    let b = fs_rng_copy.squeeze_128_bits_challenge::<TweedleDee>();

                    assert_eq!(a, b);
                    assert_eq!(fs_rng.get_state(), fs_rng_copy.get_state());
                }
            }
        }
    };
}

type PC<G, FS> = InnerProductArgPC<G, FS>;

#[cfg(not(feature = "circuit-friendly"))]
mod chacha_fs {
    use super::*;
    use fiat_shamir::chacha20::FiatShamirChaChaRng;

    type CHACHA_BLAKE2S_FS_RNG = FiatShamirChaChaRng<Blake2s>;
    // The ipa_pc over the Tweedle Dee using a Chacha-Blake2s based Fiat-Shamir rng.
    type PC_DEE_CHACHA_BLAKE2S = PC<TweedleDee, FiatShamirChaChaRng<Blake2s>>;
    // its domain extended variant
    type PC_DEE_CHACHA_DE_BLAKE2S = DomainExtendedPolynomialCommitment<TweedleDee, PC_DEE_CHACHA_BLAKE2S>;
    
    generate_pc_tests!(pc_dee, PC_DEE_CHACHA_BLAKE2S, PC_DEE_CHACHA_DE_BLAKE2S, Blake2s, CHACHA_BLAKE2S_FS_RNG);
}

#[cfg(feature = "circuit-friendly")]
mod poseidon_fs {
    use super::*;
    use primitives::TweedleFqPoseidonSponge;

    type POSEIDON_TWEEDLE_FQ_FS_RNG = TweedleFqPoseidonSponge;
    type PC_DEE_POSEIDON = PC<TweedleDee, TweedleFqPoseidonSponge>;
    // its domain extended variant
    type PC_DEE_POSEIDON_DE = DomainExtendedPolynomialCommitment<TweedleDee, PC_DEE_POSEIDON>;
    
    generate_pc_tests!(pc_dee, PC_DEE_POSEIDON, PC_DEE_POSEIDON_DE, Blake2s, POSEIDON_TWEEDLE_FQ_FS_RNG);
}
// The ipa_pc over the Tweedle Dee using a Poseidon based Fiat-Shamir rng.

