//! Tests the ipa_pc (extended and non-extended) using the Tweedle Dee as commitment group.
#![allow(non_camel_case_types)]

use super::InnerProductArgPC;
use crate::Error;

use crate::fiat_shamir::{
    FiatShamirRng, FiatShamirRngSeed,
    chacha20::{FiatShamirChaChaRng, FiatShamirChaChaRngSeed}
};
use crate::ipa_pc::CommitterKey;
use crate::tests::TestUtils;
use crate::{
    DomainExtendedPolynomialCommitment, PCCommitterKey, PCParameters, PolynomialCommitment,
};
use algebra::{curves::tweedle::dee::DeeJacobian, Curve, CanonicalSerialize, serialize_no_metadata};
use blake2::Blake2s;
use digest::Digest;
use rand::thread_rng;

type PC<G, D> = InnerProductArgPC<G, D>;
// The ipa_pc over the Tweedle Dee using a Blake2s based Fiat-Shamir rng.
type PC_DEE = PC<DeeJacobian, Blake2s>;
// its domain extended variant
type PC_DEE_DE = DomainExtendedPolynomialCommitment<DeeJacobian, PC_DEE>;

impl<G: Curve> TestUtils for CommitterKey<G> {
    fn randomize(&mut self) {
        let mut rng = thread_rng();
        self.comm_key = self
            .comm_key
            .iter()
            .map(|_| G::rand(&mut rng).into_affine().unwrap())
            .collect::<Vec<_>>();
    }
}

#[test]
fn constant_poly_test() {
    use crate::tests::*;
    constant_poly_test::<_, PC_DEE>(None).expect("test failed for tweedle_dee-blake2s");
}

#[test]
fn constant_poly_negative_test() {
    use crate::tests::*;
    match constant_poly_test::<_, PC_DEE>(Some(NegativeType::Values)) {
        Err(Error::FailedSuccinctCheck) => {}
        Ok(_) => {
            panic!("test should fail for tweedle_dee-blake2s")
        }
        Err(e) => {
            panic!("test failed for tweedle_dee-blake2s: {:?}", e)
        }
    };
    match constant_poly_test::<_, PC_DEE>(Some(NegativeType::Commitments)) {
        Err(Error::FailedSuccinctCheck) => {}
        Ok(_) => {
            panic!("test should fail for tweedle_dee-blake2s")
        }
        Err(e) => {
            panic!("test failed for tweedle_dee-blake2s: {:?}", e)
        }
    };
    match constant_poly_test::<_, PC_DEE>(Some(NegativeType::CommitterKey)) {
        Err(Error::IncorrectProof) => {}
        Ok(_) => {
            panic!("test should fail for tweedle_dee-blake2s")
        }
        Err(e) => {
            panic!("test failed for tweedle_dee-blake2s: {:?}", e)
        }
    };
    match constant_poly_test::<_, PC_DEE>(Some(NegativeType::VerifierKey)) {
        Err(Error::IncorrectProof) => {}
        Ok(_) => {
            panic!("test should fail for tweedle_dee-blake2s")
        }
        Err(e) => {
            panic!("test failed for tweedle_dee-blake2s: {:?}", e)
        }
    };
}

#[test]
fn single_poly_test() {
    use crate::tests::*;
    single_poly_test::<_, PC_DEE>(None).expect("test failed for tweedle_dee-blake2s");
}

#[test]
fn single_poly_negative_test() {
    use crate::tests::*;
    match single_poly_test::<_, PC_DEE>(Some(NegativeType::Values)) {
        Err(Error::FailedSuccinctCheck) => {}
        Ok(_) => {
            panic!("test should fail for tweedle_dee-blake2s")
        }
        Err(e) => {
            panic!("test failed for tweedle_dee-blake2s: {:?}", e)
        }
    };
    match single_poly_test::<_, PC_DEE>(Some(NegativeType::Commitments)) {
        Err(Error::FailedSuccinctCheck) => {}
        Ok(_) => {
            panic!("test should fail for tweedle_dee-blake2s")
        }
        Err(e) => {
            panic!("test failed for tweedle_dee-blake2s: {:?}", e)
        }
    };
    match single_poly_test::<_, PC_DEE>(Some(NegativeType::CommitterKey)) {
        Err(Error::IncorrectProof) => {}
        Ok(_) => {
            panic!("test should fail for tweedle_dee-blake2s")
        }
        Err(e) => {
            panic!("test failed for tweedle_dee-blake2s: {:?}", e)
        }
    };
    match single_poly_test::<_, PC_DEE>(Some(NegativeType::VerifierKey)) {
        Err(Error::IncorrectProof) => {}
        Ok(_) => {
            panic!("test should fail for tweedle_dee-blake2s")
        }
        Err(e) => {
            panic!("test failed for tweedle_dee-blake2s: {:?}", e)
        }
    };
}

#[test]
fn two_poly_four_points_test() {
    use crate::tests::*;
    two_poly_four_points_test::<_, PC_DEE>(None).expect("test failed for tweedle_dee-blake2s");
}

#[test]
fn two_poly_four_points_negative_test() {
    use crate::tests::*;
    match two_poly_four_points_test::<_, PC_DEE>(Some(NegativeType::Values)) {
        Err(Error::FailedSuccinctCheck) => {}
        Ok(_) => {
            panic!("test should fail for tweedle_dee-blake2s")
        }
        Err(e) => {
            panic!("test failed for tweedle_dee-blake2s: {:?}", e)
        }
    };
    match two_poly_four_points_test::<_, PC_DEE>(Some(NegativeType::Commitments)) {
        Err(Error::FailedSuccinctCheck) => {}
        Ok(_) => {
            panic!("test should fail for tweedle_dee-blake2s")
        }
        Err(e) => {
            panic!("test failed for tweedle_dee-blake2s: {:?}", e)
        }
    };
    match two_poly_four_points_test::<_, PC_DEE>(Some(NegativeType::CommitterKey)) {
        Err(Error::IncorrectProof) => {}
        Ok(_) => {
            panic!("test should fail for tweedle_dee-blake2s")
        }
        Err(e) => {
            panic!("test failed for tweedle_dee-blake2s: {:?}", e)
        }
    };
    match two_poly_four_points_test::<_, PC_DEE>(Some(NegativeType::VerifierKey)) {
        Err(Error::IncorrectProof) => {}
        Ok(_) => {
            panic!("test should fail for tweedle_dee-blake2s")
        }
        Err(e) => {
            panic!("test failed for tweedle_dee-blake2s: {:?}", e)
        }
    };
}

#[test]
fn full_end_to_end_test() {
    use crate::tests::*;
    full_end_to_end_test::<_, PC_DEE>(None).expect("test failed for tweedle_dee-blake2s");
    println!("Finished tweedle_dee-blake2s");
}

#[test]
fn full_end_to_end_negative_test() {
    use crate::tests::*;
    match full_end_to_end_test::<_, PC_DEE>(Some(NegativeType::Values)) {
        Err(Error::FailedSuccinctCheck) => {}
        Ok(_) => {
            panic!("test should fail for tweedle_dee-blake2s")
        }
        Err(e) => {
            panic!("test failed for tweedle_dee-blake2s: {:?}", e)
        }
    };
    match full_end_to_end_test::<_, PC_DEE>(Some(NegativeType::Commitments)) {
        Err(Error::FailedSuccinctCheck) => {}
        Ok(_) => {
            panic!("test should fail for tweedle_dee-blake2s")
        }
        Err(e) => {
            panic!("test failed for tweedle_dee-blake2s: {:?}", e)
        }
    };
    match full_end_to_end_test::<_, PC_DEE>(Some(NegativeType::CommitterKey)) {
        Err(Error::IncorrectProof) => {}
        Ok(_) => {
            panic!("test should fail for tweedle_dee-blake2s")
        }
        Err(e) => {
            panic!("test failed for tweedle_dee-blake2s: {:?}", e)
        }
    };
    match full_end_to_end_test::<_, PC_DEE>(Some(NegativeType::VerifierKey)) {
        Err(Error::IncorrectProof) => {}
        Ok(_) => {
            panic!("test should fail for tweedle_dee-blake2s")
        }
        Err(e) => {
            panic!("test failed for tweedle_dee-blake2s: {:?}", e)
        }
    };
    println!("Finished tweedle_dee-blake2s");
}

#[test]
fn key_hash_test() {
    let max_degree = 1 << 7;
    let supported_degree = 1 << 5;

    let pp = PC_DEE::setup(max_degree).unwrap();
    let (ck, _) = pp.trim(supported_degree).unwrap();

    assert!(PC_DEE::check_key(&ck, max_degree));
    assert!(!PC_DEE::check_key(&ck, supported_degree));
    assert!(ck.get_hash() == pp.get_hash());

    let h = Blake2s::digest(&serialize_no_metadata![&ck.comm_key, &ck.h, &ck.s, ck.max_degree as u32].unwrap())
        .to_vec();
    assert_ne!(h.as_slice(), ck.get_hash());
}

#[test]
fn fiat_shamir_rng_test() {
    use algebra::fields::tweedle::fr::Fr;
    use algebra::UniformRand;

    // Empty test
    {
        let mut rng1 = FiatShamirChaChaRng::<Blake2s>::from_seed(
            FiatShamirChaChaRngSeed::default().finalize().unwrap(),
        );
        let mut rng2 = FiatShamirChaChaRng::<Blake2s>::default();

        assert_eq!(rng1.get_state(), rng2.get_state());

        let a = Fr::rand(&mut rng1);
        let b = Fr::rand(&mut rng2);

        assert_eq!(a, b);
        assert_eq!(rng1.get_state(), rng2.get_state());

        rng1.absorb::<Fr, _>("ABSORBABLE_ELEM").unwrap();
        rng2.absorb::<Fr, _>("ABSORBABLE_ELEM").unwrap();

        assert_eq!(rng1.get_state(), rng2.get_state());

        let a: Fr = rng1.squeeze_128_bits_challenge();
        let b: Fr = rng2.squeeze_128_bits_challenge();

        assert_eq!(a, b);
        assert_eq!(rng1.get_state(), rng2.get_state());
    }

    // No cross protocol attacks possible
    {
        let fs_rng_seed = {
            let mut seed_builder = FiatShamirChaChaRngSeed::new();
            seed_builder.add_bytes(b"TEST_SEED").unwrap();
            seed_builder.finalize().unwrap()
        };

        let malicious_fs_rng_seed = {
            let mut seed_builder = FiatShamirChaChaRngSeed::new();
            seed_builder.add_bytes(b"TEST_").unwrap();
            seed_builder.add_bytes(b"SEED").unwrap();
            seed_builder.finalize().unwrap()
        };

        let mut fs_rng = FiatShamirChaChaRng::<Blake2s>::from_seed(fs_rng_seed);
        let mut malicious_fs_rng = FiatShamirChaChaRng::<Blake2s>::from_seed(malicious_fs_rng_seed);

        assert_ne!(fs_rng.get_state(), malicious_fs_rng.get_state());

        let a = Fr::rand(&mut fs_rng);
        let b = Fr::rand(&mut malicious_fs_rng);

        assert_ne!(a, b);
        assert_ne!(fs_rng.get_state(), malicious_fs_rng.get_state());

        fs_rng.absorb::<Fr, _>("ABSORBABLE_ELEM").unwrap();
        malicious_fs_rng.absorb::<Fr, _>("ABSORBABLE_ELEM").unwrap();

        assert_ne!(fs_rng.get_state(), malicious_fs_rng.get_state());

        let a: Fr = fs_rng.squeeze_128_bits_challenge();
        let b: Fr = malicious_fs_rng.squeeze_128_bits_challenge();

        assert_ne!(a, b);
        assert_ne!(fs_rng.get_state(), malicious_fs_rng.get_state());
    }

    // set_state test
    {
        let fs_rng_seed = {
            let mut seed_builder = FiatShamirChaChaRngSeed::new();
            seed_builder.add_bytes(b"TEST_SEED").unwrap();
            seed_builder.finalize().unwrap()
        };
        let mut fs_rng = FiatShamirChaChaRng::<Blake2s>::from_seed(fs_rng_seed);

        let mut fs_rng_copy = FiatShamirChaChaRng::<Blake2s>::default();
        fs_rng_copy.set_state(fs_rng.get_state().clone());

        assert_eq!(fs_rng.get_state(), fs_rng_copy.get_state());

        fs_rng.absorb::<Fr, _>("ABSORBABLE_ELEM").unwrap();
        fs_rng_copy.absorb::<Fr, _>("ABSORBABLE_ELEM").unwrap();

        assert_eq!(fs_rng.get_state(), fs_rng_copy.get_state());

        let a: Fr = fs_rng.squeeze_128_bits_challenge();
        let b: Fr = fs_rng_copy.squeeze_128_bits_challenge();

        assert_eq!(a, b);
        assert_eq!(fs_rng.get_state(), fs_rng_copy.get_state());
    }
}

#[test]
fn polycommit_round_reduce_test() {
    use algebra::fields::tweedle::fr::Fr;
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
        .map(|_| DeeJacobian::rand(&mut rng))
        .collect::<Vec<_>>();

    let key_r = (0..samples)
        .map(|_| DeeJacobian::rand(&mut rng))
        .collect::<Vec<_>>();

    let mut gpu_coeffs_l = coeffs_l.clone();
    let gpu_coeffs_r = coeffs_r.clone();
    let mut gpu_z_l = z_l.clone();
    let gpu_z_r = z_r.clone();
    let mut gpu_key_proj_l = key_proj_l.clone();
    let gpu_key_r = DeeJacobian::batch_into_affine(key_r.as_slice()).unwrap();

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

    PC_DEE::round_reduce(
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
fn segmented_test() {
    use crate::tests::*;
    segmented_test::<_, PC_DEE_DE>(None).expect("test failed for tweedle_dee-blake2s");
    println!("Finished tweedle_dee-blake2s");
}

#[test]
fn segmented_negative_test() {
    use crate::tests::*;
    match segmented_test::<_, PC_DEE_DE>(Some(NegativeType::Values)) {
        Err(Error::FailedSuccinctCheck) => {}
        Ok(_) => {
            panic!("test should fail for tweedle_dee-blake2s")
        }
        Err(e) => {
            panic!("test failed for tweedle_dee-blake2s: {:?}", e)
        }
    };
    match segmented_test::<_, PC_DEE_DE>(Some(NegativeType::Commitments)) {
        Err(Error::FailedSuccinctCheck) => {}
        Ok(_) => {
            panic!("test should fail for tweedle_dee-blake2s")
        }
        Err(e) => {
            panic!("test failed for tweedle_dee-blake2s: {:?}", e)
        }
    };
    match segmented_test::<_, PC_DEE_DE>(Some(NegativeType::CommitterKey)) {
        Err(Error::IncorrectProof) => {}
        Ok(_) => {
            panic!("test should fail for tweedle_dee-blake2s")
        }
        Err(e) => {
            panic!("test failed for tweedle_dee-blake2s: {:?}", e)
        }
    };
    match segmented_test::<_, PC_DEE_DE>(Some(NegativeType::VerifierKey)) {
        Err(Error::IncorrectProof) => {}
        Ok(_) => {
            panic!("test should fail for tweedle_dee-blake2s")
        }
        Err(e) => {
            panic!("test failed for tweedle_dee-blake2s: {:?}", e)
        }
    };
    println!("Finished tweedle_dee-blake2s");
}
