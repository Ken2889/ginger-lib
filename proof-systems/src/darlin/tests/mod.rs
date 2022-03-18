//! Test suite for PCD post processing (batch-verification, aggregation)

pub mod final_darlin;
pub mod simple_marlin;

#[cfg(test)]
mod test {
    use crate::darlin::{
        data_structures::FinalDarlinProof,
        pcd::GeneralPCD,
        proof_aggregator::{accumulate_proofs, batch_verify_proofs, verify_aggregated_proofs},
        tests::{
            final_darlin::generate_test_data as generate_final_darlin_test_data,
            simple_marlin::generate_test_data as generate_simple_marlin_test_data,
        },
        DomainExtendedIpaPc,
    };
    use algebra::{
        curves::tweedle::{dee::DeeJacobian, dum::DumJacobian},
        serialize::test_canonical_serialize_deserialize,
        CanonicalDeserialize, CanonicalSerialize, Group, SemanticallyValid, ToConstraintField,
        UniformRand,
    };
    use blake2::Blake2s;
    use fiat_shamir::FiatShamirRng;
    use marlin::VerifierKey as MarlinVerifierKey;
    use poly_commit::{
        ipa_pc::{IPACurve, CommitterKey as DLogCommitterKey, VerifierKey as DLogVerifierKey},
        PolynomialCommitment,
    };
    use rand::{thread_rng, Rng, RngCore, SeedableRng};
    use rand_xorshift::XorShiftRng;
    use std::collections::HashSet;
    use std::fs::File;
    use std::path::Path;

    fn get_unique_random_proof_indices<R: RngCore>(pcds_len: usize, rng: &mut R) -> Vec<usize> {
        let num_proofs_to_randomize: usize = rng.gen_range(1..pcds_len / 2);
        let mut indices = (0..num_proofs_to_randomize)
            .map(|_| rng.gen_range(0..pcds_len))
            .collect::<HashSet<usize>>()
            .into_iter()
            .collect::<Vec<usize>>();
        indices.sort_unstable();
        indices
    }

    /// Generic test for `accumulate_proofs` and `verify_aggregated_proofs`
    fn test_accumulation<'a, G1: IPACurve, G2: IPACurve, FS: FiatShamirRng, R: RngCore>(
        pcds: &mut [GeneralPCD<'a, G1, G2, FS>],
        vks: &mut [MarlinVerifierKey<
            G1,
            DomainExtendedIpaPc<G1, FS>,
        >],
        committer_key_g1: &DLogCommitterKey<G1>,
        committer_key_g2: &DLogCommitterKey<G2>,
        verifier_key_g1: &DLogVerifierKey<G1>,
        verifier_key_g2: &DLogVerifierKey<G2>,
        fake_pcds: Option<&[GeneralPCD<'a, G1, G2, FS>]>,
        fake_vks: Option<
            &[MarlinVerifierKey<
                G1,
                DomainExtendedIpaPc<G1, FS>,
            >],
        >,
        rng: &mut R,
    ) where
        G1: IPACurve<BaseField = <G2 as Group>::ScalarField>
            + ToConstraintField<<G2 as Group>::ScalarField>,
        G2: IPACurve<BaseField = <G1 as Group>::ScalarField>
            + ToConstraintField<<G1 as Group>::ScalarField>,
    {
        // Accumulate PCDs
        let (proof_g1, proof_g2) =
            accumulate_proofs::<G1, G2, FS>(pcds, vks, committer_key_g1, committer_key_g2).unwrap();

        // Verify accumulation
        assert!(verify_aggregated_proofs::<G1, G2, FS, R>(
            pcds,
            vks,
            &proof_g1,
            &proof_g2,
            verifier_key_g1,
            verifier_key_g2,
            rng
        )
        .unwrap());

        // Pass wrong accumulation proof and check verification fails
        // Change one element in proof_g1
        let mut wrong_proof_g1 = proof_g1.clone().unwrap();
        wrong_proof_g1.pc_proof.c = G1::ScalarField::rand(rng);
        assert!(!verify_aggregated_proofs::<G1, G2, FS, R>(
            pcds,
            vks,
            &Some(wrong_proof_g1),
            &proof_g2,
            verifier_key_g1,
            verifier_key_g2,
            rng
        )
        .unwrap());

        // Randomize usr_ins for some PCDs and assert AHP verification fails
        let indices = get_unique_random_proof_indices(pcds.len(), rng);

        // Save original pcds and randomize existing ones
        let original_pcds = indices
            .iter()
            .map(|&idx| {
                let copy = pcds[idx].clone();
                pcds[idx].randomize_usr_ins(rng);
                copy
            })
            .collect::<Vec<_>>();

        let result = verify_aggregated_proofs::<G1, G2, FS, R>(
            pcds,
            vks,
            &proof_g1,
            &proof_g2,
            verifier_key_g1,
            verifier_key_g2,
            rng,
        );

        // Check AHP failed
        assert!(result.is_err());

        // Since the AHP failed, we are able to determine which proof verifications have failed
        assert_eq!(result.unwrap_err().unwrap(), indices);

        // Restore correct PCDs
        indices
            .into_iter()
            .zip(original_pcds)
            .for_each(|(idx, original_pcd)| pcds[idx] = original_pcd);

        // Randomize sys_ins for some PCDs and assert AHP verification fails
        let indices = get_unique_random_proof_indices(pcds.len(), rng);

        // Save original pcds and randomize existing ones
        let original_pcds = indices
            .iter()
            .map(|&idx| {
                let copy = pcds[idx].clone();
                pcds[idx].randomize_sys_ins(committer_key_g1, committer_key_g2, rng);
                copy
            })
            .collect::<Vec<_>>();

        let result = verify_aggregated_proofs::<G1, G2, FS, R>(
            pcds,
            vks,
            &proof_g1,
            &proof_g2,
            verifier_key_g1,
            verifier_key_g2,
            rng,
        );

        // Check AHP failed
        assert!(result.is_err());

        // Since the AHP failed, we are able to determine which proof verifications have failed
        assert_eq!(result.unwrap_err().unwrap(), indices);

        // Restore correct PCDs
        indices
            .into_iter()
            .zip(original_pcds)
            .for_each(|(idx, original_pcd)| pcds[idx] = original_pcd);

        if fake_pcds.is_some() && fake_vks.is_some() {
            let idx: usize = rng.gen_range(0..pcds.len());
            let original_pcd = pcds[idx].clone(); // Save correct pcd
            let original_vk = vks[idx].clone(); // Save correct pcd
            pcds[idx] = fake_pcds.unwrap()[idx].clone();
            vks[idx] = fake_vks.unwrap()[idx].clone();

            let result = verify_aggregated_proofs::<G1, G2, FS, R>(
                pcds,
                vks,
                &proof_g1,
                &proof_g2,
                verifier_key_g1,
                verifier_key_g2,
                rng,
            );

            // Check accumulation verification failed in hard part
            assert!(
                (result.is_err() && result.clone().unwrap_err().is_none())
                    || (result.is_ok() && !result.clone().unwrap())
            );

            // Restore correct PCD
            pcds[idx] = original_pcd;

            // Restore correct PCD
            vks[idx] = original_vk;
        }
    }

    /// Generic test for `batch_verify_proofs`
    fn test_batch_verification<
        'a,
        G1: IPACurve,
        G2: IPACurve,
        FS: FiatShamirRng,
        R: RngCore,
    >(
        pcds: &mut [GeneralPCD<'a, G1, G2, FS>],
        vks: &mut [MarlinVerifierKey<
            G1,
            DomainExtendedIpaPc<G1, FS>,
        >],
        verifier_key_g1: &DLogVerifierKey<G1>,
        verifier_key_g2: &DLogVerifierKey<G2>,
        fake_pcds: Option<&[GeneralPCD<'a, G1, G2, FS>]>,
        fake_vks: Option<
            &[MarlinVerifierKey<
                G1,
                DomainExtendedIpaPc<G1, FS>,
            >],
        >,
        rng: &mut R,
    ) where
        G1: IPACurve<BaseField = <G2 as Group>::ScalarField>
            + ToConstraintField<<G2 as Group>::ScalarField>,
        G2: IPACurve<BaseField = <G1 as Group>::ScalarField>
            + ToConstraintField<<G1 as Group>::ScalarField>,
    {
        // Batch Verify
        assert!(batch_verify_proofs::<G1, G2, FS, R>(
            pcds,
            vks,
            verifier_key_g1,
            verifier_key_g2,
            rng
        )
        .unwrap());

        // Randomize usr_ins for some PCDs and assert AHP verification fails
        let indices = get_unique_random_proof_indices(pcds.len(), rng);

        // Save original pcds and randomize existing ones
        let original_pcds = indices
            .iter()
            .map(|&idx| {
                let copy = pcds[idx].clone();
                pcds[idx].randomize_usr_ins(rng);
                copy
            })
            .collect::<Vec<_>>();

        let result =
            batch_verify_proofs::<G1, G2, FS, R>(pcds, vks, verifier_key_g1, verifier_key_g2, rng);

        // Check AHP failed
        assert!(result.is_err());

        // Since the AHP failed, we are able to determine which proof verifications have failed
        assert_eq!(result.unwrap_err().unwrap(), indices);

        // Restore correct PCDs
        indices
            .into_iter()
            .zip(original_pcds)
            .for_each(|(idx, original_pcd)| pcds[idx] = original_pcd);

        // Randomize sys_ins for some PCDs and assert AHP verification fails
        let indices = get_unique_random_proof_indices(pcds.len(), rng);

        // Save original pcds and randomize existing ones
        let original_pcds = indices
            .iter()
            .map(|&idx| {
                let copy = pcds[idx].clone();
                pcds[idx].randomize_sys_ins(verifier_key_g1, verifier_key_g2, rng);
                copy
            })
            .collect::<Vec<_>>();

        let result =
            batch_verify_proofs::<G1, G2, FS, R>(pcds, vks, verifier_key_g1, verifier_key_g2, rng);

        // Check AHP failed
        assert!(result.is_err());

        // Since the AHP failed, we are able to determine which proof verifications have failed
        assert_eq!(result.unwrap_err().unwrap(), indices);

        // Restore correct PCDs
        indices
            .into_iter()
            .zip(original_pcds)
            .for_each(|(idx, original_pcd)| pcds[idx] = original_pcd);

        if fake_pcds.is_some() && fake_vks.is_some() {
            let idx: usize = rng.gen_range(0..pcds.len());
            let original_pcd = pcds[idx].clone(); // Save correct pcd
            let original_vk = vks[idx].clone(); // Save correct pcd
            pcds[idx] = fake_pcds.unwrap()[idx].clone();
            vks[idx] = fake_vks.unwrap()[idx].clone();

            let result = batch_verify_proofs::<G1, G2, FS, R>(
                pcds,
                vks,
                verifier_key_g1,
                verifier_key_g2,
                rng,
            );

            // Check not failed in succinct part
            assert!(!result.is_err() || result.clone().unwrap_err().is_none());

            // Check batch verification failed in hard part
            assert!(!result.unwrap());

            // Restore correct PCD
            pcds[idx] = original_pcd;

            // Restore correct PCD
            vks[idx] = original_vk;
        }
    }

    #[cfg(not(feature = "circuit-friendly"))]
    type FsRngDee = fiat_shamir::chacha20::FiatShamirChaChaRng<Blake2s>;

    #[cfg(not(feature = "circuit-friendly"))]
    type FsRngDum = FsRngDee;

    #[cfg(feature = "circuit-friendly")]
    type FsRngDee = fiat_shamir::poseidon::TweedleFqPoseidonFSRng;

    #[cfg(feature = "circuit-friendly")]
    type FsRngDum = fiat_shamir::poseidon::TweedleFrPoseidonFSRng;

    type TestIPAPCDee = DomainExtendedIpaPc<
        DeeJacobian,
        FsRngDee,
    >;
    type TestIPAPCDum = DomainExtendedIpaPc<
        DumJacobian,
        FsRngDum,
    >;

    #[test]
    fn test_simple_marlin_proof_aggregator() {
        let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);

        // Set params
        let max_proofs = 100;
        let max_pow = 10usize;
        let segment_size = 1 << max_pow;

        // Generate keys
        let (committer_key_g1, verifier_key_g1) = TestIPAPCDee::setup::<Blake2s>(segment_size - 1).unwrap();
        let (committer_key_g2, verifier_key_g2) = TestIPAPCDum::setup::<Blake2s>(segment_size - 1).unwrap();

        // Generate fake params
        let (mut committer_key_g1_fake, mut verifier_key_g1_fake) =
            TestIPAPCDee::setup_from_seed::<Blake2s>(segment_size - 1, b"FAKE PROTOCOL").unwrap();

        committer_key_g1_fake.s = committer_key_g1.s.clone();
        committer_key_g1_fake.h = committer_key_g1.h.clone();
        committer_key_g1_fake.hash = committer_key_g1.hash.clone();

        verifier_key_g1_fake.s = verifier_key_g1.s.clone();
        verifier_key_g1_fake.h = verifier_key_g1.h.clone();
        verifier_key_g1_fake.hash = verifier_key_g1.hash.clone();

        test_canonical_serialize_deserialize(true, &committer_key_g1);
        test_canonical_serialize_deserialize(true, &committer_key_g2);
        test_canonical_serialize_deserialize(true, &verifier_key_g1);
        test_canonical_serialize_deserialize(true, &verifier_key_g2);

        // Generate pcds and index vks: we want to generate PCDs with different segment
        // sizes up at least to max_proofs, so we are going to randomly sample the segment size
        // and the number of proofs with that specific segment size to generate (to save
        // time without lacking in expressivity we just generate one and clone it
        // iteration_num_proofs time.
        let mut generated_proofs = 0;
        let mut pcds = Vec::new();
        let mut simple_marlin_vks = Vec::new();
        let mut pcds_fake = Vec::new();
        let mut simple_marlin_vks_fake = Vec::new();
        let generation_rng = &mut thread_rng();
        while generated_proofs < max_proofs {
            let iteration_num_proofs: usize = generation_rng.gen_range(1..max_proofs);
            generated_proofs += iteration_num_proofs;
            let iteration_segment_size = 1 << (generation_rng.gen_range(5..max_pow));
            let iteration_num_constraints = iteration_segment_size;
            let (mut iteration_pcds, mut iteration_vks) = generate_simple_marlin_test_data::<Blake2s, _, _, _>(
                iteration_num_constraints - 1,
                iteration_segment_size,
                (&committer_key_g1, &verifier_key_g1),
                iteration_num_proofs,
                generation_rng,
            );

            assert!(&iteration_pcds[0].proof.is_valid());
            test_canonical_serialize_deserialize(true, &iteration_pcds[0].proof);
            test_canonical_serialize_deserialize(true, &iteration_vks[0]);

            pcds.append(&mut iteration_pcds);
            simple_marlin_vks.append(&mut iteration_vks);

            let (mut iteration_pcds_fake, mut iteration_vks_fake) =
                generate_simple_marlin_test_data::<Blake2s, _, _, _>(
                    iteration_num_constraints - 1,
                    iteration_segment_size,
                    (&committer_key_g1_fake, &verifier_key_g1_fake),
                    iteration_num_proofs,
                    generation_rng,
                );

            pcds_fake.append(&mut iteration_pcds_fake);
            simple_marlin_vks_fake.append(&mut iteration_vks_fake);
        }

        // Collect PCDs
        let mut simple_marlin_pcds = pcds
            .into_iter()
            .map(|simple_marlin_pcd| {
                GeneralPCD::SimpleMarlin::<DeeJacobian, DumJacobian, FsRngDee>(
                    simple_marlin_pcd,
                )
            })
            .collect::<Vec<_>>();

        let simple_marlin_pcds_fake = pcds_fake
            .into_iter()
            .map(GeneralPCD::SimpleMarlin)
            .collect::<Vec<_>>();

        println!("Test accumulation");
        test_accumulation::<DeeJacobian, DumJacobian, FsRngDee, _>(
            simple_marlin_pcds.clone().as_mut_slice(),
            simple_marlin_vks.clone().as_mut_slice(),
            &committer_key_g1,
            &committer_key_g2,
            &verifier_key_g1,
            &verifier_key_g2,
            Some(simple_marlin_pcds_fake.as_slice()),
            Some(simple_marlin_vks_fake.as_slice()),
            rng,
        );

        println!("Test batch verification");
        test_batch_verification::<DeeJacobian, DumJacobian, FsRngDee, _>(
            simple_marlin_pcds.as_mut_slice(),
            simple_marlin_vks.as_mut_slice(),
            &verifier_key_g1,
            &verifier_key_g2,
            Some(simple_marlin_pcds_fake.as_slice()),
            Some(simple_marlin_vks_fake.as_slice()),
            rng,
        );
    }

    #[test]
    fn test_final_darlin_proof_aggregator() {
        let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);

        // Set params
        let max_proofs = 100;
        let max_pow = 10usize;
        let segment_size = 1 << max_pow;

        //Generate keys
        let (committer_key_g1, verifier_key_g1) = TestIPAPCDee::setup::<Blake2s>(segment_size - 1).unwrap();
        let (committer_key_g2, verifier_key_g2) = TestIPAPCDum::setup::<Blake2s>(segment_size - 1).unwrap();

        // Generate fake params
        let (mut committer_key_g1_fake, mut verifier_key_g1_fake) =
            TestIPAPCDee::setup_from_seed::<Blake2s>(segment_size - 1, b"FAKE PROTOCOL").unwrap();

        let (mut committer_key_g2_fake, mut verifier_key_g2_fake) =
            TestIPAPCDum::setup_from_seed::<Blake2s>(segment_size - 1, b"FAKE PROTOCOL").unwrap();

        committer_key_g1_fake.s = committer_key_g1.s.clone();
        committer_key_g1_fake.h = committer_key_g1.h.clone();
        committer_key_g1_fake.hash = committer_key_g1.hash.clone();

        verifier_key_g1_fake.s = verifier_key_g1.s.clone();
        verifier_key_g1_fake.h = verifier_key_g1.h.clone();
        verifier_key_g1_fake.hash = verifier_key_g1.hash.clone();

        committer_key_g2_fake.s = committer_key_g2.s.clone();
        committer_key_g2_fake.h = committer_key_g2.h.clone();
        committer_key_g2_fake.hash = committer_key_g2.hash.clone();

        verifier_key_g2_fake.s = verifier_key_g2.s.clone();
        verifier_key_g2_fake.h = verifier_key_g2.h.clone();
        verifier_key_g2_fake.hash = verifier_key_g2.hash.clone();

        test_canonical_serialize_deserialize(true, &committer_key_g1);
        test_canonical_serialize_deserialize(true, &committer_key_g2);
        test_canonical_serialize_deserialize(true, &verifier_key_g1);
        test_canonical_serialize_deserialize(true, &verifier_key_g2);

        // Generate pcds and index vks: we want to generate PCDs with different segment
        // sizes up to at least max_proofs, so we are going to randomly sample the segment size
        // and the number of proofs with that specific segment size to generate (to save
        // time without lacking in expressivity we just generate one and clone it
        // iteration_num_proofs time.
        let mut generated_proofs = 0;
        let mut pcds = Vec::new();
        let mut final_darlin_vks = Vec::new();
        let mut pcds_fake = Vec::new();
        let mut final_darlin_vks_fake = Vec::new();
        let generation_rng = &mut thread_rng();
        while generated_proofs < max_proofs {
            let iteration_num_proofs: usize = generation_rng.gen_range(1..max_proofs);
            generated_proofs += iteration_num_proofs;
            let iteration_segment_size = 1 << (generation_rng.gen_range(5..max_pow));
            let iteration_num_constraints = iteration_segment_size;
            let (mut iteration_pcds, mut iteration_vks) = generate_final_darlin_test_data::<Blake2s, _, _, _, _>(
                iteration_num_constraints - 1,
                iteration_segment_size,
                (&committer_key_g1, &verifier_key_g1),
                (&committer_key_g2, &verifier_key_g2),
                iteration_num_proofs,
                generation_rng,
            );

            assert!(&iteration_pcds[0].final_darlin_proof.is_valid());
            test_canonical_serialize_deserialize(true, &iteration_pcds[0].final_darlin_proof);
            test_canonical_serialize_deserialize(true, &iteration_vks[0]);

            pcds.append(&mut iteration_pcds);
            final_darlin_vks.append(&mut iteration_vks);

            let (mut iteration_pcds_fake, mut iteration_vks_fake) = generate_final_darlin_test_data::<Blake2s, _, _, _, _>(
                iteration_num_constraints - 1,
                iteration_segment_size,
                (&committer_key_g1_fake, &verifier_key_g1_fake),
                (&committer_key_g2_fake, &verifier_key_g2_fake),
                iteration_num_proofs,
                generation_rng,
            );

            pcds_fake.append(&mut iteration_pcds_fake);
            final_darlin_vks_fake.append(&mut iteration_vks_fake);
        }

        // Collect PCDs
        let mut final_darlin_pcds = pcds
            .into_iter()
            .map(GeneralPCD::FinalDarlin)
            .collect::<Vec<_>>();

        let final_darlin_pcds_fake = pcds_fake
            .into_iter()
            .map(GeneralPCD::FinalDarlin)
            .collect::<Vec<_>>();

        println!("Test accumulation");
        test_accumulation::<DeeJacobian, DumJacobian, FsRngDee, _>(
            final_darlin_pcds.clone().as_mut_slice(),
            final_darlin_vks.as_mut_slice(),
            &committer_key_g1,
            &committer_key_g2,
            &verifier_key_g1,
            &verifier_key_g2,
            Some(final_darlin_pcds_fake.as_slice()),
            Some(final_darlin_vks_fake.as_slice()),
            rng,
        );

        println!("Test batch verification");
        test_batch_verification::<DeeJacobian, DumJacobian, FsRngDee, _>(
            final_darlin_pcds.as_mut_slice(),
            final_darlin_vks.as_mut_slice(),
            &verifier_key_g1,
            &verifier_key_g2,
            Some(final_darlin_pcds_fake.as_slice()),
            Some(final_darlin_vks_fake.as_slice()),
            rng,
        );
    }

    #[test]
    fn test_mixed_proof_aggregator() {
        let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);

        // Set params
        let max_proofs = 100;
        let max_pow = 10usize;
        let segment_size = 1 << max_pow;

        //Generate keys
        let (committer_key_g1, verifier_key_g1) = TestIPAPCDee::setup::<Blake2s>(segment_size - 1).unwrap();
        let (committer_key_g2, verifier_key_g2) = TestIPAPCDum::setup::<Blake2s>(segment_size - 1).unwrap();

        // Generate fake params
        let (mut committer_key_g1_fake, mut verifier_key_g1_fake) =
            TestIPAPCDee::setup_from_seed::<Blake2s>(segment_size - 1, b"FAKE PROTOCOL").unwrap();

        let (mut committer_key_g2_fake, mut verifier_key_g2_fake) =
            TestIPAPCDum::setup_from_seed::<Blake2s>(segment_size - 1, b"FAKE PROTOCOL").unwrap();

        committer_key_g1_fake.s = committer_key_g1.s.clone();
        committer_key_g1_fake.h = committer_key_g1.h.clone();
        committer_key_g1_fake.hash = committer_key_g1.hash.clone();

        verifier_key_g1_fake.s = verifier_key_g1.s.clone();
        verifier_key_g1_fake.h = verifier_key_g1.h.clone();
        verifier_key_g1_fake.hash = verifier_key_g1.hash.clone();

        committer_key_g2_fake.s = committer_key_g2.s.clone();
        committer_key_g2_fake.h = committer_key_g2.h.clone();
        committer_key_g2_fake.hash = committer_key_g2.hash.clone();

        verifier_key_g2_fake.s = verifier_key_g2.s.clone();
        verifier_key_g2_fake.h = verifier_key_g2.h.clone();
        verifier_key_g2_fake.hash = verifier_key_g2.hash.clone();

        test_canonical_serialize_deserialize(true, &committer_key_g1);
        test_canonical_serialize_deserialize(true, &committer_key_g2);
        test_canonical_serialize_deserialize(true, &verifier_key_g1);
        test_canonical_serialize_deserialize(true, &verifier_key_g2);

        // Generate pcds and index vks: we want to generate PCDs with different segment
        // sizes up to at least max_proofs, so we are going to randomly sample the segment size
        // and the number of proofs with that specific segment size to generate (to save
        // time without lacking in expressivity we just generate one and clone it
        // iteration_num_proofs time.
        let generation_rng = &mut thread_rng();
        let mut generated_proofs = 0;
        let mut pcds = Vec::new();
        let mut vks = Vec::new();
        let mut pcds_fake = Vec::new();
        let mut vks_fake = Vec::new();
        while generated_proofs < max_proofs {
            let iteration_num_proofs: usize = generation_rng.gen_range(1..max_proofs);
            generated_proofs += iteration_num_proofs;
            let iteration_segment_size = 1 << (generation_rng.gen_range(5..max_pow));
            let iteration_num_constraints = iteration_segment_size;

            // Randomly choose if to generate a SimpleMarlinProof or a FinalDarlinProof
            let simple: bool = generation_rng.gen();
            if simple {
                let (iteration_pcds, mut iteration_vks) = generate_simple_marlin_test_data::<Blake2s, _, _, _>(
                    iteration_num_constraints - 1,
                    iteration_segment_size,
                    (&committer_key_g1, &verifier_key_g1),
                    iteration_num_proofs,
                    generation_rng,
                );

                assert!(&iteration_pcds[0].proof.is_valid());
                test_canonical_serialize_deserialize(true, &iteration_pcds[0].proof);
                test_canonical_serialize_deserialize(true, &iteration_vks[0]);

                let mut iteration_pcds = iteration_pcds
                    .into_iter()
                    .map(|pcd| GeneralPCD::SimpleMarlin(pcd))
                    .collect::<Vec<_>>();

                pcds.append(&mut iteration_pcds);
                vks.append(&mut iteration_vks);

                let (iteration_pcds_fake, mut iteration_vks_fake) =
                    generate_simple_marlin_test_data::<Blake2s, _, _, _>(
                        iteration_num_constraints - 1,
                        iteration_segment_size,
                        (&committer_key_g1_fake, &verifier_key_g1_fake),
                        iteration_num_proofs,
                        generation_rng,
                    );

                let mut iteration_pcds_fake = iteration_pcds_fake
                    .into_iter()
                    .map(|pcd| GeneralPCD::SimpleMarlin(pcd))
                    .collect::<Vec<_>>();

                pcds_fake.append(&mut iteration_pcds_fake);
                vks_fake.append(&mut iteration_vks_fake);
            } else {
                let (iteration_pcds, mut iteration_vks) = generate_final_darlin_test_data::<Blake2s, _, _, _, _>(
                    iteration_num_constraints - 1,
                    iteration_segment_size,
                    (&committer_key_g1, &verifier_key_g1),
                    (&committer_key_g2, &verifier_key_g2),
                    iteration_num_proofs,
                    generation_rng,
                );

                assert!(&iteration_pcds[0].final_darlin_proof.is_valid());
                test_canonical_serialize_deserialize(true, &iteration_pcds[0].final_darlin_proof);
                test_canonical_serialize_deserialize(true, &iteration_vks[0]);

                let mut iteration_pcds = iteration_pcds
                    .into_iter()
                    .map(GeneralPCD::FinalDarlin)
                    .collect::<Vec<_>>();

                pcds.append(&mut iteration_pcds);
                vks.append(&mut iteration_vks);

                let (iteration_pcds_fake, mut iteration_vks_fake) = generate_final_darlin_test_data::<Blake2s, _, _, _, _>(
                    iteration_num_constraints - 1,
                    iteration_segment_size,
                    (&committer_key_g1_fake, &verifier_key_g1_fake),
                    (&committer_key_g2_fake, &verifier_key_g2_fake),
                    iteration_num_proofs,
                    generation_rng,
                );

                let mut iteration_pcds_fake = iteration_pcds_fake
                    .into_iter()
                    .map(|pcd| GeneralPCD::FinalDarlin(pcd))
                    .collect::<Vec<_>>();

                pcds_fake.append(&mut iteration_pcds_fake);
                vks_fake.append(&mut iteration_vks_fake);
            }
        }

        println!("Test accumulation");
        test_accumulation::<DeeJacobian, DumJacobian, FsRngDee, _>(
            pcds.clone().as_mut_slice(),
            vks.as_mut_slice(),
            &committer_key_g1,
            &committer_key_g2,
            &verifier_key_g1,
            &verifier_key_g2,
            Some(pcds_fake.as_slice()),
            Some(vks_fake.as_slice()),
            rng,
        );

        println!("Test batch verification");
        test_batch_verification::<DeeJacobian, DumJacobian, FsRngDee, _>(
            pcds.as_mut_slice(),
            vks.as_mut_slice(),
            &verifier_key_g1,
            &verifier_key_g2,
            Some(pcds_fake.as_slice()),
            Some(vks_fake.as_slice()),
            rng,
        );
    }

    #[ignore]
    #[test]
    fn test_final_darlin_size() {
        // Set params
        let num_constraints = 1 << 19;
        let segment_size = 1 << 17;

        //Generate keys
        let (committer_key_g1, verifier_key_g1) = TestIPAPCDee::setup::<Blake2s>(segment_size - 1).unwrap();
        let (committer_key_g2, verifier_key_g2) = TestIPAPCDum::setup::<Blake2s>(segment_size - 1).unwrap();

        let generation_rng = &mut thread_rng();

        let file_path = "./size_test_proof";
        let proof;

        if Path::new(file_path).exists() {
            let fs = File::open(file_path).unwrap();
            proof =
                FinalDarlinProof::<_, _, FsRngDee>::deserialize(fs).unwrap();
        } else {
            let (iteration_pcds, _) = generate_final_darlin_test_data::<Blake2s, _, _, _, _>(
                num_constraints - 1,
                segment_size,
                (&committer_key_g1, &verifier_key_g1),
                (&committer_key_g2, &verifier_key_g2),
                1,
                generation_rng,
            );

            proof = iteration_pcds[0].final_darlin_proof.clone();

            let fs = File::create(file_path).unwrap();
            proof.serialize(fs).unwrap();
            let _ = std::fs::remove_file(file_path);
        }

        test_canonical_serialize_deserialize(true, &proof);

        println!("{} - FinalDarlinProof", proof.serialized_size());
        println!("-- {} - MarlinProof", proof.proof.serialized_size());
        println!(
            "---- {} - commitments ({})",
            proof.proof.commitments.serialized_size()
                - (proof
                    .proof
                    .commitments
                    .iter()
                    .flatten()
                    .collect::<Vec<_>>()
                    .len()
                    * 4),
            proof
                .proof
                .commitments
                .iter()
                .flatten()
                .collect::<Vec<_>>()
                .len()
        );
        println!(
            "---- {} - evaluations ({})",
            proof.proof.evaluations.serialized_size() - 8,
            proof.proof.evaluations.len()
        );
        println!("---- {} - pc_proof", proof.proof.pc_proof.serialized_size());
        println!(
            "-- {} - FinalDarlinDeferredData",
            proof.deferred.serialized_size()
        );
        println!(
            "---- {} - DLogAccumulatorG1",
            proof.deferred.pre_previous_acc.serialized_size()
        );
        println!(
            "------ {} - final_comm_key",
            proof.deferred.pre_previous_acc.final_comm_key.serialized_size()
        );
        println!(
            "------ {} - check_poly",
            proof.deferred.pre_previous_acc.check_poly.serialized_size()
        );
        println!(
            "---- {} - DLogAccumulatorG2",
            proof.deferred.previous_acc.serialized_size()
        );
        println!(
            "------ {} - final_comm_key",
            proof.deferred.previous_acc.final_comm_key.serialized_size()
        );
        println!(
            "------ {} - check_poly",
            proof.deferred.previous_acc.check_poly.serialized_size()
        );
    }
}
