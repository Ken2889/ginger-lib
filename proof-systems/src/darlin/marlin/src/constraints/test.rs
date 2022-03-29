#[cfg(test)]

mod verifier_gadget {
    use crate::constraints::data_structures::{ProofGadget, VerifierKeyGadget};
    use crate::constraints::MarlinVerifierGadget;
    use crate::test::Circuit;
    use crate::Marlin;
    use algebra::{
        test_canonical_serialize_deserialize, EndoMulCurve, SemanticallyValid, UniformRand,
    };
    use digest::Digest;
    use poly_commit::constraints::PolynomialCommitmentVerifierGadget;
    use poly_commit::{LabeledCommitmentGadget, PCKey, PolynomialCommitment};
    use r1cs_core::ConstraintSystemAbstract;
    use r1cs_core::{ConstraintSystem, ConstraintSystemDebugger, SynthesisMode};
    use r1cs_std::alloc::AllocGadget;
    use r1cs_std::fields::fp::FpGadget;
    use r1cs_std::fields::nonnative::nonnative_field_gadget::NonNativeFieldGadget;
    use r1cs_std::groups::{EndoMulCurveGadget, GroupGadget};
    use r1cs_std::to_field_gadget_vec::ToConstraintFieldGadget;
    use rand::thread_rng;
    use std::ops::MulAssign;

    fn test_circuit<G, GG, PC, PCG, D>(
        num_samples: usize,
        num_constraints: usize,
        num_variables: usize,
        zk: bool,
    ) where
        G: EndoMulCurve,
        GG: EndoMulCurveGadget<G, G::BaseField>
            + ToConstraintFieldGadget<G::BaseField, FieldGadget = FpGadget<G::BaseField>>,
        PC: PolynomialCommitment<G>,
        PCG: PolynomialCommitmentVerifierGadget<G::BaseField, G, PC>,
        D: Digest,
    {
        let rng = &mut thread_rng();

        let (original_pc_pk, original_pc_vk) = PC::setup::<D>(num_constraints - 1).unwrap();
        let (pc_pk, pc_vk) = (
            original_pc_pk.trim((num_constraints - 1) / 2).unwrap(),
            original_pc_vk.trim((num_constraints - 1) / 2).unwrap(),
        );
        assert_eq!(original_pc_pk.get_hash(), pc_pk.get_hash());
        assert_eq!(original_pc_vk.get_hash(), pc_vk.get_hash());

        for _ in 0..num_samples {
            let a = G::ScalarField::rand(rng);
            let b = G::ScalarField::rand(rng);
            let mut c = a;
            c.mul_assign(&b);
            let mut d = c;
            d.mul_assign(&b);

            let circ = Circuit {
                a: Some(a),
                b: Some(b),
                c: Some(c),
                d: Some(d),
                num_constraints,
                num_variables,
            };
            let (index_pk, index_vk) =
                Marlin::<G, PC>::circuit_specific_setup::<_, D>(&pc_pk, circ).unwrap();

            assert!(index_pk.is_valid());
            assert!(index_vk.is_valid());
            test_canonical_serialize_deserialize(true, &index_pk);
            test_canonical_serialize_deserialize(true, &index_vk);

            let proof = Marlin::<G, PC>::prove(
                &index_pk,
                &pc_pk,
                circ,
                zk,
                if zk { Some(rng) } else { None },
            )
            .unwrap();

            assert!(proof.is_valid());
            test_canonical_serialize_deserialize(true, &proof);

            // Success verification
            let correct_inputs = vec![c, d];
            assert!(Marlin::<G, PC>::verify(&index_vk, &pc_vk, &correct_inputs, &proof).unwrap());

            let mut cs = ConstraintSystem::<G::BaseField>::new(SynthesisMode::Debug);

            let verifier_key_gadget = VerifierKeyGadget::<G, PC, PCG>::alloc_input(
                cs.ns(|| "alloc verifier key"),
                || Ok(index_vk.clone()),
            )
            .unwrap();

            let pc_verifier_key_gadget =
                PCG::VerifierKeyGadget::alloc(cs.ns(|| "alloc pc verifier key"), || {
                    Ok(pc_vk.clone())
                })
                .unwrap();

            let proof_gadget =
                ProofGadget::<G, PC, PCG>::alloc_input(cs.ns(|| "alloc proof"), || {
                    Ok(proof.clone())
                })
                .unwrap();

            let public_inputs = {
                let mut public_inputs = Vec::new();
                for (i, input) in correct_inputs.iter().enumerate() {
                    public_inputs.push(
                        NonNativeFieldGadget::alloc_input(
                            cs.ns(|| format!("alloc public input {}", i)),
                            || Ok(input),
                        )
                        .unwrap(),
                    )
                }
                public_inputs
            };

            MarlinVerifierGadget::<G, GG, PC, PCG>::succinct_verify(
                cs.ns(|| "proof verification"),
                &pc_verifier_key_gadget,
                &verifier_key_gadget,
                &public_inputs,
                &proof_gadget,
            )
            .unwrap();

            if !cs.is_satisfied() {
                println!(
                    "constraint {} is unsatisfied",
                    cs.which_is_unsatisfied().unwrap()
                )
            }

            assert!(cs.is_satisfied());

            // Fail verification at the level of IOP because of wrong public inputs
            let wrong_inputs = vec![a, a];
            assert!(!Marlin::<G, PC>::verify(&index_vk, &pc_vk, &wrong_inputs, &proof).unwrap());

            let mut cs = ConstraintSystem::<G::BaseField>::new(SynthesisMode::Debug);

            let verifier_key_gadget = VerifierKeyGadget::<G, PC, PCG>::alloc_input(
                cs.ns(|| "alloc verifier key"),
                || Ok(index_vk.clone()),
            )
            .unwrap();

            let pc_verifier_key_gadget =
                PCG::VerifierKeyGadget::alloc(cs.ns(|| "alloc pc verifier key"), || {
                    Ok(pc_vk.clone())
                })
                .unwrap();

            let proof_gadget =
                ProofGadget::<G, PC, PCG>::alloc_input(cs.ns(|| "alloc proof"), || {
                    Ok(proof.clone())
                })
                .unwrap();

            let public_inputs = {
                let mut public_inputs = Vec::new();
                for (i, input) in wrong_inputs.iter().enumerate() {
                    public_inputs.push(
                        NonNativeFieldGadget::alloc_input(
                            cs.ns(|| format!("alloc public input {}", i)),
                            || Ok(input),
                        )
                        .unwrap(),
                    )
                }
                public_inputs
            };

            MarlinVerifierGadget::<G, GG, PC, PCG>::verify_iop(
                cs.ns(|| "proof verification"),
                &pc_verifier_key_gadget,
                &verifier_key_gadget,
                &public_inputs,
                &proof_gadget,
            )
            .unwrap();

            assert!(!cs.is_satisfied());

            let mut cs = ConstraintSystem::<G::BaseField>::new(SynthesisMode::Debug);

            let verifier_key_gadget = VerifierKeyGadget::<G, PC, PCG>::alloc_input(
                cs.ns(|| "alloc verifier key"),
                || Ok(index_vk.clone()),
            )
            .unwrap();

            let pc_verifier_key_gadget =
                PCG::VerifierKeyGadget::alloc(cs.ns(|| "alloc pc verifier key"), || {
                    Ok(pc_vk.clone())
                })
                .unwrap();

            let proof_gadget =
                ProofGadget::<G, PC, PCG>::alloc_input(cs.ns(|| "alloc proof"), || {
                    Ok(proof.clone())
                })
                .unwrap();

            let public_inputs = {
                let mut public_inputs = Vec::new();
                for (i, input) in correct_inputs.iter().enumerate() {
                    public_inputs.push(
                        NonNativeFieldGadget::alloc_input(
                            cs.ns(|| format!("alloc public input {}", i)),
                            || Ok(input),
                        )
                        .unwrap(),
                    )
                }
                public_inputs
            };

            // Check that IOP verification succeeds ...
            let (query_map, evaluations, mut commitments, mut fs_rng) =
                MarlinVerifierGadget::<G, GG, PC, PCG>::verify_iop(
                    cs.ns(|| "IOP verification"),
                    &pc_verifier_key_gadget,
                    &verifier_key_gadget,
                    &public_inputs,
                    &proof_gadget,
                )
                .unwrap();
            assert!(cs.is_satisfied());

            // ... then tamper with a commitment and check that opening proof fails
            let last_labeled_comm = commitments.pop().unwrap();
            let mut last_comm = last_labeled_comm.commitment().clone();
            last_comm
                .double_in_place(cs.ns(|| "double last commitment in place"))
                .unwrap();
            let last_comm_label = last_labeled_comm.label().clone();
            commitments.push(LabeledCommitmentGadget::new(last_comm_label, last_comm));
            MarlinVerifierGadget::<G, GG, PC, PCG>::succinct_verify_opening(
                cs.ns(|| "succinct opening verification"),
                &pc_verifier_key_gadget,
                &proof_gadget,
                commitments,
                query_map,
                evaluations,
                &mut fs_rng,
            )
            .unwrap();

            assert!(!cs.is_satisfied());

            // Use a vk derived from bigger universal params and check that verification fails
            // (absorbed hash won't be the same)
            let (original_pc_pk, original_pc_vk) =
                PC::setup::<D>(2 * (num_constraints - 1)).unwrap();
            let pc_vk = original_pc_vk.trim((num_constraints - 1) / 4).unwrap();
            assert_ne!(pc_pk.get_hash(), original_pc_pk.get_hash());
            assert!(!Marlin::<G, PC>::verify(&index_vk, &pc_vk, &[c, d], &proof).unwrap());

            let mut cs = ConstraintSystem::<G::BaseField>::new(SynthesisMode::Debug);

            let verifier_key_gadget = VerifierKeyGadget::<G, PC, PCG>::alloc_input(
                cs.ns(|| "alloc verifier key"),
                || Ok(index_vk.clone()),
            )
            .unwrap();

            let pc_verifier_key_gadget =
                PCG::VerifierKeyGadget::alloc(cs.ns(|| "alloc pc verifier key"), || {
                    Ok(pc_vk.clone())
                })
                .unwrap();

            let proof_gadget =
                ProofGadget::<G, PC, PCG>::alloc_input(cs.ns(|| "alloc proof"), || {
                    Ok(proof.clone())
                })
                .unwrap();

            let public_inputs = {
                let mut public_inputs = Vec::new();
                for (i, input) in correct_inputs.iter().enumerate() {
                    public_inputs.push(
                        NonNativeFieldGadget::alloc_input(
                            cs.ns(|| format!("alloc public input {}", i)),
                            || Ok(input),
                        )
                        .unwrap(),
                    )
                }
                public_inputs
            };

            MarlinVerifierGadget::<G, GG, PC, PCG>::verify_iop(
                cs.ns(|| "IOP verification"),
                &pc_verifier_key_gadget,
                &verifier_key_gadget,
                &public_inputs,
                &proof_gadget,
            )
            .unwrap();
            assert!(!cs.is_satisfied());
        }
    }

    mod poseidon_fs {
        use super::*;
        use algebra::curves::tweedle::dum::{DumJacobian, TweedledumParameters};
        use algebra::fields::tweedle::Fr;
        use algebra::Group;
        use blake2::Blake2s;
        use fiat_shamir::poseidon::constraints::DensityOptimizedPoseidonQuinticSBoxFSRngGadget;
        use fiat_shamir::poseidon::TweedleFrPoseidonFSRng;
        use poly_commit::ipa_pc::{InnerProductArgGadget, InnerProductArgPC};
        use poly_commit::{
            DomainExtendedPolyCommitVerifierGadget, DomainExtendedPolynomialCommitment,
        };
        use primitives::TweedleFrPoseidonParameters;
        use r1cs_crypto::TweedleFrDensityOptimizedPoseidonParameters;
        use r1cs_std::fields::fp::FpGadget;
        use r1cs_std::groups::curves::short_weierstrass::AffineGadget;

        type G = DumJacobian;
        type ConstraintF = <G as Group>::BaseField;
        type GG = AffineGadget<TweedledumParameters, ConstraintF, FpGadget<Fr>>;
        type FS = TweedleFrPoseidonFSRng;
        type FSG = DensityOptimizedPoseidonQuinticSBoxFSRngGadget<
            ConstraintF,
            TweedleFrPoseidonParameters,
            TweedleFrDensityOptimizedPoseidonParameters,
        >;
        type PC = DomainExtendedPolynomialCommitment<G, InnerProductArgPC<G, FS>>;
        type PCG = DomainExtendedPolyCommitVerifierGadget<
            ConstraintF,
            G,
            InnerProductArgPC<G, FS>,
            InnerProductArgGadget<ConstraintF, FSG, G, GG>,
        >;
        type D = Blake2s;

        #[test]
        fn prove_and_verify_with_square_matrix() {
            let num_constraints = 25;
            let num_variables = 25;

            test_circuit::<G, GG, PC, PCG, D>(10, num_constraints, num_variables, false);
            test_circuit::<G, GG, PC, PCG, D>(10, num_constraints, num_variables, true);
        }
    }
}
