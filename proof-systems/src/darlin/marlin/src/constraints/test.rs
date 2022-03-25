#[cfg(test)]
#[cfg(feature = "circuit-friendly")]
mod verifier_gadget {
    use crate::constraints::data_structures::{ProofGadget, PublicInputsGadget, VerifierKeyGadget};
    use crate::constraints::MarlinVerifierGadget;
    use crate::test::Circuit;
    use crate::Marlin;
    use algebra::{EndoMulCurve, UniformRand};
    use digest::Digest;
    use poly_commit::constraints::PolynomialCommitmentVerifierGadget;
    use poly_commit::PolynomialCommitment;
    use r1cs_core::ConstraintSystemAbstract;
    use r1cs_core::{ConstraintSystem, ConstraintSystemDebugger, SynthesisMode};
    use r1cs_std::alloc::AllocGadget;
    use r1cs_std::fields::fp::FpGadget;
    use r1cs_std::groups::EndoMulCurveGadget;
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

        let (pc_pk, pc_vk) = PC::setup::<D>((num_constraints - 1) / 2).unwrap();

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

            let proof = Marlin::<G, PC>::prove(
                &index_pk,
                &pc_pk,
                circ,
                zk,
                if zk { Some(rng) } else { None },
            )
            .unwrap();

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

            let public_inputs_gadget =
                PublicInputsGadget::<G>::alloc_input(cs.ns(|| "alloc public inputs"), || {
                    Ok(correct_inputs)
                })
                .unwrap();

            MarlinVerifierGadget::<G, GG, PC, PCG>::verify(
                cs.ns(|| "proof verification"),
                &pc_verifier_key_gadget,
                &verifier_key_gadget,
                public_inputs_gadget,
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

            // Fail verification
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

            let public_inputs_gadget =
                PublicInputsGadget::<G>::alloc_input(cs.ns(|| "alloc public inputs"), || {
                    Ok(wrong_inputs)
                })
                .unwrap();

            MarlinVerifierGadget::<G, GG, PC, PCG>::verify(
                cs.ns(|| "proof verification"),
                &pc_verifier_key_gadget,
                &verifier_key_gadget,
                public_inputs_gadget,
                &proof_gadget,
            )
            .unwrap();

            assert!(!cs.is_satisfied());
        }
    }

    macro_rules! generate_tests {
        ($pc_inst_name: ident, $curve: ty, $curve_gadget: ty, $pc_inst: ty, $pc_gadget: ty, $digest: ty) => {
            paste::item! {
                #[test]
                fn [<prove_and_verify_with_square_matrix_ $pc_inst_name>]() {
                    let num_constraints = 25;
                    let num_variables = 25;

                    test_circuit::<$curve, $curve_gadget, $pc_inst, $pc_gadget, $digest>(10, num_constraints, num_variables, false);
                    test_circuit::<$curve, $curve_gadget, $pc_inst, $pc_gadget, $digest>(10, num_constraints, num_variables, true);
                }
            }
        };
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

        generate_tests!(dum_poseidon, G, GG, PC, PCG, D);
    }
}