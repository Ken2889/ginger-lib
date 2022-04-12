use algebra::PrimeField;
use r1cs_core::{ConstraintSynthesizer, ConstraintSystemAbstract, SynthesisError};

/// A simple test circuit for the language {(c,d): (c,d)=a*(b,b^2), a,b from F}
/// by allocating `num_variables` dummy witnesses and repeating `num_constraints`
/// often the same quadratic constraints a*b=c and b*c=d.
// TODO: replace this example by a more representative (high-rank A,B,C).
#[derive(Copy, Clone)]
struct Circuit<F: PrimeField> {
    a: Option<F>,
    b: Option<F>,
    c: Option<F>,
    d: Option<F>,
    num_constraints: usize,
    num_variables: usize,
}

impl<F: PrimeField> ConstraintSynthesizer<F> for Circuit<F> {
    fn generate_constraints<CS: ConstraintSystemAbstract<F>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let a = cs.alloc(|| "a", || self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = cs.alloc(|| "b", || self.b.ok_or(SynthesisError::AssignmentMissing))?;
        let c = cs.alloc_input(|| "c", || self.c.ok_or(SynthesisError::AssignmentMissing))?;
        let d = cs.alloc_input(|| "d", || self.d.ok_or(SynthesisError::AssignmentMissing))?;

        for i in 0..(self.num_variables - 3) {
            let _ = cs.alloc(
                || format!("var {}", i),
                || self.a.ok_or(SynthesisError::AssignmentMissing),
            )?;
        }

        for i in 0..(self.num_constraints - 1) {
            cs.enforce(
                || format!("constraint {}", i),
                |lc| lc + a,
                |lc| lc + b,
                |lc| lc + c,
            );
        }
        cs.enforce(
            || format!("constraint {}", self.num_constraints - 1),
            |lc| lc + c,
            |lc| lc + b,
            |lc| lc + d,
        );
        Ok(())
    }
}

mod t_dlog_acc_marlin {
    use super::*;

    use crate::darlin::accumulators::dual::DualAccumulatorItem;
    use crate::darlin::accumulators::Accumulator;
    use crate::darlin::t_dlog_acc_marlin::data_structures::PC;
    use crate::darlin::t_dlog_acc_marlin::iop::{DualTDLogAccumulator, TDLogAccumulator};
    use crate::darlin::t_dlog_acc_marlin::TDLogAccMarlin;
    use crate::darlin::IPACurve;
    use algebra::{
        serialize::test_canonical_serialize_deserialize, DualCycle, Group, SemanticallyValid,
        ToConstraintField, UniformRand,
    };
    use digest::Digest;
    use fiat_shamir::FiatShamirRng;
    use poly_commit::{PCKey, PolynomialCommitment};
    use rand::thread_rng;
    use std::ops::MulAssign;

    fn test_circuit<G1, G2, FS, D>(
        num_samples: usize,
        num_constraints: usize,
        num_variables: usize,
        zk: bool,
    ) where
        G1: IPACurve + ToConstraintField<<G1 as Group>::BaseField>,
        G2: IPACurve + ToConstraintField<<G2 as Group>::BaseField>,
        G1: DualCycle<G2>,
        FS: FiatShamirRng + 'static,
        D: Digest + 'static,
    {
        let rng = &mut thread_rng();

        let (pc_pk_g1_original, pc_vk_g1_original) =
            <PC<G1, FS> as PolynomialCommitment<G1>>::setup::<D>(num_constraints - 1).unwrap();
        let pc_pk_g1 = pc_pk_g1_original.trim((num_constraints - 1) / 2).unwrap();
        let pc_vk_g1 = pc_vk_g1_original.trim((num_constraints - 1) / 2).unwrap();
        assert_eq!(pc_pk_g1.get_hash(), pc_pk_g1_original.get_hash());
        assert_eq!(pc_vk_g1.get_hash(), pc_vk_g1_original.get_hash());

        let (pc_pk_g2_original, pc_vk_g2_original) =
            <PC<G2, FS> as PolynomialCommitment<G2>>::setup::<D>(num_constraints - 1).unwrap();
        let pc_pk_g2 = pc_pk_g2_original.trim((num_constraints - 1) / 2).unwrap();
        let pc_vk_g2 = pc_vk_g2_original.trim((num_constraints - 1) / 2).unwrap();
        assert_eq!(pc_pk_g2.get_hash(), pc_pk_g2_original.get_hash());
        assert_eq!(pc_vk_g2.get_hash(), pc_vk_g2_original.get_hash());

        for _ in 0..num_samples {
            let a = G1::ScalarField::rand(rng);
            let b = G1::ScalarField::rand(rng);
            let mut c = a;
            c.mul_assign(&b);
            let mut d = c;
            d.mul_assign(&b);

            let circ_g1 = Circuit {
                a: Some(a),
                b: Some(b),
                c: Some(c),
                d: Some(d),
                num_constraints,
                num_variables,
            };

            let a_g2 = G2::ScalarField::rand(rng);
            let b_g2 = G2::ScalarField::rand(rng);
            let mut c_g2 = a_g2;
            c_g2.mul_assign(&b_g2);
            let mut d_g2 = c_g2;
            d_g2.mul_assign(&b_g2);

            let circ_g2 = Circuit {
                a: Some(a_g2),
                b: Some(b_g2),
                c: Some(c_g2),
                d: Some(d_g2),
                num_constraints,
                num_variables,
            };

            let (index_pk_g1, index_vk_g1) =
                TDLogAccMarlin::<G1, G2, FS, D>::circuit_specific_setup(&pc_pk_g1, circ_g1)
                    .unwrap();
            let (index_pk_g2, index_vk_g2) =
                TDLogAccMarlin::<G2, G1, FS, D>::circuit_specific_setup(&pc_pk_g2, circ_g2)
                    .unwrap();

            assert!(index_pk_g1.is_valid());
            assert!(index_vk_g1.is_valid());
            assert!(index_pk_g2.is_valid());
            assert!(index_vk_g2.is_valid());

            println!("Called index");

            test_canonical_serialize_deserialize(true, &index_pk_g1);
            test_canonical_serialize_deserialize(true, &index_vk_g1);
            test_canonical_serialize_deserialize(true, &index_pk_g2);
            test_canonical_serialize_deserialize(true, &index_vk_g2);

            let dual_t_dlog_acc = DualTDLogAccumulator::<_, _, _, _, FS>::random_item(
                &(
                    &(&(&index_vk_g2, &pc_vk_g2), &pc_vk_g2),
                    &(&(&index_vk_g1, &pc_vk_g1), &pc_vk_g1),
                ),
                rng,
            )
            .unwrap();

            let t_dlog_polys = DualTDLogAccumulator::<_, _, _, _, FS>::expand_item(
                &(
                    &(&(&index_vk_g2, &pc_vk_g2), &pc_vk_g2),
                    &(&(&index_vk_g1, &pc_vk_g1), &pc_vk_g1),
                ),
                &dual_t_dlog_acc,
            )
            .unwrap();

            let t_poly_g1 = &t_dlog_polys[0].0;
            let bullet_poly_g1 = &t_dlog_polys[0].1;

            let proof = TDLogAccMarlin::<G1, G2, FS, D>::prove(
                &index_pk_g1,
                &pc_pk_g1,
                circ_g1,
                &dual_t_dlog_acc,
                t_poly_g1,
                bullet_poly_g1,
                zk,
                if zk { Some(rng) } else { None },
            );

            assert!(proof.is_ok());

            let proof = proof.unwrap();

            assert!(proof.is_valid());

            println!("Called prover");

            test_canonical_serialize_deserialize(true, &proof);

            // Success verification
            assert!(TDLogAccMarlin::<G1, G2, FS, D>::verify(
                &index_vk_g1,
                &index_vk_g2,
                &pc_vk_g1,
                &pc_vk_g2,
                &[c, d],
                &dual_t_dlog_acc,
                &proof
            )
            .is_ok());

            // Fail verification (wrong public input)
            assert!(!TDLogAccMarlin::<G1, G2, FS, D>::verify(
                &index_vk_g1,
                &index_vk_g2,
                &pc_vk_g1,
                &pc_vk_g2,
                &[a, a],
                &dual_t_dlog_acc,
                &proof
            )
            .is_ok());

            /*
            Generate a dual dlog accumulator which is invalid in its G1 part and check that
            the succinct verification of the proof fails.
             */
            let t_dlog_acc_g1_invalid =
                TDLogAccumulator::invalid_item(&(&(&index_vk_g1, &pc_pk_g1), &pc_pk_g1), rng)
                    .unwrap();
            let t_dlog_acc_g2_valid =
                TDLogAccumulator::random_item(&(&(&index_vk_g2, &pc_pk_g2), &pc_pk_g2), rng)
                    .unwrap();
            let dual_t_dlog_acc = DualAccumulatorItem {
                native: vec![t_dlog_acc_g2_valid],
                non_native: vec![t_dlog_acc_g1_invalid],
            };

            let t_dlog_polys = DualTDLogAccumulator::expand_item(
                &(
                    &(&(&index_vk_g2, &pc_pk_g2), &pc_pk_g2),
                    &(&(&index_vk_g1, &pc_pk_g1), &pc_pk_g1),
                ),
                &dual_t_dlog_acc,
            )
            .unwrap();

            let t_poly_g1 = &t_dlog_polys[0].0;
            let bullet_poly_g1 = &t_dlog_polys[0].1;

            let proof = TDLogAccMarlin::<G1, G2, FS, D>::prove(
                &index_pk_g1,
                &pc_pk_g1,
                circ_g1,
                &dual_t_dlog_acc,
                &t_poly_g1,
                &bullet_poly_g1,
                zk,
                if zk { Some(rng) } else { None },
            )
            .unwrap();

            assert!(TDLogAccMarlin::<G1, G2, FS, D>::succinct_verify(
                &pc_vk_g1,
                &index_vk_g1,
                &[c, d],
                &dual_t_dlog_acc,
                &proof
            )
            .is_err());

            /*
            Generate a dual inner-sumcheck accumulator which is invalid in its G2 part and
            check that the succinct verification of the proof succeeds (the G2 part of the
            accumulator is merely forwarded).
             */
            let t_dlog_acc_g1_valid =
                TDLogAccumulator::random_item(&(&(&index_vk_g1, &pc_pk_g1), &pc_pk_g1), rng)
                    .unwrap();
            let t_dlog_acc_g2_invalid =
                TDLogAccumulator::invalid_item(&(&(&index_vk_g2, &pc_pk_g2), &pc_pk_g2), rng)
                    .unwrap();
            let dual_t_dlog_acc = DualAccumulatorItem {
                native: vec![t_dlog_acc_g2_invalid],
                non_native: vec![t_dlog_acc_g1_valid],
            };

            let t_dlog_polys = DualTDLogAccumulator::expand_item(
                &(
                    &(&(&index_vk_g2, &pc_pk_g2), &pc_pk_g2),
                    &(&(&index_vk_g1, &pc_pk_g1), &pc_pk_g1),
                ),
                &dual_t_dlog_acc,
            )
            .unwrap();

            let t_poly_g1 = &t_dlog_polys[0].0;
            let bullet_poly_g1 = &t_dlog_polys[0].1;

            let proof = TDLogAccMarlin::<G1, G2, FS, D>::prove(
                &index_pk_g1,
                &pc_pk_g1,
                circ_g1,
                &dual_t_dlog_acc,
                &t_poly_g1,
                &bullet_poly_g1,
                zk,
                if zk { Some(rng) } else { None },
            )
            .unwrap();

            assert!(TDLogAccMarlin::<G1, G2, FS, D>::succinct_verify(
                &pc_vk_g1,
                &index_vk_g1,
                &[c, d],
                &dual_t_dlog_acc,
                &proof
            )
            .is_ok());
        }
    }

    #[cfg(feature = "circuit-friendly")]
    mod poseidon_fs {
        use super::*;
        use algebra::curves::tweedle::dee::DeeJacobian;
        use algebra::curves::tweedle::dum::DumJacobian;
        use blake2::Blake2s;
        use fiat_shamir::poseidon::TweedleFrPoseidonFSRng;

        #[test]
        fn prove_and_verify() {
            let num_constraints = 25;
            let num_variables = 25;

            test_circuit::<DumJacobian, DeeJacobian, TweedleFrPoseidonFSRng, Blake2s>(
                25,
                num_constraints,
                num_variables,
                false,
            );
            println!("Marlin No ZK passed");

            test_circuit::<DumJacobian, DeeJacobian, TweedleFrPoseidonFSRng, Blake2s>(
                25,
                num_constraints,
                num_variables,
                true,
            );
            println!("Marlin ZK passed");
        }
    }

    #[cfg(not(feature = "circuit-friendly"))]
    mod chachafs {
        use super::*;
        use algebra::curves::tweedle::dee::DeeJacobian;
        use algebra::curves::tweedle::dum::DumJacobian;
        use blake2::Blake2s;
        use fiat_shamir::chacha20::FiatShamirChaChaRng;

        #[test]
        fn prove_and_verify() {
            let num_constraints = 25;
            let num_variables = 25;

            test_circuit::<DumJacobian, DeeJacobian, FiatShamirChaChaRng<Blake2s>, Blake2s>(
                25,
                num_constraints,
                num_variables,
                false,
            );
            println!("Marlin No ZK passed");

            test_circuit::<DumJacobian, DeeJacobian, FiatShamirChaChaRng<Blake2s>, Blake2s>(
                25,
                num_constraints,
                num_variables,
                true,
            );
            println!("Marlin ZK passed");
        }
    }
}
