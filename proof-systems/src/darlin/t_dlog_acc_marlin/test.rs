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

    use crate::darlin::accumulators::dlog::DualDLogItem;
    use crate::darlin::data_structures::FinalDarlinDeferredData;
    use crate::darlin::t_dlog_acc_marlin::data_structures::{DualSumcheckItem, PC};
    use crate::darlin::t_dlog_acc_marlin::Marlin;
    use algebra::{
        curves::tweedle::dee::DeeJacobian, curves::tweedle::dum::DumJacobian,
        serialize::test_canonical_serialize_deserialize, Curve, Group, SemanticallyValid,
        ToConstraintField, UniformRand,
    };
    use blake2::Blake2s;
    use digest::Digest;
    use marlin::iop::Error as IOPError;
    use marlin::Error as MarlinError;
    use poly_commit::{
        ipa_pc::Parameters as IPAParameters, PCCommitterKey, PCParameters, PCVerifierKey,
        PolynomialCommitment,
    };
    use rand::thread_rng;
    use std::ops::MulAssign;

    trait TestUtils {
        /// Copy other instance params into this
        fn copy_params(&mut self, other: &Self);
    }

    impl<G: Curve> TestUtils for IPAParameters<G> {
        fn copy_params(&mut self, other: &Self) {
            self.s = other.s.clone();
            self.h = other.h.clone();
            self.hash = other.hash.clone();
        }
    }

    fn test_circuit<G1, G2, D>(
        num_samples: usize,
        num_constraints: usize,
        num_variables: usize,
        zk: bool,
    ) where
        G1: Curve<BaseField = <G2 as Group>::ScalarField>
            + ToConstraintField<<G2 as Group>::ScalarField>,
        G2: Curve<BaseField = <G1 as Group>::ScalarField>
            + ToConstraintField<<G1 as Group>::ScalarField>,
        D: Digest + 'static,
    {
        let rng = &mut thread_rng();

        let universal_srs_g1 =
            <PC<G1, D> as PolynomialCommitment<G1>>::setup(num_constraints - 1).unwrap();
        let (pc_pk_g1, pc_vk_g1) = universal_srs_g1.trim((num_constraints - 1) / 2).unwrap();
        assert_eq!(
            PCCommitterKey::get_hash(&pc_pk_g1),
            universal_srs_g1.get_hash()
        );
        assert_eq!(
            PCVerifierKey::get_hash(&pc_vk_g1),
            universal_srs_g1.get_hash()
        );

        let universal_srs_g2 =
            <PC<G2, D> as PolynomialCommitment<G2>>::setup(num_constraints - 1).unwrap();
        let (pc_pk_g2, pc_vk_g2) = universal_srs_g2.trim((num_constraints - 1) / 2).unwrap();
        assert_eq!(
            PCCommitterKey::get_hash(&pc_pk_g2),
            universal_srs_g2.get_hash()
        );
        assert_eq!(
            PCVerifierKey::get_hash(&pc_vk_g2),
            universal_srs_g2.get_hash()
        );

        // Fake parameters for opening proof fail test
        let mut universal_srs_fake = <PC<G1, D> as PolynomialCommitment<G1>>::setup_from_seed(
            num_constraints - 1,
            b"FAKE PROTOCOL",
        )
        .unwrap();

        universal_srs_fake.copy_params(&universal_srs_g1);
        let (pc_pk_fake, _) = universal_srs_fake.trim((num_constraints - 1) / 2).unwrap();

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
                Marlin::<G1, G2, D>::circuit_specific_setup(&pc_pk_g1, circ_g1).unwrap();
            let (index_pk_g2, index_vk_g2) =
                Marlin::<G2, G1, D>::circuit_specific_setup(&pc_pk_g2, circ_g2).unwrap();

            assert!(index_pk_g1.is_valid());
            assert!(index_vk_g1.is_valid());
            assert!(index_pk_g2.is_valid());
            assert!(index_vk_g2.is_valid());

            println!("Called index");

            test_canonical_serialize_deserialize(true, &index_pk_g1);
            test_canonical_serialize_deserialize(true, &index_vk_g1);
            test_canonical_serialize_deserialize(true, &index_pk_g2);
            test_canonical_serialize_deserialize(true, &index_vk_g2);

            let starting_dlog_acc = DualDLogItem::generate_random(rng, &pc_pk_g1, &pc_pk_g2);
            let starting_inner_sumcheck_acc = DualSumcheckItem::<G1, G2>::generate_random::<D>(
                rng,
                &index_pk_g1.index_vk.index,
                &index_pk_g2.index_vk.index,
                &pc_pk_g1,
                &pc_pk_g2,
            );

            let (verification_g1, verification_g2) = Marlin::<G1, G2, D>::hard_verify(
                &pc_vk_g1,
                &pc_vk_g2,
                &index_vk_g1,
                &index_vk_g2,
                &starting_inner_sumcheck_acc,
                &starting_dlog_acc,
            )
            .unwrap()
            .unwrap();

            let proof = Marlin::<G2, G1, D>::prove(
                &index_pk_g2,
                &pc_pk_g2,
                circ_g2,
                &starting_inner_sumcheck_acc,
                &starting_dlog_acc,
                &verification_g2.t_acc_poly,
                &verification_g2.bullet_poly,
                zk,
                if zk { Some(rng) } else { None },
            );

            let (_, previous_inner_sumcheck_acc, previous_dlog_acc) = proof.unwrap();

            let proof = Marlin::<G1, G2, D>::prove(
                &index_pk_g1,
                &pc_pk_g1,
                circ_g1,
                &previous_inner_sumcheck_acc,
                &previous_dlog_acc,
                &verification_g1.t_acc_poly,
                &verification_g1.bullet_poly,
                zk,
                if zk { Some(rng) } else { None },
            );

            assert!(proof.is_ok());

            let (proof, new_inner_sumcheck_acc, new_dlog_acc) = proof.unwrap();

            assert!(proof.is_valid());

            println!("Called prover");

            test_canonical_serialize_deserialize(true, &proof);

            // Success verification
            assert!(Marlin::<G1, G2, D>::verify(
                &index_vk_g1,
                &index_vk_g2,
                &pc_vk_g1,
                &pc_vk_g2,
                &[c, d],
                &previous_inner_sumcheck_acc,
                &previous_dlog_acc,
                &new_inner_sumcheck_acc,
                &new_dlog_acc,
                &proof
            )
            .unwrap());

            // Fail verification
            assert!(!Marlin::<G1, G2, D>::verify(
                &index_vk_g1,
                &index_vk_g2,
                &pc_vk_g1,
                &pc_vk_g2,
                &[a, a],
                &previous_inner_sumcheck_acc,
                &previous_dlog_acc,
                &new_inner_sumcheck_acc,
                &new_dlog_acc,
                &proof
            )
            .unwrap());

            // Check correct error assertion for the case when
            // witness assignment doesn't satisfy the circuit
            let c = G1::ScalarField::rand(rng);
            let d = G1::ScalarField::rand(rng);

            let circ = Circuit {
                a: Some(a),
                b: Some(b),
                c: Some(c),
                d: Some(d),
                num_constraints,
                num_variables,
            };
            let (index_pk, index_vk) =
                Marlin::<G1, G2, D>::circuit_specific_setup(&pc_pk_g1, circ).unwrap();

            assert!(index_pk.is_valid());
            assert!(index_vk.is_valid());

            println!("Called index");

            let proof = Marlin::<G1, G2, D>::prove(
                &index_pk,
                &pc_pk_g1,
                circ,
                &previous_inner_sumcheck_acc,
                &previous_dlog_acc,
                &verification_g1.t_acc_poly,
                &verification_g1.bullet_poly,
                zk,
                if zk { Some(rng) } else { None },
            );

            assert!(proof.is_err());

            assert!(match proof.unwrap_err() {
                MarlinError::IOPError(IOPError::InvalidCoboundaryPolynomial) => true,
                _ => false,
            });
        }
    }

    #[test]
    fn prove_and_verify_with_tall_matrix_big() {
        let num_constraints = 100;
        let num_variables = 25;

        test_circuit::<DumJacobian, DeeJacobian, Blake2s>(
            25,
            num_constraints,
            num_variables,
            false,
        );
        println!("Marlin No ZK passed");

        test_circuit::<DumJacobian, DeeJacobian, Blake2s>(25, num_constraints, num_variables, true);
        println!("Marlin ZK passed");
    }

    #[test]
    fn prove_and_verify_with_tall_matrix_small() {
        let num_constraints = 26;
        let num_variables = 25;

        test_circuit::<DumJacobian, DeeJacobian, Blake2s>(
            25,
            num_constraints,
            num_variables,
            false,
        );
        println!("Marlin No ZK passed");

        test_circuit::<DumJacobian, DeeJacobian, Blake2s>(25, num_constraints, num_variables, true);
        println!("Marlin ZK passed");
    }

    #[test]
    fn prove_and_verify_with_squat_matrix_big() {
        let num_constraints = 25;
        let num_variables = 100;

        test_circuit::<DumJacobian, DeeJacobian, Blake2s>(
            25,
            num_constraints,
            num_variables,
            false,
        );
        println!("Marlin No ZK passed");

        test_circuit::<DumJacobian, DeeJacobian, Blake2s>(25, num_constraints, num_variables, true);
        println!("Marlin ZK passed");
    }

    #[test]
    fn prove_and_verify_with_squat_matrix_small() {
        let num_constraints = 25;
        let num_variables = 26;

        test_circuit::<DumJacobian, DeeJacobian, Blake2s>(
            25,
            num_constraints,
            num_variables,
            false,
        );
        println!("Marlin No ZK passed");

        test_circuit::<DumJacobian, DeeJacobian, Blake2s>(25, num_constraints, num_variables, true);
        println!("Marlin ZK passed");
    }

    #[test]
    fn prove_and_verify_with_square_matrix() {
        let num_constraints = 25;
        let num_variables = 25;

        test_circuit::<DumJacobian, DeeJacobian, Blake2s>(
            25,
            num_constraints,
            num_variables,
            false,
        );
        println!("Marlin No ZK passed");

        test_circuit::<DumJacobian, DeeJacobian, Blake2s>(25, num_constraints, num_variables, true);
        println!("Marlin ZK passed");
    }

    #[test]
    // See https://github.com/HorizenLabs/marlin/issues/3 for the rationale behind this test
    fn prove_and_verify_with_trivial_index_polynomials() {
        let num_constraints = 1 << 6;
        let num_variables = 1 << 4;

        test_circuit::<DumJacobian, DeeJacobian, Blake2s>(
            25,
            num_constraints,
            num_variables,
            false,
        );
        println!("Marlin No ZK passed");

        test_circuit::<DumJacobian, DeeJacobian, Blake2s>(25, num_constraints, num_variables, true);
        println!("Marlin ZK passed");
    }
}
