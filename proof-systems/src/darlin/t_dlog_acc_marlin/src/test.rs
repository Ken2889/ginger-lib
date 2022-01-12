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
    use crate::{DualSumcheckItem, Marlin, SumcheckItem, IOP, PC};

    use crate::error::Error as MarlinError;
    use crate::iop::Error as IOPError;
    use algebra::{
        curves::tweedle::dee::DeeJacobian, curves::tweedle::dum::DumJacobian,
        serialize::test_canonical_serialize_deserialize, Curve, GroupVec, SemanticallyValid,
        UniformRand,
    };
    use blake2::Blake2s;
    use digest::Digest;
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

    fn test_circuit<G1: Curve, G2: Curve, D: Digest + 'static>(
        num_samples: usize,
        num_constraints: usize,
        num_variables: usize,
        zk: bool,
    ) {
        let rng = &mut thread_rng();

        let universal_srs =
            <PC<G1, D> as PolynomialCommitment<G1>>::setup(num_constraints - 1).unwrap();
        let (pc_pk, pc_vk) = universal_srs.trim((num_constraints - 1) / 2).unwrap();
        assert_eq!(PCCommitterKey::get_hash(&pc_pk), universal_srs.get_hash());
        assert_eq!(PCVerifierKey::get_hash(&pc_vk), universal_srs.get_hash());

        // Fake parameters for opening proof fail test
        let mut universal_srs_fake = <PC<G1, D> as PolynomialCommitment<G1>>::setup_from_seed(
            num_constraints - 1,
            b"FAKE PROTOCOL",
        )
        .unwrap();

        universal_srs_fake.copy_params(&universal_srs);
        let (pc_pk_fake, _) = universal_srs_fake.trim((num_constraints - 1) / 2).unwrap();

        for _ in 0..num_samples {
            let a = G1::ScalarField::rand(rng);
            let b = G1::ScalarField::rand(rng);
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
                Marlin::<G1, G2, D>::circuit_specific_setup(&pc_pk, circ).unwrap();

            assert!(index_pk.is_valid());
            assert!(index_vk.is_valid());

            println!("Called index");

            test_canonical_serialize_deserialize(true, &index_pk);
            test_canonical_serialize_deserialize(true, &index_vk);

            let mut previous_inner_sumcheck_acc = DualSumcheckItem {
                0: SumcheckItem {
                    zeta: G2::ScalarField::rand(rng),
                    eta: G2::ScalarField::rand(rng),
                    c: GroupVec::new(vec![G2::rand(rng)]),
                },
                1: SumcheckItem {
                    zeta: G1::ScalarField::rand(rng),
                    eta: G1::ScalarField::rand(rng),
                    c: GroupVec::new(vec![G1::rand(rng)]),
                },
            };
            let prover_init_state =
                IOP::prover_init(&index_pk.index_vk.index, circ, &previous_inner_sumcheck_acc)
                    .unwrap();
            let (acc_oracles, _) = IOP::prover_compute_acc_polys(prover_init_state).unwrap();
            let t_prime_poly = acc_oracles.t_prime;
            let (t_prime_poly_comm, _) =
                <PC<G1, D> as PolynomialCommitment<G1>>::commit(&pc_pk, &t_prime_poly, false, None)
                    .unwrap();
            previous_inner_sumcheck_acc.1.c = t_prime_poly_comm;

            let proof = Marlin::<G1, G2, D>::prove(
                &index_pk,
                &pc_pk,
                circ,
                &previous_inner_sumcheck_acc,
                zk,
                if zk { Some(rng) } else { None },
            );

            assert!(proof.is_ok());

            let (proof, new_inner_sumcheck_acc) = proof.unwrap();

            assert!(proof.is_valid());

            println!("Called prover");

            test_canonical_serialize_deserialize(true, &proof);

            // Success verification
            assert!(Marlin::<G1, G2, D>::verify(
                &index_vk,
                &pc_vk,
                &[c, d],
                &previous_inner_sumcheck_acc,
                &new_inner_sumcheck_acc,
                &proof
            )
            .unwrap());

            // Fail verification
            assert!(!Marlin::<G1, G2, D>::verify(
                &index_vk,
                &pc_vk,
                &[a, a],
                &previous_inner_sumcheck_acc,
                &new_inner_sumcheck_acc,
                &proof
            )
            .unwrap());

            // Use a bigger vk derived from the same universal params and check verification is successful
            let (_, pc_vk) = universal_srs.trim(num_constraints - 1).unwrap();
            assert_eq!(PCVerifierKey::get_hash(&pc_vk), universal_srs.get_hash());
            assert!(Marlin::<G1, G2, D>::verify(
                &index_vk,
                &pc_vk,
                &[c, d],
                &previous_inner_sumcheck_acc,
                &new_inner_sumcheck_acc,
                &proof
            )
            .unwrap());

            // Use a bigger vk derived from other universal params and check verification fails (absorbed hash won't be the same)
            let universal_srs =
                <PC<G1, D> as PolynomialCommitment<G1>>::setup((num_constraints - 1) * 2).unwrap();
            let (_, pc_vk) = universal_srs.trim(num_constraints - 1).unwrap();
            assert_ne!(PCVerifierKey::get_hash(&pc_pk), universal_srs.get_hash());
            assert!(!Marlin::<G1, G2, D>::verify(
                &index_vk,
                &pc_vk,
                &[c, d],
                &previous_inner_sumcheck_acc,
                &new_inner_sumcheck_acc,
                &proof
            )
            .unwrap());

            // Use a vk of the same size of the original one, but derived from bigger universal params
            // and check that verification fails (absorbed hash won't be the same)
            let universal_srs =
                <PC<G1, D> as PolynomialCommitment<G1>>::setup((num_constraints - 1) * 2).unwrap();
            let (_, pc_vk) = universal_srs.trim((num_constraints - 1) / 4).unwrap();
            assert_ne!(PCVerifierKey::get_hash(&pc_pk), universal_srs.get_hash());
            assert!(!Marlin::<G1, G2, D>::verify(
                &index_vk,
                &pc_vk,
                &[c, d],
                &previous_inner_sumcheck_acc,
                &new_inner_sumcheck_acc,
                &proof
            )
            .unwrap());

            // Fake indexes to pass the IOP part
            let (index_pk_fake, index_vk_fake) =
                Marlin::<G1, G2, D>::circuit_specific_setup(&pc_pk, circ).unwrap();

            let (proof_fake, new_inner_sumcheck_acc) = Marlin::<G1, G2, D>::prove(
                &index_pk_fake,
                &pc_pk_fake,
                circ,
                &previous_inner_sumcheck_acc,
                zk,
                if zk { Some(rng) } else { None },
            )
            .unwrap();

            // Fail verification using fake proof at the level of opening proof
            println!("\nShould not verify");
            assert!(!Marlin::<G1, G2, D>::verify(
                &index_vk_fake,
                &pc_vk,
                &[c, d],
                &previous_inner_sumcheck_acc,
                &new_inner_sumcheck_acc,
                &proof_fake
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
                Marlin::<G1, G2, D>::circuit_specific_setup(&pc_pk, circ).unwrap();

            assert!(index_pk.is_valid());
            assert!(index_vk.is_valid());

            println!("Called index");

            let proof = Marlin::<G1, G2, D>::prove(
                &index_pk,
                &pc_pk,
                circ,
                &previous_inner_sumcheck_acc,
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

        // test_circuit::<DumJacobian, DeeJacobian, MultiPC>(25, num_constraints, num_variables, true);
        // println!("Marlin ZK passed");
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
