use algebra::Field;
use r1cs_core::{ConstraintSynthesizer, ConstraintSystemAbstract, SynthesisError};

/// A simple test circuit for the language {(c,d): (c,d)=a*(b,b^2), a,b from F}
/// by allocating `num_variables` dummy witnesses and repeating `num_constraints`
/// often the same quadratic constraints a*b=c and b*c=d.
// TODO: replace this example by a more representative (high-rank A,B,C).
#[derive(Copy, Clone)]
struct Circuit<F: Field> {
    a: Option<F>,
    b: Option<F>,
    c: Option<F>,
    d: Option<F>,
    num_constraints: usize,
    num_variables: usize,
}

impl<ConstraintF: Field> ConstraintSynthesizer<ConstraintF> for Circuit<ConstraintF> {
    fn generate_constraints<CS: ConstraintSystemAbstract<ConstraintF>>(
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

mod marlin {
    use super::*;
    use crate::Marlin;

    use crate::ahp::Error as AHPError;
    use crate::error::Error as MarlinError;
    use algebra::{
        curves::tweedle::dum::Affine, fields::tweedle::fq::Fq,
        serialize::test_canonical_serialize_deserialize, PrimeField, SemanticallyValid,
    };
    use blake2::Blake2s;
    use digest::Digest;
    use poly_commit::{
        ipa_pc::InnerProductArgPC, PCCommitterKey, PCUniversalParams, PCVerifierKey,
        PolynomialCommitment,
    };
    use rand::thread_rng;

    type MultiPC = InnerProductArgPC<Affine, Blake2s>;

    fn test_circuit<F: PrimeField, PC: PolynomialCommitment<F>, D: Digest>(
        num_samples: usize,
        num_constraints: usize,
        num_variables: usize,
        zk: bool,
    ) {
        let rng = &mut thread_rng();

        let universal_srs = PC::setup(num_constraints - 1).unwrap();
        let (pc_pk, pc_vk) = PC::trim(&universal_srs, (num_constraints - 1) / 2).unwrap();
        assert_eq!(pc_pk.get_hash(), universal_srs.get_hash());
        assert_eq!(pc_vk.get_hash(), universal_srs.get_hash());

        // Fake parameters for opening proof fail test
        let mut universal_srs_fake =
            PC::setup_from_seed(num_constraints - 1, b"FAKE PROTOCOL").unwrap();
        universal_srs_fake.copy_params(&universal_srs);
        let (pc_pk_fake, _) = PC::trim(&universal_srs_fake, (num_constraints - 1) / 2).unwrap();

        for _ in 0..num_samples {
            let a = F::rand(rng);
            let b = F::rand(rng);
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
            let (index_pk, index_vk) = Marlin::<F, PC, D>::index(&pc_pk, circ).unwrap();

            assert!(index_pk.is_valid());
            assert!(index_vk.is_valid());

            println!("Called index");

            test_canonical_serialize_deserialize(true, &index_pk);
            test_canonical_serialize_deserialize(true, &index_vk);

            let proof = Marlin::<F, PC, D>::prove(
                &index_pk,
                &pc_pk,
                circ,
                zk,
                if zk { Some(rng) } else { None },
            );

            assert!(proof.is_ok());

            let proof = proof.unwrap();

            assert!(proof.is_valid());

            println!("Called prover");

            test_canonical_serialize_deserialize(true, &proof);

            // Success verification
            assert!(Marlin::<F, PC, D>::verify(&index_vk, &pc_vk, &[c, d], &proof).unwrap());

            // Fail verification
            assert!(!Marlin::<F, PC, D>::verify(&index_vk, &pc_vk, &[a, a], &proof).unwrap());

            // Use a bigger vk derived from the same universal params and check verification is successful
            let (_, pc_vk) = PC::trim(&universal_srs, num_constraints - 1).unwrap();
            assert_eq!(pc_vk.get_hash(), universal_srs.get_hash());
            assert!(Marlin::<F, PC, D>::verify(&index_vk, &pc_vk, &[c, d], &proof).unwrap());

            // Use a bigger vk derived from other universal params and check verification fails (absorbed hash won't be the same)
            let universal_srs = PC::setup((num_constraints - 1) * 2).unwrap();
            let (_, pc_vk) = PC::trim(&universal_srs, num_constraints - 1).unwrap();
            assert_ne!(pc_pk.get_hash(), universal_srs.get_hash());
            assert!(!Marlin::<F, PC, D>::verify(&index_vk, &pc_vk, &[c, d], &proof).unwrap());

            // Use a vk of the same size of the original one, but derived from bigger universal params
            // and check that verification fails (absorbed hash won't be the same)
            let universal_srs = PC::setup((num_constraints - 1) * 2).unwrap();
            let (_, pc_vk) = PC::trim(&universal_srs, (num_constraints - 1) / 4).unwrap();
            assert_ne!(pc_pk.get_hash(), universal_srs.get_hash());
            assert!(!Marlin::<F, PC, D>::verify(&index_vk, &pc_vk, &[c, d], &proof).unwrap());

            // Fake indexes to pass the AHP part
            let (index_pk_fake, index_vk_fake) =
                Marlin::<F, PC, D>::index(&pc_pk_fake, circ).unwrap();

            let proof_fake = Marlin::<F, PC, D>::prove(
                &index_pk_fake,
                &pc_pk_fake,
                circ,
                zk,
                if zk { Some(rng) } else { None },
            )
            .unwrap();

            // Fail verification using fake proof at the level of opening proof
            println!("\nShould not verify");
            assert!(
                !Marlin::<F, PC, D>::verify(&index_vk_fake, &pc_vk, &[c, d], &proof_fake).unwrap()
            );

            // Check correct error assertion for the case when
            // witness assignment doesn't satisfy the circuit
            let c = F::rand(rng);
            let d = F::rand(rng);

            let circ = Circuit {
                a: Some(a),
                b: Some(b),
                c: Some(c),
                d: Some(d),
                num_constraints,
                num_variables,
            };
            let (index_pk, index_vk) = Marlin::<F, PC, D>::index(&pc_pk, circ).unwrap();

            assert!(index_pk.is_valid());
            assert!(index_vk.is_valid());

            println!("Called index");

            let proof = Marlin::<F, PC, D>::prove(
                &index_pk,
                &pc_pk,
                circ,
                zk,
                if zk { Some(rng) } else { None },
            );

            assert!(proof.is_err());

            assert!(match proof.unwrap_err() {
                MarlinError::AHPError(AHPError::InvalidCoboundaryPolynomial) => true,
                _ => false,
            });
        }
    }

    #[test]
    fn prove_and_verify_with_tall_matrix_big() {
        let num_constraints = 100;
        let num_variables = 25;

        test_circuit::<Fq, MultiPC, Blake2s>(25, num_constraints, num_variables, false);
        println!("Marlin No ZK passed");

        test_circuit::<Fq, MultiPC, Blake2s>(25, num_constraints, num_variables, true);
        println!("Marlin ZK passed");
    }

    #[test]
    fn prove_and_verify_with_tall_matrix_small() {
        let num_constraints = 26;
        let num_variables = 25;

        test_circuit::<Fq, MultiPC, Blake2s>(25, num_constraints, num_variables, false);
        println!("Marlin No ZK passed");

        test_circuit::<Fq, MultiPC, Blake2s>(25, num_constraints, num_variables, true);
        println!("Marlin ZK passed");
    }

    #[test]
    fn prove_and_verify_with_squat_matrix_big() {
        let num_constraints = 25;
        let num_variables = 100;

        test_circuit::<Fq, MultiPC, Blake2s>(25, num_constraints, num_variables, false);
        println!("Marlin No ZK passed");

        test_circuit::<Fq, MultiPC, Blake2s>(25, num_constraints, num_variables, true);
        println!("Marlin ZK passed");
    }

    #[test]
    fn prove_and_verify_with_squat_matrix_small() {
        let num_constraints = 25;
        let num_variables = 26;

        test_circuit::<Fq, MultiPC, Blake2s>(25, num_constraints, num_variables, false);
        println!("Marlin No ZK passed");

        test_circuit::<Fq, MultiPC, Blake2s>(25, num_constraints, num_variables, true);
        println!("Marlin ZK passed");
    }

    #[test]
    fn prove_and_verify_with_square_matrix() {
        let num_constraints = 25;
        let num_variables = 25;

        test_circuit::<Fq, MultiPC, Blake2s>(25, num_constraints, num_variables, false);
        println!("Marlin No ZK passed");

        test_circuit::<Fq, MultiPC, Blake2s>(25, num_constraints, num_variables, true);
        println!("Marlin ZK passed");
    }

    #[test]
    // See https://github.com/HorizenLabs/marlin/issues/3 for the rationale behind this test
    fn prove_and_verify_with_trivial_index_polynomials() {
        let num_constraints = 1 << 6;
        let num_variables = 1 << 4;

        test_circuit::<Fq, MultiPC, Blake2s>(25, num_constraints, num_variables, false);
        println!("Marlin No ZK passed");

        test_circuit::<Fq, MultiPC, Blake2s>(25, num_constraints, num_variables, true);
        println!("Marlin ZK passed");
    }
}
