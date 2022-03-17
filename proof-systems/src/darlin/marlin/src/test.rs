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
    use std::ops::MulAssign;

    use crate::error::Error as MarlinError;
    use crate::iop::Error as IOPError;
    use algebra::curves::tweedle::dum::DumJacobian;
    use algebra::{
        serialize::test_canonical_serialize_deserialize, Group, SemanticallyValid, UniformRand,
    };
    use blake2::Blake2s;
    use digest::Digest;
    use poly_commit::{
        ipa_pc::InnerProductArgPC, DomainExtendedPolynomialCommitment, PolynomialCommitment,
    };
    use rand::thread_rng;

    type MultiPC =
        DomainExtendedPolynomialCommitment<DumJacobian, InnerProductArgPC<DumJacobian, Blake2s>>;

    fn test_circuit<G: Group, PC: PolynomialCommitment<G>, D: Digest>(
        num_samples: usize,
        num_constraints: usize,
        num_variables: usize,
        zk: bool,
    ) {
        let rng = &mut thread_rng();

        let (pc_pk, pc_vk) = PC::setup((num_constraints - 1) / 2).unwrap();

        // Fake parameters for opening proof fail test
        let (pc_pk_fake, _) =
            PC::setup_from_seed((num_constraints - 1) / 2, b"FAKE PROTOCOL").unwrap();

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
                Marlin::<G, PC, D>::circuit_specific_setup(&pc_pk, circ).unwrap();

            assert!(index_pk.is_valid());
            assert!(index_vk.is_valid());

            println!("Called index");

            test_canonical_serialize_deserialize(true, &index_pk);
            test_canonical_serialize_deserialize(true, &index_vk);

            let proof = Marlin::<G, PC, D>::prove(
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
            assert!(Marlin::<G, PC, D>::verify(&index_vk, &pc_vk, &[c, d], &proof).unwrap());

            // Fail verification
            assert!(!Marlin::<G, PC, D>::verify(&index_vk, &pc_vk, &[a, a], &proof).unwrap());

            // Fake indexes to pass the IOP part
            let (index_pk_fake, index_vk_fake) =
                Marlin::<G, PC, D>::circuit_specific_setup(&pc_pk_fake, circ).unwrap();

            let proof_fake = Marlin::<G, PC, D>::prove(
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
                !Marlin::<G, PC, D>::verify(&index_vk_fake, &pc_vk, &[c, d], &proof_fake).unwrap()
            );

            // Check correct error assertion for the case when
            // witness assignment doesn't satisfy the circuit
            let c = G::ScalarField::rand(rng);
            let d = G::ScalarField::rand(rng);

            let circ = Circuit {
                a: Some(a),
                b: Some(b),
                c: Some(c),
                d: Some(d),
                num_constraints,
                num_variables,
            };
            let (index_pk, index_vk) =
                Marlin::<G, PC, D>::circuit_specific_setup(&pc_pk, circ).unwrap();

            assert!(index_pk.is_valid());
            assert!(index_vk.is_valid());

            println!("Called index");

            let proof = Marlin::<G, PC, D>::prove(
                &index_pk,
                &pc_pk,
                circ,
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

        test_circuit::<DumJacobian, MultiPC, Blake2s>(25, num_constraints, num_variables, false);
        println!("Marlin No ZK passed");

        test_circuit::<DumJacobian, MultiPC, Blake2s>(25, num_constraints, num_variables, true);
        println!("Marlin ZK passed");
    }

    #[test]
    fn prove_and_verify_with_tall_matrix_small() {
        let num_constraints = 26;
        let num_variables = 25;

        test_circuit::<DumJacobian, MultiPC, Blake2s>(25, num_constraints, num_variables, false);
        println!("Marlin No ZK passed");

        test_circuit::<DumJacobian, MultiPC, Blake2s>(25, num_constraints, num_variables, true);
        println!("Marlin ZK passed");
    }

    #[test]
    fn prove_and_verify_with_squat_matrix_big() {
        let num_constraints = 25;
        let num_variables = 100;

        test_circuit::<DumJacobian, MultiPC, Blake2s>(25, num_constraints, num_variables, false);
        println!("Marlin No ZK passed");

        test_circuit::<DumJacobian, MultiPC, Blake2s>(25, num_constraints, num_variables, true);
        println!("Marlin ZK passed");
    }

    #[test]
    fn prove_and_verify_with_squat_matrix_small() {
        let num_constraints = 25;
        let num_variables = 26;

        test_circuit::<DumJacobian, MultiPC, Blake2s>(25, num_constraints, num_variables, false);
        println!("Marlin No ZK passed");

        test_circuit::<DumJacobian, MultiPC, Blake2s>(25, num_constraints, num_variables, true);
        println!("Marlin ZK passed");
    }

    #[test]
    fn prove_and_verify_with_square_matrix() {
        let num_constraints = 25;
        let num_variables = 25;

        test_circuit::<DumJacobian, MultiPC, Blake2s>(25, num_constraints, num_variables, false);
        println!("Marlin No ZK passed");

        test_circuit::<DumJacobian, MultiPC, Blake2s>(25, num_constraints, num_variables, true);
        println!("Marlin ZK passed");
    }

    #[test]
    // See https://github.com/HorizenLabs/marlin/issues/3 for the rationale behind this test
    fn prove_and_verify_with_trivial_index_polynomials() {
        let num_constraints = 1 << 6;
        let num_variables = 1 << 4;

        test_circuit::<DumJacobian, MultiPC, Blake2s>(25, num_constraints, num_variables, false);
        println!("Marlin No ZK passed");

        test_circuit::<DumJacobian, MultiPC, Blake2s>(25, num_constraints, num_variables, true);
        println!("Marlin ZK passed");
    }
}
