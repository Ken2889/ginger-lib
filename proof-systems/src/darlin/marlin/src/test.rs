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

    use crate::error::Error as MarlinError;
    use crate::iop::Error as IOPError;
    use algebra::{
        curves::tweedle::dum::DumJacobian, serialize::test_canonical_serialize_deserialize, EndoMulCurve,
        SemanticallyValid, UniformRand,
    };
    
    use blake2::Blake2s;
    use digest::Digest;
    use poly_commit::{
        ipa_pc::{InnerProductArgPC, Parameters as IPAParameters},
        DomainExtendedPolynomialCommitment, PCCommitterKey, PCParameters, PCVerifierKey,
        PolynomialCommitment,
    };
    use rand::thread_rng;
    use std::ops::MulAssign;


    trait TestUtils {
        /// Copy other instance params into this
        fn copy_params(&mut self, other: &Self);
    }

    impl<G: EndoMulCurve> TestUtils for IPAParameters<G> {
        fn copy_params(&mut self, other: &Self) {
            self.s = other.s.clone();
            self.h = other.h.clone();
            self.hash = other.hash.clone();
        }
    }

    fn test_circuit<G: EndoMulCurve, PC: PolynomialCommitment<G>, D: Digest>(
        num_samples: usize,
        num_constraints: usize,
        num_variables: usize,
        zk: bool,
    ) where
        PC::Parameters: TestUtils,
    {
        let rng = &mut thread_rng();

        let universal_srs = PC::setup::<D>(num_constraints - 1).unwrap();
        let (pc_pk, pc_vk) = universal_srs.trim((num_constraints - 1) / 2).unwrap();
        assert_eq!(pc_pk.get_hash(), universal_srs.get_hash());
        assert_eq!(pc_vk.get_hash(), universal_srs.get_hash());

        // Fake parameters for opening proof fail test
        let mut universal_srs_fake =
            PC::setup_from_seed::<D>(num_constraints - 1, b"FAKE PROTOCOL").unwrap();

        universal_srs_fake.copy_params(&universal_srs);
        let (pc_pk_fake, _) = universal_srs_fake.trim((num_constraints - 1) / 2).unwrap();

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
                Marlin::<G, PC>::circuit_specific_setup(&pc_pk, circ).unwrap();

            assert!(index_pk.is_valid());
            assert!(index_vk.is_valid());

            println!("Called index");

            test_canonical_serialize_deserialize(true, &index_pk);
            test_canonical_serialize_deserialize(true, &index_vk);

            let proof = Marlin::<G, PC>::prove(
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
            assert!(Marlin::<G, PC>::verify(&index_vk, &pc_vk, &[c, d], &proof).unwrap());

            // Fail verification
            assert!(!Marlin::<G, PC>::verify(&index_vk, &pc_vk, &[a, a], &proof).unwrap());

            // Use a bigger vk derived from the same universal params and check verification is successful
            let (_, pc_vk) = universal_srs.trim(num_constraints - 1).unwrap();
            assert_eq!(pc_vk.get_hash(), universal_srs.get_hash());
            assert!(Marlin::<G, PC>::verify(&index_vk, &pc_vk, &[c, d], &proof).unwrap());

            // Use a bigger vk derived from other universal params and check verification fails (absorbed hash won't be the same)
            let universal_srs = PC::setup::<D>((num_constraints - 1) * 2).unwrap();
            let (_, pc_vk) = universal_srs.trim(num_constraints - 1).unwrap();
            assert_ne!(pc_pk.get_hash(), universal_srs.get_hash());
            assert!(!Marlin::<G, PC>::verify(&index_vk, &pc_vk, &[c, d], &proof).unwrap());

            // Use a vk of the same size of the original one, but derived from bigger universal params
            // and check that verification fails (absorbed hash won't be the same)
            let universal_srs = PC::setup::<D>((num_constraints - 1) * 2).unwrap();
            let (_, pc_vk) = universal_srs.trim((num_constraints - 1) / 4).unwrap();
            assert_ne!(pc_pk.get_hash(), universal_srs.get_hash());
            assert!(!Marlin::<G, PC>::verify(&index_vk, &pc_vk, &[c, d], &proof).unwrap());

            // Fake indexes to pass the IOP part
            let (index_pk_fake, index_vk_fake) =
                Marlin::<G, PC>::circuit_specific_setup(&pc_pk_fake, circ).unwrap();

            let proof_fake = Marlin::<G, PC>::prove(
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
                !Marlin::<G, PC>::verify(&index_vk_fake, &pc_vk, &[c, d], &proof_fake).unwrap()
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
                Marlin::<G, PC>::circuit_specific_setup(&pc_pk, circ).unwrap();

            assert!(index_pk.is_valid());
            assert!(index_vk.is_valid());

            println!("Called index");

            let proof = Marlin::<G, PC>::prove(
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

    macro_rules! generate_tests {
        ($pc_inst_name: ident, $curve: ty, $pc_inst: ty, $digest: ty) => {
            paste::item! {
                #[test]
                fn [<prove_and_verify_with_tall_matrix_big_ $pc_inst_name>]() {
                    let num_constraints = 100;
                    let num_variables = 25;
            
                    test_circuit::<$curve, $pc_inst, $digest>(25, num_constraints, num_variables, false);
                    test_circuit::<$curve, $pc_inst, $digest>(25, num_constraints, num_variables, true);
                }
            
                #[test]
                fn [<prove_and_verify_with_tall_matrix_small_ $pc_inst_name>]() {
                    let num_constraints = 26;
                    let num_variables = 25;
                    test_circuit::<$curve, $pc_inst, $digest>(25, num_constraints, num_variables, false);
                    test_circuit::<$curve, $pc_inst, $digest>(25, num_constraints, num_variables, true);
                }
            
                #[test]
                fn [<prove_and_verify_with_squat_matrix_big_ $pc_inst_name>]() {
                    let num_constraints = 25;
                    let num_variables = 100;
            
                    test_circuit::<$curve, $pc_inst, $digest>(25, num_constraints, num_variables, false);
                    test_circuit::<$curve, $pc_inst, $digest>(25, num_constraints, num_variables, true);
                }
            
                #[test]
                fn [<prove_and_verify_with_squat_matrix_small_ $pc_inst_name>]() {
                    let num_constraints = 25;
                    let num_variables = 26;
            
                    test_circuit::<$curve, $pc_inst, $digest>(25, num_constraints, num_variables, false);
                    test_circuit::<$curve, $pc_inst, $digest>(25, num_constraints, num_variables, true);
                }
            
                #[test]
                fn [<prove_and_verify_with_square_matrix_ $pc_inst_name>]() {
                    let num_constraints = 25;
                    let num_variables = 25;
            
                    test_circuit::<$curve, $pc_inst, $digest>(25, num_constraints, num_variables, false);
                    test_circuit::<$curve, $pc_inst, $digest>(25, num_constraints, num_variables, true);
                }
            
                #[test]
                // See https://github.com/HorizenLabs/marlin/issues/3 for the rationale behind this test
                fn [<prove_and_verify_with_trivial_index_polynomials_ $pc_inst_name>]() {
                    let num_constraints = 1 << 6;
                    let num_variables = 1 << 4;
            
                    test_circuit::<$curve, $pc_inst, $digest>(25, num_constraints, num_variables, false);
                    test_circuit::<$curve, $pc_inst, $digest>(25, num_constraints, num_variables, true);
                }
            }
        };
    }

    #[cfg(not(feature = "circuit-friendly"))]
    mod chacha_fs {
        use super::*;
        use poly_commit::fiat_shamir::chacha20::FiatShamirChaChaRng;

        type MultiPCChaCha =
        DomainExtendedPolynomialCommitment<DumJacobian, InnerProductArgPC<DumJacobian, FiatShamirChaChaRng<Blake2s>>>;

        generate_tests!(dum_blake2s, DumJacobian, MultiPCChaCha, Blake2s);
    }

    #[cfg(feature = "circuit-friendly")]
    mod poseidon_fs {
        use super::*;
        use primitives::TweedleFrPoseidonSponge;

        type MultiPCPoseidon =
            DomainExtendedPolynomialCommitment<DumJacobian, InnerProductArgPC<DumJacobian, TweedleFrPoseidonSponge>>;

        generate_tests!(dum_poseidon, DumJacobian, MultiPCPoseidon, Blake2s);
    }
}
