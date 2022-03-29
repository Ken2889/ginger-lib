use algebra::Field;
use r1cs_core::{ConstraintSynthesizer, ConstraintSystemAbstract, SynthesisError};

/// A simple test circuit for the language {(c,d): (c,d)=a*(b,b^2), a,b from F}
/// by allocating `num_variables` dummy witnesses and repeating `num_constraints`
/// often the same quadratic constraints a*b=c and b*c=d.
// TODO: replace this example by a more representative (high-rank A,B,C).
#[derive(Copy, Clone)]
pub(crate) struct Circuit<F: Field> {
    pub(crate) a: Option<F>,
    pub(crate) b: Option<F>,
    pub(crate) c: Option<F>,
    pub(crate) d: Option<F>,
    pub(crate) num_constraints: usize,
    pub(crate) num_variables: usize,
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
    use algebra::{
        curves::tweedle::dum::DumJacobian, serialize::test_canonical_serialize_deserialize, Group,
        SemanticallyValid, UniformRand,
    };

    use blake2::Blake2s;
    use digest::Digest;
    use poly_commit::{
        ipa_pc::InnerProductArgPC, DomainExtendedPolynomialCommitment, LabeledCommitment, PCKey,
        PolynomialCommitment,
    };
    use rand::thread_rng;

    fn test_circuit<G: Group, PC: PolynomialCommitment<G>, D: Digest>(
        num_samples: usize,
        num_constraints: usize,
        num_variables: usize,
        zk: bool,
    ) {
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

            // Fail verification at the level of IOP because of wrong public inputs
            assert!(Marlin::<G, PC>::verify_iop(&pc_vk, &index_vk, &[a, a], &proof).is_err());

            // Check that IOP verification succeeds ...
            let (query_map, evaluations, mut commitments, mut fs_rng) =
                Marlin::<G, PC>::verify_iop(&pc_vk, &index_vk, &[c, d], &proof).unwrap();
            // ... then tamper with a commitment and check that opening proof fails
            let comm_last = commitments.pop().unwrap();
            commitments.push(LabeledCommitment::new(
                comm_last.label().into(),
                comm_last.commitment().double(),
            ));
            assert!(Marlin::<G, PC>::verify_opening(
                &pc_vk,
                &proof,
                commitments,
                query_map,
                evaluations,
                &mut fs_rng
            )
            .is_err());

            // Use a vk derived from bigger universal params
            // and check that verification fails (absorbed hash won't be the same)
            let (original_pc_pk, original_pc_vk) =
                PC::setup::<D>(2 * (num_constraints - 1)).unwrap();
            let pc_vk = original_pc_vk.trim((num_constraints - 1) / 4).unwrap();
            assert_ne!(pc_pk.get_hash(), original_pc_pk.get_hash());
            assert!(!Marlin::<G, PC>::verify(&index_vk, &pc_vk, &[c, d], &proof).unwrap());

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
                Marlin::<G, PC>::circuit_specific_setup::<_, D>(&pc_pk, circ).unwrap();

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
        use fiat_shamir::chacha20::FiatShamirChaChaRng;

        type MultiPCChaCha = DomainExtendedPolynomialCommitment<
            DumJacobian,
            InnerProductArgPC<DumJacobian, FiatShamirChaChaRng<Blake2s>>,
        >;

        generate_tests!(dum_blake2s, DumJacobian, MultiPCChaCha, Blake2s);
    }

    #[cfg(feature = "circuit-friendly")]
    mod poseidon_fs {
        use super::*;
        use fiat_shamir::poseidon::{TweedleFqPoseidonFSRng, TweedleFrPoseidonFSRng};

        type MultiPCPoseidon<FS> =
            DomainExtendedPolynomialCommitment<DumJacobian, InnerProductArgPC<DumJacobian, FS>>;

        generate_tests!(
            dum_tweedle_fr_poseidon_fs,
            DumJacobian,
            MultiPCPoseidon::<TweedleFrPoseidonFSRng>,
            Blake2s
        );
        generate_tests!(
            dum_tweedle_fq_poseidon_fs,
            DumJacobian,
            MultiPCPoseidon::<TweedleFqPoseidonFSRng>,
            Blake2s
        );
    }
}
