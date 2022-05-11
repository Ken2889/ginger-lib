#[cfg(test)]

mod verifier_gadget {
    use crate::constraints::data_structures::{ProofGadget, VerifierKeyGadget};
    use crate::constraints::MarlinVerifierGadget;
    use crate::test::Circuit;
    use crate::{Marlin, Proof, VerifierKey};
    use algebra::{
        test_canonical_serialize_deserialize, EndoMulCurve, SemanticallyValid, ToBits,
        ToConstraintField, UniformRand,
    };
    use digest::Digest;
    use poly_commit::constraints::PolynomialCommitmentVerifierGadget;
    use poly_commit::{LabeledCommitmentGadget, PCKey, PolynomialCommitment};
    use primitives::FieldBasedHash;
    use r1cs_core::{ConstraintSynthesizer, ConstraintSystemAbstract, SynthesisError};
    use r1cs_core::{ConstraintSystem, ConstraintSystemDebugger, SynthesisMode};
    use r1cs_crypto::FieldBasedHashGadget;
    use r1cs_std::alloc::AllocGadget;
    use r1cs_std::eq::EqGadget;
    use r1cs_std::fields::fp::FpGadget;
    use r1cs_std::fields::nonnative::nonnative_field_gadget::NonNativeFieldGadget;
    use r1cs_std::fields::FieldGadget;
    use r1cs_std::groups::{EndoMulCurveGadget, GroupGadget};
    use r1cs_std::to_field_gadget_vec::ToConstraintFieldGadget;
    use r1cs_std::Assignment;
    use rand::thread_rng;
    use std::marker::PhantomData;
    use std::ops::MulAssign;

    struct TestRecursiveCircuit<'a, G, GDual, GG, PC, PCG, D, H, HG>
    where
        G: EndoMulCurve,
        GDual: EndoMulCurve<ScalarField = G::BaseField>,
        GG: EndoMulCurveGadget<G, G::BaseField>
            + ToConstraintFieldGadget<G::BaseField, FieldGadget = FpGadget<G::BaseField>>,
        PC: PolynomialCommitment<G>,
        PCG: PolynomialCommitmentVerifierGadget<G::BaseField, G, PC>,
        D: Digest,
        H: FieldBasedHash<Data = G::BaseField>,
        HG: FieldBasedHashGadget<H, G::BaseField>,
    {
        index_vk: &'a VerifierKey<G, PC>,
        pc_vk: &'a PC::VerifierKey,
        proof: &'a Proof<G, PC>,
        public_inputs: &'a [G::ScalarField],
        _g_dual: PhantomData<GDual>,
        _endomul_curve_gadget: PhantomData<GG>,
        _polynomial_commitment_verifier_gadget: PhantomData<PCG>,
        _digest: PhantomData<D>,
        _hash: PhantomData<H>,
        _hash_gadget: PhantomData<HG>,
    }

    impl<'a, G, GDual, GG, PC, PCG, D, H, HG> TestRecursiveCircuit<'a, G, GDual, GG, PC, PCG, D, H, HG>
    where
        G: EndoMulCurve,
        GDual: EndoMulCurve<ScalarField = G::BaseField>,
        GG: EndoMulCurveGadget<G, G::BaseField>
            + ToConstraintFieldGadget<G::BaseField, FieldGadget = FpGadget<G::BaseField>>,
        PC: PolynomialCommitment<G>,
        PCG: PolynomialCommitmentVerifierGadget<G::BaseField, G, PC>,
        D: Digest,
        H: FieldBasedHash<Data = G::BaseField>,
        HG: FieldBasedHashGadget<H, G::BaseField, DataGadget = FpGadget<G::BaseField>>,
    {
        fn new(
            index_vk: &'a VerifierKey<G, PC>,
            pc_vk: &'a PC::VerifierKey,
            proof: &'a Proof<G, PC>,
            public_inputs: &'a [G::ScalarField],
        ) -> Self {
            Self {
                index_vk: &index_vk,
                pc_vk: &pc_vk,
                proof: &proof,
                public_inputs: &public_inputs,
                _g_dual: PhantomData,
                _endomul_curve_gadget: PhantomData,
                _polynomial_commitment_verifier_gadget: PhantomData,
                _digest: PhantomData,
                _hash: PhantomData,
                _hash_gadget: PhantomData,
            }
        }

        fn get_usr_ins(&self) -> Result<Vec<GDual::ScalarField>, SynthesisError> {
            // Vk digest to GDual::ScalarField elements
            let mut hash_inputs = self
                .index_vk
                .get_hash()
                .to_field_elements()
                .map_err(|e| SynthesisError::Other(e.to_string()))?;
            let non_native_bits = self
                .public_inputs
                .iter()
                .flat_map(|val| val.write_bits())
                .collect::<Vec<_>>();

            hash_inputs.append(
                &mut non_native_bits
                    .to_field_elements()
                    .map_err(|e| SynthesisError::Other(e.to_string()))?,
            );

            // Hash field elements to get public input
            let public_input = {
                let mut digest = H::init_constant_length(hash_inputs.len(), None);

                hash_inputs.into_iter().for_each(|fe| {
                    digest.update(fe);
                });

                digest
                    .finalize()
                    .map_err(|e| SynthesisError::Other(e.to_string()))?
            };

            Ok(vec![public_input])
        }
    }

    impl<'a, G, GDual, GG, PC, PCG, D, H, HG> Clone
        for TestRecursiveCircuit<'a, G, GDual, GG, PC, PCG, D, H, HG>
    where
        G: EndoMulCurve,
        GDual: EndoMulCurve<ScalarField = G::BaseField>,
        GG: EndoMulCurveGadget<G, G::BaseField>
            + ToConstraintFieldGadget<G::BaseField, FieldGadget = FpGadget<G::BaseField>>,
        PC: PolynomialCommitment<G>,
        PCG: PolynomialCommitmentVerifierGadget<G::BaseField, G, PC>,
        D: Digest,
        H: FieldBasedHash<Data = G::BaseField>,
        HG: FieldBasedHashGadget<H, G::BaseField, DataGadget = FpGadget<G::BaseField>>,
    {
        fn clone(&self) -> Self {
            *self
        }
    }

    impl<'a, G, GDual, GG, PC, PCG, D, H, HG> Copy
        for TestRecursiveCircuit<'a, G, GDual, GG, PC, PCG, D, H, HG>
    where
        G: EndoMulCurve,
        GDual: EndoMulCurve<ScalarField = G::BaseField>,
        GG: EndoMulCurveGadget<G, G::BaseField>
            + ToConstraintFieldGadget<G::BaseField, FieldGadget = FpGadget<G::BaseField>>,
        PC: PolynomialCommitment<G>,
        PCG: PolynomialCommitmentVerifierGadget<G::BaseField, G, PC>,
        D: Digest,
        H: FieldBasedHash<Data = G::BaseField>,
        HG: FieldBasedHashGadget<H, G::BaseField, DataGadget = FpGadget<G::BaseField>>,
    {
    }

    impl<'a, G, GDual, GG, PC, PCG, D, H, HG> ConstraintSynthesizer<G::BaseField>
        for TestRecursiveCircuit<'a, G, GDual, GG, PC, PCG, D, H, HG>
    where
        G: EndoMulCurve,
        GDual: EndoMulCurve<ScalarField = G::BaseField>,
        GG: EndoMulCurveGadget<G, G::BaseField>
            + ToConstraintFieldGadget<G::BaseField, FieldGadget = FpGadget<G::BaseField>>,
        PC: PolynomialCommitment<G>,
        PCG: PolynomialCommitmentVerifierGadget<G::BaseField, G, PC>,
        D: Digest,
        H: FieldBasedHash<Data = G::BaseField>,
        HG: FieldBasedHashGadget<H, G::BaseField, DataGadget = FpGadget<G::BaseField>>,
    {
        /// This circuit allocates the Coboundary Marlin proof `self.proof` as witness and enforces
        /// that its succinct verification with verification key `self.index_vk` and public input
        /// `self.public_input` is successful. The verifer key and the public inputs are passed to
        /// the circuit as a single hash. This allows to expose a single public input, simplifying the
        /// interface of the circuit, and also mimicks how we intend to treat public inputs in the
        /// upcoming PCD scheme.
        fn generate_constraints<CS: ConstraintSystemAbstract<G::BaseField>>(
            self,
            cs: &mut CS,
        ) -> Result<(), SynthesisError> {
            let verifier_key_gadget =
                VerifierKeyGadget::<G, PC, PCG>::alloc(cs.ns(|| "alloc verifier key"), || {
                    Ok(self.index_vk)
                })?;

            let mut hash_inputs =
                verifier_key_gadget.to_field_gadget_elements(cs.ns(|| "vk as native fes"))?;

            // Alloc public inputs of the proof to be verified and convert them to native field elements
            let public_inputs = {
                let mut public_inputs = Vec::new();
                for (i, input) in self.public_inputs.iter().enumerate() {
                    public_inputs.push(
                        NonNativeFieldGadget::<G::ScalarField, G::BaseField>::alloc(
                            cs.ns(|| format!("alloc public input {}", i)),
                            || Ok(input),
                        )?,
                    );
                }
                public_inputs
            };
            hash_inputs.append(
                &mut public_inputs
                    .as_slice()
                    .to_field_gadget_elements(cs.ns(|| "public inputs as native fes"))?,
            );

            // Expose a single public input which is the hash of the previous ones
            let actual_digest =
                HG::enforce_hash_constant_length(cs.ns(|| "hash inputs"), &hash_inputs)?;

            let expected_digest =
                FpGadget::<G::BaseField>::alloc_input(cs.ns(|| "expected digest"), || {
                    actual_digest.get_value().get()
                })?;

            actual_digest.enforce_equal(cs.ns(|| "check pub ins"), &expected_digest)?;

            // Alloc proof to be verified
            let proof_gadget =
                ProofGadget::<G, PC, PCG>::alloc(cs.ns(|| "alloc proof"), || Ok(self.proof))?;

            // Enforce succinct proof verification
            MarlinVerifierGadget::<G, GG, PC, PCG>::succinct_verify(
                cs.ns(|| "proof verification"),
                &self.pc_vk,
                &verifier_key_gadget,
                &public_inputs,
                &proof_gadget,
            )?;

            Ok(())
        }
    }

    /// Auxiliary function to allocate all the data necessary to verify a Marlin proof in circuit.
    /// Take in input a marlin verifier key, a poly-commit verifier key, a marlin proof, and public
    /// inputs, allocate them in circuit, and return the respective gadgets.
    fn alloc_data<CS, G, GG, PC, PCG, D>(
        mut cs: CS,
        index_vk: &VerifierKey<G, PC>,
        proof: &Proof<G, PC>,
        public_inputs: &[G::ScalarField],
    ) -> Result<
        (
            VerifierKeyGadget<G, PC, PCG>,
            ProofGadget<G, PC, PCG>,
            Vec<NonNativeFieldGadget<G::ScalarField, G::BaseField>>,
        ),
        SynthesisError,
    >
    where
        CS: ConstraintSystemAbstract<G::BaseField>,
        G: EndoMulCurve,
        GG: EndoMulCurveGadget<G, G::BaseField>
            + ToConstraintFieldGadget<G::BaseField, FieldGadget = FpGadget<G::BaseField>>,
        PC: PolynomialCommitment<G>,
        PCG: PolynomialCommitmentVerifierGadget<G::BaseField, G, PC>,
        D: Digest,
    {
        let verifier_key_gadget =
            VerifierKeyGadget::<G, PC, PCG>::alloc(cs.ns(|| "alloc verifier key"), || {
                Ok(index_vk)
            })?;

        let proof_gadget = ProofGadget::<G, PC, PCG>::alloc(cs.ns(|| "alloc proof"), || Ok(proof))?;

        let public_inputs = {
            let mut result = Vec::new();
            for (i, input) in public_inputs.iter().enumerate() {
                result.push(NonNativeFieldGadget::<G::ScalarField, G::BaseField>::alloc(
                    cs.ns(|| format!("alloc public input {}", i)),
                    || Ok(input),
                )?)
            }
            result
        };

        Ok((verifier_key_gadget, proof_gadget, public_inputs))
    }

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

            let (verifier_key_gadget, proof_gadget, public_inputs) =
                alloc_data::<_, G, GG, PC, PCG, D>(
                    cs.ns(|| "alloc data"),
                    &index_vk,
                    &proof,
                    &correct_inputs,
                )
                .unwrap();

            MarlinVerifierGadget::<G, GG, PC, PCG>::succinct_verify(
                cs.ns(|| "proof verification"),
                &pc_vk,
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

            let (verifier_key_gadget, proof_gadget, public_inputs) =
                alloc_data::<_, G, GG, PC, PCG, D>(
                    cs.ns(|| "alloc data"),
                    &index_vk,
                    &proof,
                    &wrong_inputs,
                )
                .unwrap();

            MarlinVerifierGadget::<G, GG, PC, PCG>::verify_iop(
                cs.ns(|| "proof verification"),
                &pc_vk,
                &verifier_key_gadget,
                &public_inputs,
                &proof_gadget,
            )
            .unwrap();

            assert!(!cs.is_satisfied());

            // Test that tampering with output of verify_iop() makes succinct opening proof fail.
            let mut cs = ConstraintSystem::<G::BaseField>::new(SynthesisMode::Debug);

            let (verifier_key_gadget, proof_gadget, public_inputs) =
                alloc_data::<_, G, GG, PC, PCG, D>(
                    cs.ns(|| "alloc data"),
                    &index_vk,
                    &proof,
                    &correct_inputs,
                )
                .unwrap();

            // Check that IOP verification succeeds ...
            let (query_map, evaluations, mut commitments, mut fs_rng) =
                MarlinVerifierGadget::<G, GG, PC, PCG>::verify_iop(
                    cs.ns(|| "IOP verification"),
                    &pc_vk,
                    &verifier_key_gadget,
                    &public_inputs,
                    &proof_gadget,
                )
                .unwrap();
            assert!(cs.is_satisfied());

            // ... then tamper with a commitment and check that succinct opening proof fails
            let last_labeled_comm = commitments.pop().unwrap();
            let mut last_comm = last_labeled_comm.commitment().clone();
            last_comm
                .double_in_place(cs.ns(|| "double last commitment in place"))
                .unwrap();
            let last_comm_label = last_labeled_comm.label().clone();
            commitments.push(LabeledCommitmentGadget::new(last_comm_label, last_comm));
            MarlinVerifierGadget::<G, GG, PC, PCG>::succinct_verify_opening(
                cs.ns(|| "succinct opening verification"),
                &pc_vk,
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

            let (verifier_key_gadget, proof_gadget, public_inputs) =
                alloc_data::<_, G, GG, PC, PCG, D>(
                    cs.ns(|| "alloc data"),
                    &index_vk,
                    &proof,
                    &correct_inputs,
                )
                .unwrap();

            MarlinVerifierGadget::<G, GG, PC, PCG>::verify_iop(
                cs.ns(|| "IOP verification"),
                &pc_vk,
                &verifier_key_gadget,
                &public_inputs,
                &proof_gadget,
            )
            .unwrap();
            assert!(!cs.is_satisfied());
        }
    }

    fn test_recursive<G, GDual, GG, PC, PCDual, PCG, D, H, HG>(
        num_samples: usize,
        num_constraints: usize,
        num_variables: usize,
        zk: bool,
    ) where
        G: EndoMulCurve,
        GDual: EndoMulCurve<ScalarField = G::BaseField>,
        GG: EndoMulCurveGadget<G, G::BaseField>
            + ToConstraintFieldGadget<G::BaseField, FieldGadget = FpGadget<G::BaseField>>,
        PC: PolynomialCommitment<G>,
        PCDual: PolynomialCommitment<GDual>,
        PCG: PolynomialCommitmentVerifierGadget<G::BaseField, G, PC>,
        D: Digest,
        H: FieldBasedHash<Data = G::BaseField>,
        HG: FieldBasedHashGadget<H, G::BaseField, DataGadget = FpGadget<G::BaseField>>,
    {
        let rng = &mut thread_rng();

        let (original_pc_pk, original_pc_vk) = PC::setup::<D>(num_constraints - 1).unwrap();
        let (pc_pk, pc_vk) = (
            original_pc_pk.trim((num_constraints - 1) / 2).unwrap(),
            original_pc_vk.trim((num_constraints - 1) / 2).unwrap(),
        );
        assert_eq!(original_pc_pk.get_hash(), pc_pk.get_hash());
        assert_eq!(original_pc_vk.get_hash(), pc_vk.get_hash());

        let segment_size_recursive = 2usize.pow(18);
        let (pc_dual_pk, pc_dual_vk) = PCDual::setup::<D>(segment_size_recursive - 1).unwrap();

        for _ in 0..num_samples {
            let a = G::ScalarField::rand(rng);
            let b = G::ScalarField::rand(rng);
            let mut c = a;
            c.mul_assign(&b);
            let mut d = c;
            d.mul_assign(&b);

            let base_circuit = Circuit {
                a: Some(a),
                b: Some(b),
                c: Some(c),
                d: Some(d),
                num_constraints,
                num_variables,
            };
            let (index_pk, index_vk) =
                Marlin::<G, PC>::circuit_specific_setup::<_, D>(&pc_pk, base_circuit).unwrap();

            assert!(index_pk.is_valid());
            assert!(index_vk.is_valid());
            test_canonical_serialize_deserialize(true, &index_pk);
            test_canonical_serialize_deserialize(true, &index_vk);

            let base_proof = Marlin::<G, PC>::prove(
                &index_pk,
                &pc_pk,
                base_circuit,
                zk,
                if zk { Some(rng) } else { None },
            )
            .unwrap();

            println!("Created base proof");

            assert!(base_proof.is_valid());
            test_canonical_serialize_deserialize(true, &base_proof);

            // Success verification
            let correct_inputs = vec![c, d];
            assert!(
                Marlin::<G, PC>::verify(&index_vk, &pc_vk, &correct_inputs, &base_proof).unwrap()
            );

            // Now that we have successfully created and verified a base proof, we create and verify
            // a recursive proof which wraps the base proof.
            let recursive_circuit =
                TestRecursiveCircuit::<'_, G, GDual, GG, PC, PCG, D, H, HG>::new(
                    &index_vk,
                    &pc_vk,
                    &base_proof,
                    &correct_inputs,
                );

            let (index_pk_recursive, index_vk_recursive) =
                Marlin::<GDual, PCDual>::circuit_specific_setup::<_, D>(
                    &pc_dual_pk,
                    recursive_circuit.clone(),
                )
                .unwrap();

            assert!(index_pk_recursive.is_valid());
            assert!(index_vk_recursive.is_valid());
            test_canonical_serialize_deserialize(true, &index_pk_recursive);
            test_canonical_serialize_deserialize(true, &index_vk_recursive);

            let recursive_proof = Marlin::<GDual, PCDual>::prove(
                &index_pk_recursive,
                &pc_dual_pk,
                recursive_circuit,
                zk,
                if zk { Some(rng) } else { None },
            )
            .unwrap();

            println!("Created recursive proof");

            assert!(recursive_proof.is_valid());
            test_canonical_serialize_deserialize(true, &recursive_proof);

            // Success verification of `recursive_proof`. Since `recursive_circuit` encodes only the
            // succinct part of the full Marlin verification process, the hard part of the verification
            // is still missing. For efficiency reasons, the hard part of the verification will not
            // happen inside circuit, but by means of accumulators processed outside of circuit.
            // Since the scope of this test is to check the correctness of the MarlinVerifierGadget,
            // the processing of accumulators is not included.
            assert!(Marlin::<GDual, PCDual>::verify(
                &index_vk_recursive,
                &pc_dual_vk,
                recursive_circuit.get_usr_ins().unwrap().as_slice(),
                &recursive_proof
            )
            .unwrap());

            // Fail verification (wrong public inputs)
            assert!(!Marlin::<GDual, PCDual>::verify(
                &index_vk_recursive,
                &pc_dual_vk,
                &vec![G::BaseField::rand(rng)],
                &recursive_proof
            )
            .unwrap())
        }
    }

    mod poseidon_fs {
        use super::*;
        use algebra::curves::tweedle::dee::DeeJacobian;
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
        use primitives::{PoseidonHash, PoseidonQuinticSBox, TweedleFrPoseidonParameters};
        use r1cs_crypto::{
            PoseidonHashGadget, QuinticSBoxGadget, TweedleFrDensityOptimizedPoseidonParameters,
        };
        use r1cs_std::fields::fp::FpGadget;
        use r1cs_std::groups::curves::short_weierstrass::AffineGadget;

        type G = DumJacobian;
        type GDual = DeeJacobian;
        type ConstraintF = <G as Group>::BaseField;
        type GG = AffineGadget<TweedledumParameters, ConstraintF, FpGadget<Fr>>;
        type FS = TweedleFrPoseidonFSRng;
        type FSG = DensityOptimizedPoseidonQuinticSBoxFSRngGadget<
            ConstraintF,
            TweedleFrPoseidonParameters,
            TweedleFrDensityOptimizedPoseidonParameters,
        >;
        type PC = DomainExtendedPolynomialCommitment<G, InnerProductArgPC<G, FS>>;
        type PCDual = DomainExtendedPolynomialCommitment<GDual, InnerProductArgPC<GDual, FS>>;
        type PCG = DomainExtendedPolyCommitVerifierGadget<
            ConstraintF,
            G,
            InnerProductArgPC<G, FS>,
            InnerProductArgGadget<ConstraintF, FSG, G, GG>,
        >;
        type D = Blake2s;
        type SBox = PoseidonQuinticSBox<ConstraintF, TweedleFrPoseidonParameters>;
        type H = PoseidonHash<ConstraintF, TweedleFrPoseidonParameters, SBox>;
        type HG = PoseidonHashGadget<
            ConstraintF,
            TweedleFrPoseidonParameters,
            SBox,
            QuinticSBoxGadget<ConstraintF, SBox>,
        >;

        #[test]
        fn test_marlin_verifier_gadget() {
            let num_constraints = 25;
            let num_variables = 25;

            test_circuit::<G, GG, PC, PCG, D>(10, num_constraints, num_variables, false);
            test_circuit::<G, GG, PC, PCG, D>(10, num_constraints, num_variables, true);
        }

        #[test]
        fn prove_and_verify_recursive() {
            let num_constraints = 25;
            let num_variables = 25;

            test_recursive::<G, GDual, GG, PC, PCDual, PCG, D, H, HG>(
                1,
                num_constraints,
                num_variables,
                false,
            );
            test_recursive::<G, GDual, GG, PC, PCDual, PCG, D, H, HG>(
                1,
                num_constraints,
                num_variables,
                true,
            );
        }
    }
}
