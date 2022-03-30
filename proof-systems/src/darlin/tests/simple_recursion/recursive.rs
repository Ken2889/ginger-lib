use algebra::{Group, EndoMulCurve, ToConstraintField};
use blake2::Blake2s;
use fiat_shamir::{FiatShamirRng, constraints::FiatShamirRngGadget};
use poly_commit::{ipa_pc::{InnerProductArgGadget, CommitterKey, InnerProductArgPC, VerifierKey}, DomainExtendedPolyCommitVerifierGadget, PolynomialCommitmentVerifierGadget};
use marlin::{
    VerifierKey as MarlinVerifierKey,
    constraints::{data_structures::{ProofGadget as MarlinProofGadget, VerifierKeyGadget}, MarlinVerifierGadget}
};
use primitives::{PoseidonParameters, SBox, PoseidonHash, FieldBasedHash};
use r1cs_core::{ConstraintSynthesizer, ConstraintSystemAbstract, SynthesisError};
use r1cs_crypto::{PoseidonHashGadget, SBoxGadget, FieldBasedHashGadget};
use r1cs_std::{prelude::*, fields::{nonnative::nonnative_field_gadget::NonNativeFieldGadget, fp::FpGadget}, to_field_gadget_vec::ToConstraintFieldGadget, Assignment};
use rand::thread_rng;
use crate::darlin::{
    pcd::{simple_marlin::{MarlinProof, SimpleMarlinPCD}, PCDCircuit, error::PCDError, PCD},
    DomainExtendedIpaPc,
    tests::simple_marlin::generate_test_data as generate_simple_marlin_test_data
};
use std::marker::PhantomData;

type PCGadget<G, GG, FS, FSG> = DomainExtendedPolyCommitVerifierGadget<
    <G as Group>::BaseField,
    G,
    InnerProductArgPC<G, FS>,
    InnerProductArgGadget<<G as Group>::BaseField, FSG, G, GG>,
>;
type VkGadget<G, GG, FS, FSG> = VerifierKeyGadget<
    G,
    DomainExtendedIpaPc<G, FS>,
    PCGadget<G, GG, FS, FSG>
>;
type ProofGadget<G, GG, FS, FSG> = MarlinProofGadget<
    G,
    DomainExtendedIpaPc<G, FS>,
    PCGadget<G, GG, FS, FSG>
>;
type VerifierGadget<G, GG, FS, FSG> = MarlinVerifierGadget<
    G,
    GG,
    DomainExtendedIpaPc<G, FS>,
    PCGadget<G, GG, FS, FSG>
>;
type FieldHash<G, P, SB> = PoseidonHash<<G as Group>::BaseField, P, SB>; 
type FieldHashGadget<G, P, SB, SBG> = PoseidonHashGadget<<G as Group>::BaseField, P, SB, SBG>;

pub struct TestRecursiveCircuit<'a, G, GG, FS, FSG, P, SB, SBG>
where
    G: EndoMulCurve,
    GG: 'static 
        + EndoMulCurveGadget<G, G::BaseField>
        + ToConstraintFieldGadget<G::BaseField, FieldGadget = FpGadget<G::BaseField>>,
    FS: 'static + FiatShamirRng,
    FSG: 'static + FiatShamirRngGadget<G::BaseField>,
    P: PoseidonParameters<Fr = G::BaseField>,
    SB: SBox<Field = G::BaseField, Parameters = P>,
    SBG: SBoxGadget<G::BaseField, SB>,
{
    proof: MarlinProof<G, FS>,
    pc_vk: &'a CommitterKey<G>,
    index_vk: MarlinVerifierKey<G, DomainExtendedIpaPc<G, FS>>,
    public_inputs: Vec<G::ScalarField>,
    _group_gadget: PhantomData<GG>,
    _fs_rng_gadget: PhantomData<FSG>,
    _hash_params: PhantomData<P>,
    _sbox: PhantomData<SB>,
    _sbox_gadget: PhantomData<SBG>
}

impl <'a, G, GG, FS, FSG, P, SB, SBG> ConstraintSynthesizer<G::BaseField> for TestRecursiveCircuit<'a, G, GG, FS, FSG, P, SB, SBG>
where
    G: EndoMulCurve,
    GG: 'static 
        + EndoMulCurveGadget<G, G::BaseField>
        + ToConstraintFieldGadget<G::BaseField, FieldGadget = FpGadget<G::BaseField>>,
    FS: 'static + FiatShamirRng,
    FSG: 'static + FiatShamirRngGadget<G::BaseField>,
    P: PoseidonParameters<Fr = G::BaseField>,
    SB: SBox<Field = G::BaseField, Parameters = P>,
    SBG: SBoxGadget<G::BaseField, SB>,
{
    //TODO: Expose only one public input, which is the Poseidon Hash of all the public inputs.
    //TODO: Add some additional payload
    fn generate_constraints<CS: ConstraintSystemAbstract<G::BaseField>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError>
    {
        // Construct public input
        // Alloc vk and convert it to native field elements
        let verifier_key_gadget = VkGadget::<G, GG, FS, FSG>::alloc(
            cs.ns(|| "alloc verifier key"),
            || Ok(&self.index_vk),
        )?;

        let mut hash_inputs = verifier_key_gadget
            .to_field_gadget_elements(cs.ns(|| "vk as native fes"))?;

        // Alloc public inputs of the proof to be verified and convert them to native field elements
        let public_inputs = {
            let mut public_inputs = Vec::new();
            for (i, input) in self.public_inputs.iter().enumerate() {
                public_inputs.push(
                    NonNativeFieldGadget::<G::ScalarField, G::BaseField>::alloc(
                        cs.ns(|| format!("alloc public input {}", i)),
                        || Ok(input),
                    )?
                );
            }
            public_inputs
        };
        hash_inputs.append(
            &mut public_inputs
                .as_slice()
                .to_field_gadget_elements(cs.ns(|| "public inputs as native fes"))?
        );

        // Expose a single public input which is the hash of the previous ones
        let actual_digest = FieldHashGadget::<G, P, SB, SBG>::enforce_hash_constant_length(
            cs.ns(|| "hash inputs"),
            &hash_inputs,
        )?;

        let expected_digest = FpGadget::<G::BaseField>::alloc_input(
            cs.ns(|| "expected digest"),
            || actual_digest.get_value().get()
        )?;

        actual_digest.enforce_equal(
            cs.ns(|| "check pub ins"),
            &expected_digest
        )?;

        // Enforce proof verification
        // TODO: No need to allocate it in the future, should be hardcoded
        let pc_verifier_key_gadget = 
        <
            PCGadget<G, GG, FS, FSG> as PolynomialCommitmentVerifierGadget
            <
                G::BaseField,
                G,
                DomainExtendedIpaPc<G, FS>
            >
        >::VerifierKeyGadget::alloc(
            cs.ns(|| "alloc pc verifier key"),
            || Ok(self.pc_vk)
        )?;

        // Alloc proof to be verified
        let proof_gadget = ProofGadget::<G, GG, FS, FSG>::alloc(
            cs.ns(|| "alloc proof"),
            || Ok(&self.proof.0)    
        )?;

        // Enforce succinct proof verification
        VerifierGadget::<G, GG, FS, FSG>::verify(
            cs.ns(|| "proof verification"),
            &pc_verifier_key_gadget,
            &verifier_key_gadget,
            &public_inputs,
            &proof_gadget,
        )?;

        Ok(())
    }
}

#[derive(Clone)]
pub struct TestRecursiveCircuitConfig<'a, G: EndoMulCurve> {
    num_constraints: usize,
    segment_size: usize,
    ck: &'a CommitterKey<G>,
    vk: &'a VerifierKey<G>,
}

impl <'a, G, GDual, GG, FS, FSG, P, SB, SBG> PCDCircuit<GDual> for TestRecursiveCircuit<'a, G, GG, FS, FSG, P, SB, SBG>
where
    G: EndoMulCurve<BaseField = <GDual as Group>::ScalarField>
        + ToConstraintField<<GDual as Group>::ScalarField>,
    GDual: EndoMulCurve<BaseField = <G as Group>::ScalarField>
        + ToConstraintField<<G as Group>::ScalarField>,
    GG: 'static 
        + EndoMulCurveGadget<G, G::BaseField>
        + ToConstraintFieldGadget<G::BaseField, FieldGadget = FpGadget<G::BaseField>>,
    FS: 'static + FiatShamirRng,
    FSG: 'static + FiatShamirRngGadget<G::BaseField>,
    P: PoseidonParameters<Fr = G::BaseField>,
    SB: SBox<Field = G::BaseField, Parameters = P>,
    SBG: SBoxGadget<G::BaseField, SB>,
{
    type SetupData = TestRecursiveCircuitConfig<'a, G>;

    type AdditionalData = ();

    type SystemInputs = ();

    type PreviousPCD = SimpleMarlinPCD<'a, G, FS>;

    fn init(config: Self::SetupData) -> Self {
        // TODO: Here we generate a new PCD from scratch and we use it to initialize an empty instance of the circuit.
        //       In real use cases we need to estimate and set proof and vk lengths. And be sure that any
        //       time we use this circuit, proof and vks get padded before being passed to it. 
        let (mut pcd, mut vk) = generate_simple_marlin_test_data::<Blake2s, G, FS, _>(
            config.num_constraints,
            config.segment_size,
            (config.ck, config.vk),
            1,
            &mut thread_rng()
        );

        let pcd = pcd.pop().unwrap();

        TestRecursiveCircuit { 
            proof: pcd.proof,
            pc_vk: config.vk,
            index_vk: vk.pop().unwrap(),
            public_inputs: pcd.usr_ins,
            _group_gadget: PhantomData,
            _fs_rng_gadget: PhantomData,
            _hash_params: PhantomData,
            _sbox: PhantomData,
            _sbox_gadget: PhantomData,
        }
    }

    fn init_state(
        config: Self::SetupData,
        mut previous_proofs_data: Vec<Self::PreviousPCD>,
        mut previous_proofs_vks: Vec<<Self::PreviousPCD as PCD>::PCDVerifierKey>,
        _additional_data: Self::AdditionalData,
    ) -> Self 
    {
        // Cannot verify more than one PCD
        assert!(previous_proofs_data.len() == 1);
        assert!(previous_proofs_vks.len() == 1);

        let pcd = previous_proofs_data.pop().unwrap();
        let vk = previous_proofs_vks.pop().unwrap();

        TestRecursiveCircuit { 
            proof: pcd.proof,
            pc_vk: config.vk,
            index_vk: vk.0.clone(),
            public_inputs: pcd.usr_ins,
            _group_gadget: PhantomData,
            _fs_rng_gadget: PhantomData,
            _hash_params: PhantomData,
            _sbox: PhantomData,
            _sbox_gadget: PhantomData,
        }
    }

    fn get_sys_ins(&self) -> Result<&Self::SystemInputs, PCDError> {
        todo!()
    }

    fn get_usr_ins(&self) -> Result<Vec<GDual::ScalarField>, PCDError> {
        
        // Vk digest to GDual::ScalarField elements
        let mut hash_inputs = self
            .index_vk
            .get_hash()
            .to_field_elements()
            .map_err(|e| PCDError::MissingUserInputs(e.to_string()))?;
        
        // Proof's public inputs to GDual::ScalarField elements
        for input in &self.public_inputs {
            hash_inputs.append(
                &mut NonNativeFieldGadget::<G::ScalarField, G::BaseField>::get_limbs_representations(input)
                    .map_err(|e| PCDError::MissingUserInputs(e.to_string()))?
            );
        }

        // Hash field elements to get public input
        let public_input = {
            let mut digest = FieldHash::<G, P, SB>::init_constant_length(
                hash_inputs.len(),
                None
            );

            hash_inputs
                .into_iter()
                .for_each(|fe | { digest.update(fe); });

            digest
                .finalize()
                .map_err(|e| PCDError::MissingUserInputs(e.to_string()))
        }?;

        Ok(vec![public_input])
    }
}