use algebra::{Group, EndoMulCurve, ToConstraintField};
use fiat_shamir::{FiatShamirRng, constraints::FiatShamirRngGadget};
use marlin::VerifierKey as MarlinVerifierKey;
use poly_commit::{ipa_pc::VerifierKey as DLogVerifierKey, PolynomialCommitmentVerifierGadget};
use primitives::{PoseidonParameters, SBox};
use r1cs_core::{ConstraintSynthesizer, ConstraintSystemAbstract, SynthesisError};
use r1cs_crypto::SBoxGadget;
use r1cs_std::{Assignment, prelude::*, fields::{nonnative::nonnative_field_gadget::NonNativeFieldGadget, fp::FpGadget}, to_field_gadget_vec::ToConstraintFieldGadget};
use crate::darlin::pcd::{simple_marlin::{MarlinProof, DefaultMarlinProofConfig}, PCDCircuit};
use super::*;
use std::marker::PhantomData;

pub struct WrapCircuit<'a, G1, G2, GG, FS, FSG, P, SB, SBG>
where
    G1: EndoMulCurve<BaseField = <G2 as Group>::ScalarField>
        + ToConstraintField<<G2 as Group>::ScalarField>,
    G2: EndoMulCurve<BaseField = <G1 as Group>::ScalarField>
        + ToConstraintField<<G1 as Group>::ScalarField>,
    GG: 'static 
        + EndoMulCurveGadget<G1, G1::BaseField>
        + ToConstraintFieldGadget<G1::BaseField, FieldGadget = FpGadget<G1::BaseField>>,
    FS: 'static + FiatShamirRng,
    FSG: 'static + FiatShamirRngGadget<G1::BaseField>,
    P: PoseidonParameters<Fr = G2::ScalarField>,
    SB: SBox<Field = G2::ScalarField, Parameters = P>,
    SBG: SBoxGadget<G2::ScalarField, SB>,
{
    proof: MarlinProof<G1, FS>,
    pc_vk: &'a DLogVerifierKey<G1>,
    index_vk: MarlinVerifierKey<G1, DomainExtendedIpaPc<G1, FS>>,
    public_inputs: Vec<G1::ScalarField>,
    _dual_group: PhantomData<G2>,
    _group_gadget: PhantomData<GG>,
    _fs_rng_gadget: PhantomData<FSG>,
    _hash_params: PhantomData<P>,
    _sbox: PhantomData<SB>,
    _sbox_gadget: PhantomData<SBG>
}

impl<'a, G1, G2, GG, FS, FSG, P, SB, SBG> ConstraintSynthesizer<G2::ScalarField> for WrapCircuit<'a, G1, G2, GG, FS, FSG, P, SB, SBG>
where
    G1: EndoMulCurve<BaseField = <G2 as Group>::ScalarField>
        + ToConstraintField<<G2 as Group>::ScalarField>,
    G2: EndoMulCurve<BaseField = <G1 as Group>::ScalarField>
        + ToConstraintField<<G1 as Group>::ScalarField>,
    GG: 'static 
        + EndoMulCurveGadget<G1, G1::BaseField>
        + ToConstraintFieldGadget<G1::BaseField, FieldGadget = FpGadget<G1::BaseField>>,
    FS: 'static + FiatShamirRng,
    FSG: 'static + FiatShamirRngGadget<G1::BaseField>,
    P: PoseidonParameters<Fr = G2::ScalarField>,
    SB: SBox<Field = G2::ScalarField, Parameters = P>,
    SBG: SBoxGadget<G2::ScalarField, SB>,
{
    fn generate_constraints<CS: ConstraintSystemAbstract<G2::ScalarField>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError>
    {
        // Construct public input
        // Alloc vk and convert it to native field elements
        let verifier_key_gadget = MarlinVkGadget::<G1, GG, FS, FSG>::alloc(
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
                    NonNativeFieldGadget::<G1::ScalarField, G2::ScalarField>::alloc(
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
        let actual_digest = FieldHashGadget::<G2::ScalarField, P, SB, SBG>::enforce_hash_constant_length(
            cs.ns(|| "hash inputs"),
            &hash_inputs,
        )?;

        let expected_digest = FpGadget::<G2::ScalarField>::alloc_input(
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
            PCGadget<G1, GG, FS, FSG> as PolynomialCommitmentVerifierGadget
            <
                G1::BaseField,
                G1,
                DomainExtendedIpaPc<G1, FS>
            >
        >::VerifierKeyGadget::alloc(
            cs.ns(|| "alloc pc verifier key"),
            || Ok(self.pc_vk)
        )?;

        // Alloc proof to be verified
        let proof_gadget = ProofGadget::<G1, GG, FS, FSG>::alloc(
            cs.ns(|| "alloc proof"),
            || Ok(&self.proof.0)    
        )?;

        // Enforce succinct proof verification
        VerifierGadget::<G1, GG, FS, FSG>::verify(
            cs.ns(|| "proof verification"),
            &pc_verifier_key_gadget,
            &verifier_key_gadget,
            &public_inputs,
            &proof_gadget,
        )?;

        Ok(())
    }
}

pub type WrapPCD<'a, G2, G1, FS> = Merge1PCD<'a, G2, G1, FS>;

impl<'a, G1, G2, GG, FS, FSG, P, SB, SBG> PCDCircuit<G2> for WrapCircuit<'a, G1, G2, GG, FS, FSG, P, SB, SBG>
where
    G1: EndoMulCurve<BaseField = <G2 as Group>::ScalarField>
        + ToConstraintField<<G2 as Group>::ScalarField>,
    G2: EndoMulCurve<BaseField = <G1 as Group>::ScalarField>
        + ToConstraintField<<G1 as Group>::ScalarField>,
    GG: 'static 
        + EndoMulCurveGadget<G1, G1::BaseField>
        + ToConstraintFieldGadget<G1::BaseField, FieldGadget = FpGadget<G1::BaseField>>,
    FS: 'static + FiatShamirRng,
    FSG: 'static + FiatShamirRngGadget<G1::BaseField>,
    P: PoseidonParameters<Fr = G2::ScalarField>,
    SB: SBox<Field = G2::ScalarField, Parameters = P>,
    SBG: SBoxGadget<G2::ScalarField, SB>,
{
    type SetupData = DefaultMarlinProofConfig;

    type AdditionalData = ();

    type SystemInputs = G2::ScalarField;

    type PreviousPCD = Merge1PCD<'a, G1, G2, FS>;

    fn init(config: Self::SetupData) -> Self {
        todo!()
    }

    fn init_state(
        config: Self::SetupData,
        previous_proofs_data: Vec<Self::PreviousPCD>,
        previous_proofs_vks: Vec<<Self::PreviousPCD as crate::darlin::pcd::PCD>::PCDVerifierKey>,
        additional_data: Self::AdditionalData,
    ) -> Self {
        todo!()
    }

    fn get_sys_ins(&self) -> Result<&Self::SystemInputs, crate::darlin::pcd::error::PCDError> {
        todo!()
    }

    fn get_usr_ins(&self) -> Result<Vec<<G2>::ScalarField>, crate::darlin::pcd::error::PCDError> {
        todo!()
    }
}

// #[derive(Clone)]
// pub struct TestRecursiveCircuitConfig<'a, G: EndoMulCurve> {
//     num_constraints: usize,
//     segment_size: usize,
//     ck: &'a CommitterKey<G>,
//     vk: &'a VerifierKey<G>,
// }

// impl <'a, G, GDual, GG, FS, FSG, P, SB, SBG> PCDCircuit<GDual> for WrapCircuit<'a, G, GG, FS, FSG, P, SB, SBG>
// where
//     G: EndoMulCurve<BaseField = <GDual as Group>::ScalarField>
//         + ToConstraintField<<GDual as Group>::ScalarField>,
//     GDual: EndoMulCurve<BaseField = <G as Group>::ScalarField>
//         + ToConstraintField<<G as Group>::ScalarField>,
//     GG: 'static 
//         + EndoMulCurveGadget<G, G::BaseField>
//         + ToConstraintFieldGadget<G::BaseField, FieldGadget = FpGadget<G::BaseField>>,
//     FS: 'static + FiatShamirRng,
//     FSG: 'static + FiatShamirRngGadget<G::BaseField>,
//     P: PoseidonParameters<Fr = G::BaseField>,
//     SB: SBox<Field = G::BaseField, Parameters = P>,
//     SBG: SBoxGadget<G::BaseField, SB>,
// {
//     type SetupData = TestRecursiveCircuitConfig<'a, G>;

//     type AdditionalData = ();

//     type SystemInputs = ();

//     type PreviousPCD = SimpleMarlinPCD<'a, G, FS>;

//     fn init(config: Self::SetupData) -> Self {
//         // TODO: Here we generate a new PCD from scratch and we use it to initialize an empty instance of the circuit.
//         //       In real use cases we need to estimate and set proof and vk lengths. And be sure that any
//         //       time we use this circuit, proof and vks get padded before being passed to it. 
//         let (mut pcd, mut vk) = generate_simple_marlin_test_data::<Blake2s, G, FS, _>(
//             config.num_constraints,
//             config.segment_size,
//             (config.ck, config.vk),
//             1,
//             &mut thread_rng()
//         );

//         let pcd = pcd.pop().unwrap();

//         WrapCircuit { 
//             proof: pcd.proof,
//             pc_vk: config.vk,
//             index_vk: vk.pop().unwrap(),
//             public_inputs: pcd.usr_ins,
//             _group_gadget: PhantomData,
//             _fs_rng_gadget: PhantomData,
//             _hash_params: PhantomData,
//             _sbox: PhantomData,
//             _sbox_gadget: PhantomData,
//         }
//     }

//     fn init_state(
//         config: Self::SetupData,
//         mut previous_proofs_data: Vec<Self::PreviousPCD>,
//         mut previous_proofs_vks: Vec<<Self::PreviousPCD as PCD>::PCDVerifierKey>,
//         _additional_data: Self::AdditionalData,
//     ) -> Self 
//     {
//         // Cannot verify more than one PCD
//         assert!(previous_proofs_data.len() == 1);
//         assert!(previous_proofs_vks.len() == 1);

//         let pcd = previous_proofs_data.pop().unwrap();
//         let vk = previous_proofs_vks.pop().unwrap();

//         WrapCircuit { 
//             proof: pcd.proof,
//             pc_vk: config.vk,
//             index_vk: vk.0.clone(),
//             public_inputs: pcd.usr_ins,
//             _group_gadget: PhantomData,
//             _fs_rng_gadget: PhantomData,
//             _hash_params: PhantomData,
//             _sbox: PhantomData,
//             _sbox_gadget: PhantomData,
//         }
//     }

//     fn get_sys_ins(&self) -> Result<&Self::SystemInputs, PCDError> {
//         todo!()
//     }

//     fn get_usr_ins(&self) -> Result<Vec<GDual::ScalarField>, PCDError> {
        
//         // Vk digest to GDual::ScalarField elements
//         let mut hash_inputs = self
//             .index_vk
//             .get_hash()
//             .to_field_elements()
//             .map_err(|e| PCDError::MissingUserInputs(e.to_string()))?;
        
//         // Proof's public inputs to GDual::ScalarField elements
//         for input in &self.public_inputs {
//             hash_inputs.append(
//                 &mut NonNativeFieldGadget::<G::ScalarField, G::BaseField>::get_limbs_representations(input)
//                     .map_err(|e| PCDError::MissingUserInputs(e.to_string()))?
//             );
//         }

//         // Hash field elements to get public input
//         let public_input = {
//             let mut digest = FieldHash::<G, P, SB>::init_constant_length(
//                 hash_inputs.len(),
//                 None
//             );

//             hash_inputs
//                 .into_iter()
//                 .for_each(|fe | { digest.update(fe); });

//             digest
//                 .finalize()
//                 .map_err(|e| PCDError::MissingUserInputs(e.to_string()))
//         }?;

//         Ok(vec![public_input])
//     }
// }

// pub struct TestRecursivePCD {

// }

// impl PCD for TestRecursivePCD {
//     type PCDAccumulator;

//     type PCDVerifierKey;

//     fn succinct_verify(
//         &self,
//         vk: &Self::PCDVerifierKey,
//     ) -> Result<<Self::PCDAccumulator as crate::darlin::accumulators::ItemAccumulator>::Item, PCDError> {
//         todo!()
//     }

//     fn get_id() -> String {
//         todo!()
//     }
// }

// pub struct TestRecursivePCDNode<'a, G, GDual, GG, FS, FSG, P, SB, SBG>
// where
//     G: EndoMulCurve<BaseField = <GDual as Group>::ScalarField>
//         + ToConstraintField<<GDual as Group>::ScalarField>,
//     GDual: EndoMulCurve<BaseField = <G as Group>::ScalarField>
//         + ToConstraintField<<G as Group>::ScalarField>,
//     GG: 'static 
//         + EndoMulCurveGadget<G, G::BaseField>
//         + ToConstraintFieldGadget<G::BaseField, FieldGadget = FpGadget<G::BaseField>>,
//     FS: 'static + FiatShamirRng,
//     FSG: 'static + FiatShamirRngGadget<G::BaseField>,
//     P: PoseidonParameters<Fr = G::BaseField>,
//     SB: SBox<Field = G::BaseField, Parameters = P>,
//     SBG: SBoxGadget<G::BaseField, SB>,
// {
//     _lifetime: PhantomData<&'a ()>,
//     _group: PhantomData<G>,
//     _dual_group: PhantomData<GDual>,
//     _group_gadget: PhantomData<GG>,
//     _fs_rng: PhantomData<FS>,
//     _fs_rng_gadget: PhantomData<FSG>,
//     _hash_params: PhantomData<P>,
//     _sbox: PhantomData<SB>,
//     _sbox_gadget: PhantomData<SBG>
// }

// impl<'a, G, GDual, GG, FS, FSG, P, SB, SBG> PCDNode<G, GDual> for TestRecursivePCDNode<'a, G, GDual, GG, FS, FSG, P, SB, SBG>
// where
//     G: EndoMulCurve<BaseField = <GDual as Group>::ScalarField>
//         + ToConstraintField<<GDual as Group>::ScalarField>,
//     GDual: EndoMulCurve<BaseField = <G as Group>::ScalarField>
//         + ToConstraintField<<G as Group>::ScalarField>,
//     GG: 'static 
//         + EndoMulCurveGadget<G, G::BaseField>
//         + ToConstraintFieldGadget<G::BaseField, FieldGadget = FpGadget<G::BaseField>>,
//     FS: 'static + FiatShamirRng,
//     FSG: 'static + FiatShamirRngGadget<G::BaseField>,
//     P: PoseidonParameters<Fr = G::BaseField>,
//     SB: SBox<Field = G::BaseField, Parameters = P>,
//     SBG: SBoxGadget<G::BaseField, SB>,
// {
//     type ProverKey;

//     type VerifierKey;

//     type InputPCD = SimpleMarlinPCD<'a, G, FS>;

//     type OutputPCD = TestRecursivePCD;

//     type Circuit = WrapCircuit<'a, G, GG, FS, FSG, P, SB, SBG>;

//     fn index<D: Digest>(
//         committer_key: &CommitterKey<G>,
//         config: <Self::Circuit as PCDCircuit<G>>::SetupData,
//     ) -> Result<(Self::ProverKey, Self::VerifierKey), PCDError> {
//         todo!()
//     }

//     fn prove(
//         index_pk: &Self::ProverKey,
//         pc_pk: &CommitterKey<G>,
//         config: <Self::Circuit as PCDCircuit<G>>::SetupData,
//         previous: Vec<Self::InputPCD>,
//         additional_data: <Self::Circuit as PCDCircuit<G>>::AdditionalData,
//         zk: bool,
//         zk_rng: Option<&mut dyn rand::RngCore>,
//     ) -> Result<Self::OutputPCD, PCDError> {
//         todo!()
//     }
// }

use super::merge::Merge1PCD;