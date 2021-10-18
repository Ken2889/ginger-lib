use algebra::{Field, PrimeField};
use primitives::{
    commitment::injective_map::{InjectiveMap, PedersenCommCompressor},
    commitment::pedersen::PedersenWindow,
};

use crate::commitment::{
    pedersen::{
        PedersenCommitmentGadget, PedersenCommitmentGadgetParameters, PedersenRandomnessGadget
    },
    CommitmentGadget,
};

pub use crate::crh::injective_map::InjectiveMapGadget;
use algebra::groups::Group;
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use r1cs_std::{groups::GroupGadget, uint8::UInt8};

use std::marker::PhantomData;

pub struct PedersenCommitmentCompressorGadget<G, I, ConstraintF, GG, IG>
where
    G: Group,
    I: InjectiveMap<G>,
    ConstraintF: Field,
    GG: GroupGadget<G, ConstraintF>,
    IG: InjectiveMapGadget<G, I, ConstraintF, GG>,
{
    _compressor:        PhantomData<I>,
    _compressor_gadget: PhantomData<IG>,
    _crh:               PedersenCommitmentGadget<G, ConstraintF, GG>,
}

impl<G, I, ConstraintF, GG, IG, W> CommitmentGadget<PedersenCommCompressor<G, I, W>, ConstraintF>
    for PedersenCommitmentCompressorGadget<G, I, ConstraintF, GG, IG>
where
    G: Group,
    I: InjectiveMap<G>,
    ConstraintF: PrimeField,
    GG: GroupGadget<G, ConstraintF>,
    IG: InjectiveMapGadget<G, I, ConstraintF, GG>,
    W: PedersenWindow,
{
    type OutputGadget = IG::OutputGadget;
    type ParametersGadget = PedersenCommitmentGadgetParameters<G, W, ConstraintF>;
    type RandomnessGadget = PedersenRandomnessGadget;

    fn check_commitment_gadget<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        parameters: &Self::ParametersGadget,
        input: &[UInt8],
        r: &Self::RandomnessGadget,
    ) -> Result<Self::OutputGadget, SynthesisError> {
        let result = PedersenCommitmentGadget::<G, ConstraintF, GG>::check_commitment_gadget(
            cs.ns(|| "PedersenComm"),
            parameters,
            input,
            r,
        )?;
        IG::evaluate_map(cs.ns(|| "InjectiveMap"), &result)
    }
}
