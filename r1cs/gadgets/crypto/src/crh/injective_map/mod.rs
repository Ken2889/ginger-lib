use primitives::crh::{
    injective_map::{InjectiveMap, JacobianCompressor, PedersenCRHCompressor, TECompressor},
    pedersen::PedersenWindow,
};
use std::{fmt::Debug, marker::PhantomData};

use crate::crh::{
    pedersen::{PedersenCRHGadget, PedersenCRHGadgetParameters},
    FixedLengthCRHGadget,
};

use algebra::{
    curves::{
        models::{ModelParameters, TEModelParameters},
        short_weierstrass_jacobian::Jacobian,
        twisted_edwards_extended::TEExtended,
        Curve,
    },
    fields::{Field, PrimeField, SquareRootField},
    SWModelParameters,
};
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use r1cs_std::{
    fields::fp::FpGadget,
    groups::{
        curves::short_weierstrass::AffineGadget as SWGadget,
        curves::twisted_edwards::AffineGadget as TwistedEdwardsGadget, GroupGadget,
    },
    prelude::*,
};

pub trait InjectiveMapGadget<
    G: Curve,
    I: InjectiveMap<G>,
    ConstraintF: Field,
    GG: GroupGadget<G, ConstraintF>,
>
{
    type OutputGadget: EqGadget<ConstraintF>
        + ToBytesGadget<ConstraintF>
        + CondSelectGadget<ConstraintF>
        + AllocGadget<I::Output, ConstraintF>
        + Debug
        + Clone
        + Sized;

    fn evaluate_map<CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        ge: &GG,
    ) -> Result<Self::OutputGadget, SynthesisError>;
}

pub struct JacobianCompressorGadget;

impl<ConstraintF, P>
    InjectiveMapGadget<
        Jacobian<P>,
        JacobianCompressor,
        ConstraintF,
        SWGadget<P, ConstraintF, FpGadget<ConstraintF>>,
    > for JacobianCompressorGadget
where
    ConstraintF: PrimeField + SquareRootField,
    P: SWModelParameters + ModelParameters<BaseField = ConstraintF>,
{
    type OutputGadget = FpGadget<ConstraintF>;

    fn evaluate_map<CS: ConstraintSystemAbstract<ConstraintF>>(
        _cs: CS,
        ge: &SWGadget<P, ConstraintF, FpGadget<ConstraintF>>,
    ) -> Result<Self::OutputGadget, SynthesisError> {
        Ok(ge.x.clone())
    }
}

pub struct TECompressorGadget;

impl<ConstraintF, P>
    InjectiveMapGadget<
        TEExtended<P>,
        TECompressor,
        ConstraintF,
        TwistedEdwardsGadget<P, ConstraintF, FpGadget<ConstraintF>>,
    > for TECompressorGadget
where
    ConstraintF: PrimeField + SquareRootField,
    P: TEModelParameters + ModelParameters<BaseField = ConstraintF>,
{
    type OutputGadget = FpGadget<ConstraintF>;

    fn evaluate_map<CS: ConstraintSystemAbstract<ConstraintF>>(
        _cs: CS,
        ge: &TwistedEdwardsGadget<P, ConstraintF, FpGadget<ConstraintF>>,
    ) -> Result<Self::OutputGadget, SynthesisError> {
        Ok(ge.x.clone())
    }
}

pub struct PedersenCRHCompressorGadget<G, I, ConstraintF, GG, IG>
where
    G: Curve,
    I: InjectiveMap<G>,
    ConstraintF: Field,
    GG: GroupGadget<G, ConstraintF>,
    IG: InjectiveMapGadget<G, I, ConstraintF, GG>,
{
    _compressor: PhantomData<I>,
    _compressor_gadget: PhantomData<IG>,
    _crh: PedersenCRHGadget<G, ConstraintF, GG>,
}

impl<G, I, ConstraintF, GG, IG, W> FixedLengthCRHGadget<PedersenCRHCompressor<G, I, W>, ConstraintF>
    for PedersenCRHCompressorGadget<G, I, ConstraintF, GG, IG>
where
    G: Curve,
    I: InjectiveMap<G>,
    ConstraintF: Field,
    GG: GroupGadget<G, ConstraintF>,
    IG: InjectiveMapGadget<G, I, ConstraintF, GG>,
    W: PedersenWindow,
{
    type OutputGadget = IG::OutputGadget;
    type ParametersGadget = PedersenCRHGadgetParameters<G, W, ConstraintF, GG>;

    fn check_evaluation_gadget<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        parameters: &Self::ParametersGadget,
        input: &[UInt8],
    ) -> Result<Self::OutputGadget, SynthesisError> {
        let result = PedersenCRHGadget::<G, ConstraintF, GG>::check_evaluation_gadget(
            cs.ns(|| "PedCRH"),
            parameters,
            input,
        )?;
        IG::evaluate_map(cs.ns(|| "InjectiveMap"), &result)
    }
}
