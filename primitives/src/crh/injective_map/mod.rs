use crate::{CryptoError, Error};
use algebra::bytes::ToBytes;
use rand::Rng;
use std::{fmt::Debug, hash::Hash, marker::PhantomData};

use super::{
    bowe_hopwood::{BoweHopwoodPedersenCRH, BoweHopwoodPedersenParameters, PedersenWindow},
    FixedLengthCRH,
};
use algebra::{
    curves::{
        Curve,
        models::{ModelParameters, TEModelParameters},
        twisted_edwards_extended::TEExtended,
    },
};

use serde::{Deserialize, Serialize};

pub trait InjectiveMap<G: Curve> {
    type Output: ToBytes + Serialize + for<'a> Deserialize<'a> + Clone + Eq + Hash + Default + Debug;
    fn injective_map(ge: &G) -> Result<Self::Output, CryptoError>;
}

pub struct TECompressor;

impl<P: TEModelParameters> InjectiveMap<TEExtended<P>> for TECompressor {
    type Output = <P as ModelParameters>::BaseField;

    fn injective_map(ge: &TEExtended<P>) -> Result<Self::Output, CryptoError> {
        if !ge.is_in_correct_subgroup_assuming_on_curve() {
            return Err(CryptoError::InvalidElement(format!("{}", ge)));
        }
        Ok(ge.x)
    }
}

pub struct BoweHopwoodPedersenCRHCompressor<G: Curve, I: InjectiveMap<G>, W: PedersenWindow> {
    _group: PhantomData<G>,
    _compressor: PhantomData<I>,
    _crh: BoweHopwoodPedersenCRH<G, W>,
}

impl<G: Curve, I: InjectiveMap<G>, W: PedersenWindow> FixedLengthCRH
    for BoweHopwoodPedersenCRHCompressor<G, I, W>
{
    const INPUT_SIZE_BITS: usize = BoweHopwoodPedersenCRH::<G, W>::INPUT_SIZE_BITS;
    type Output = I::Output;
    type Parameters = BoweHopwoodPedersenParameters<G>;

    fn setup<R: Rng>(rng: &mut R) -> Result<Self::Parameters, Error> {
        let time = start_timer!(|| format!("BoweHopwoodPedersenCRHCompressor::Setup"));
        let params = BoweHopwoodPedersenCRH::<G, W>::setup(rng);
        end_timer!(time);
        params
    }

    fn evaluate(parameters: &Self::Parameters, input: &[u8]) -> Result<Self::Output, Error> {
        let eval_time = start_timer!(|| "BoweHopwoodPedersenCRHCompressor::Eval");
        let result = I::injective_map(&BoweHopwoodPedersenCRH::<G, W>::evaluate(parameters, input)?)?;
        end_timer!(eval_time);
        Ok(result)
    }
}
