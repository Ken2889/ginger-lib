use algebra::Field;
use std::fmt::Debug;

use primitives::prf::PRF;
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};

use r1cs_std::prelude::*;

pub mod blake2s;
pub mod ripemd160;
pub mod sha256;

pub trait PRFGadget<P: PRF, ConstraintF: Field> {
    type OutputGadget: EqGadget<ConstraintF>
        + ToBytesGadget<ConstraintF>
        + AllocGadget<P::Output, ConstraintF>
        + Clone
        + Debug;

    fn new_seed<CS: ConstraintSystemAbstract<ConstraintF>>(cs: CS, output: &P::Seed) -> Vec<UInt8>;

    fn check_evaluation_gadget<CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        seed: &[UInt8],
        input: &[UInt8],
    ) -> Result<Self::OutputGadget, SynthesisError>;
}
