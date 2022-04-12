use std::marker::PhantomData;

use algebra::{Group, PrimeField};
use poly_commit::{
    DomainExtendedPolyCommitVerifierGadget,
    ipa_pc::{InnerProductArgPC, InnerProductArgGadget}
};
use primitives::{PoseidonHash, PoseidonParameters, SBox};
use marlin::{
    constraints::{
        data_structures::{ProofGadget as MarlinProofGadget, VerifierKeyGadget},
        MarlinVerifierGadget
    },
};
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use r1cs_crypto::{PoseidonHashGadget, SBoxGadget, FieldBasedHashGadget};
use r1cs_std::fields::fp::FpGadget;

use crate::darlin::DomainExtendedIpaPc;

pub mod base;
pub mod wrap;
pub mod merge;

pub(crate) type PCGadget<G, GG, FS, FSG> = DomainExtendedPolyCommitVerifierGadget<
    <G as Group>::BaseField,
    G,
    InnerProductArgPC<G, FS>,
    InnerProductArgGadget<<G as Group>::BaseField, FSG, G, GG>,
>;
pub(crate) type MarlinVkGadget<G, GG, FS, FSG> = VerifierKeyGadget<
    G,
    DomainExtendedIpaPc<G, FS>,
    PCGadget<G, GG, FS, FSG>
>;
pub(crate) type ProofGadget<G, GG, FS, FSG> = MarlinProofGadget<
    G,
    DomainExtendedIpaPc<G, FS>,
    PCGadget<G, GG, FS, FSG>
>;
pub(crate) type VerifierGadget<G, GG, FS, FSG> = MarlinVerifierGadget<
    G,
    GG,
    DomainExtendedIpaPc<G, FS>,
    PCGadget<G, GG, FS, FSG>
>;
pub(crate) type FieldHash<F, P, SB> = PoseidonHash<F, P, SB>; 
pub(crate) type FieldHashGadget<F, P, SB, SBG> = PoseidonHashGadget<F, P, SB, SBG>;

pub trait StateTransitionGadget<ConstraintF: PrimeField>: {
    type InputState;
    type OutputState;
    
    fn enforce_state_transition<CS: ConstraintSystemAbstract<ConstraintF>>(
        self,
        cs: CS,
        input_state: Self::InputState,
    ) -> Result<Self::OutputState, SynthesisError>;
}

pub struct HashChainTransitionGadget<
    F: PrimeField,
    P: PoseidonParameters<Fr = F>,
    SB: SBox<Field = F, Parameters = P>,
    SBG: SBoxGadget<F, SB>,
> {
    incremental: FpGadget<F>,
    _hash_params: PhantomData<P>,
    _sbox: PhantomData<SB>,
    _sbox_gadget: PhantomData<SBG>
}

impl<F, P, SB, SBG> HashChainTransitionGadget<F, P, SB, SBG>
where
    F: PrimeField,
    P: PoseidonParameters<Fr = F>,
    SB: SBox<Field = F, Parameters = P>,
    SBG: SBoxGadget<F, SB>,
{
    pub fn new(incremental: FpGadget<F>) -> Self {
        Self {
            incremental,
            _hash_params: PhantomData,
            _sbox: PhantomData,
            _sbox_gadget: PhantomData,
        }
    }
}

impl<F, P, SB, SBG> StateTransitionGadget<F> for HashChainTransitionGadget<F, P, SB, SBG>
where
    F: PrimeField,
    P: PoseidonParameters<Fr = F>,
    SB: SBox<Field = F, Parameters = P>,
    SBG: SBoxGadget<F, SB>,
{
    type InputState = FpGadget<F>;
    type OutputState = FpGadget<F>;

    fn enforce_state_transition<CS: ConstraintSystemAbstract<F>>(
        self,
        cs: CS,
        input_state: Self::InputState,
    ) -> Result<Self::OutputState, SynthesisError> 
    {
        FieldHashGadget::<F, P, SB, SBG>::enforce_hash_constant_length(
            cs,
            &[input_state, self.incremental]
        )
    }
}