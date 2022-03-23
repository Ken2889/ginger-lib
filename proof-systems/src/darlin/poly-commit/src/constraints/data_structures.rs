use crate::{
    BDFGMultiPointProof, PCKey, PCVerifierState, PolynomialCommitment,
    PolynomialCommitmentVerifierGadget, PolynomialLabel,
};
use algebra::{Group, PrimeField};
use r1cs_std::prelude::AllocGadget;
use std::fmt::Debug;

/// A commitment gadget plus its label, needed for reference.
#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
pub struct LabeledCommitmentGadget<
    PCG: PolynomialCommitmentVerifierGadget<ConstraintF, G, PC>,
    ConstraintF: PrimeField,
    G: Group<BaseField = ConstraintF>,
    PC: PolynomialCommitment<G>,
> {
    label: PolynomialLabel,
    commitment: PCG::CommitmentGadget,
}

impl<PCG, ConstraintF, G, PC> LabeledCommitmentGadget<PCG, ConstraintF, G, PC>
where
    PCG: PolynomialCommitmentVerifierGadget<ConstraintF, G, PC>,
    ConstraintF: PrimeField,
    G: Group<BaseField = ConstraintF>,
    PC: PolynomialCommitment<G>,
{
    /// Instantiate a new labeled commitment from a label and a commitment gadget.
    pub fn new(label: PolynomialLabel, commitment: PCG::CommitmentGadget) -> Self {
        Self { label, commitment }
    }

    /// Return the label for `self`.
    pub fn label(&self) -> &String {
        &self.label
    }

    /// Retrieve the commitment from `self`.
    pub fn commitment(&self) -> &PCG::CommitmentGadget {
        &self.commitment
    }
}

/// Define interface for a gadget representing an opening proof for a multi-point assertion
pub trait MultiPointProofGadget<
    ConstraintF: PrimeField,
    G: Group<BaseField = ConstraintF>,
    MPP: BDFGMultiPointProof<G>,
>: AllocGadget<MPP, ConstraintF>
{
    /// Type of commitment gadget
    type CommitmentGadget;
    /// Type of the opening proof gadget for a single-point assertion
    type ProofGadget;

    /// get the proof gadget for the combined single-point assertion
    fn get_proof(&self) -> &Self::ProofGadget;

    /// get the commitment of polynomial h, which is computed in the opening proof of multi-point assertion
    fn get_h_commitment(&self) -> &Self::CommitmentGadget;
}

/// Gadget for the state returned by verifier in case of successful verification
pub trait VerifierStateGadget<VS: PCVerifierState, ConstraintF: PrimeField>:
    Clone + Debug + Eq + PartialEq + AllocGadget<VS, ConstraintF>
{
}
/// Interface for the gadget representing the verifier key
pub trait VerifierKeyGadget<VK: PCKey, ConstraintF: PrimeField>:
    Clone + Debug + Eq + PartialEq + AllocGadget<VK, ConstraintF>
{
    /// Get the maximum degree for a segment of a polynomial whose commitments can be verified
    /// with `self`
    fn degree(&self) -> usize;

    /// Get the gadget for the hash of the verifier key `VK` represented by `self`
    fn get_hash(&self) -> &[u8];
}
