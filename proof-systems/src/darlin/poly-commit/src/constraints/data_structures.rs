use crate::{BDFGMultiPointProof, PCKey, PCVerifierState, PolynomialLabel};
use algebra::{Group, PrimeField};
use r1cs_std::groups::GroupGadget;
use r1cs_std::prelude::AllocGadget;
use std::fmt::Debug;
use std::marker::PhantomData;
#[cfg(feature = "boneh-with-single-point-batch")]
use r1cs_std::boolean::Boolean;

/// A commitment gadget plus its label, needed for reference.
#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
pub struct LabeledCommitmentGadget<
    ConstraintF: PrimeField,
    G: Group<BaseField = ConstraintF>,
    GG: GroupGadget<G, ConstraintF>,
> {
    label: PolynomialLabel,
    commitment: GG,
    _constraintf: PhantomData<ConstraintF>,
    _group: PhantomData<G>,
}

impl<ConstraintF, G, GG> LabeledCommitmentGadget<ConstraintF, G, GG>
where
    ConstraintF: PrimeField,
    G: Group<BaseField = ConstraintF>,
    GG: GroupGadget<G, ConstraintF>,
{
    /// Instantiate a new labeled commitment from a label and a commitment gadget.
    pub fn new(label: PolynomialLabel, commitment: GG) -> Self {
        Self {
            label,
            commitment,
            _constraintf: PhantomData::<ConstraintF>,
            _group: PhantomData::<G>,
        }
    }

    /// Return the label for `self`.
    pub fn label(&self) -> &String {
        &self.label
    }

    /// Retrieve the commitment from `self`.
    pub fn commitment(&self) -> &GG {
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

    /// get the evaluations of the polynomials over the batching point
    #[cfg(feature = "boneh-with-single-point-batch")]
    fn get_evaluations(&self) -> &Vec<Vec<Boolean>>;
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
