//! Proof carrying data from accumulator SNARKS. For now, it includes only the
//! following basic elements:
//!     - trait for recursive circuits,
//!     - verifier trait for proof carrying data, and their implementation
//!     for SimpleMarlin and FinalDarlin PCDs.
use crate::darlin::{
    accumulators::{
        dlog::{DualDLogItem, DualDLogItemAccumulator},
        ItemAccumulator,
    },
    pcd::{
        error::PCDError,
        final_darlin::{FinalDarlinPCD, FinalDarlinPCDVerifierKey, data_structures::FinalDarlinDeferredData},
        simple_marlin::{SimpleMarlinPCD, SimpleMarlinPCDVerifierKey},
    },
};
use algebra::{serialize::*, Group, ToConstraintField, UniformRand};
use fiat_shamir::FiatShamirRng;
use poly_commit::ipa_pc::{CommitterKey as DLogCommitterKey, IPACurve};
use r1cs_core::ConstraintSynthesizer;
use rand::RngCore;
use std::fmt::Debug;
use derivative::Derivative;
use digest::Digest;

pub mod scheme;
pub mod error;
pub mod final_darlin;
pub mod simple_marlin;

/// Trait for the recursive circuit of a PCD node in G. Both witnesses and public inputs
/// are derived from previous proofs (PCDs) and some additional data ("payload").
/// A recursive circuit comes with a universal circuit interface, comprised of
///     - `user inputs` (i.e. the proof "statement") and
///     - `system inputs`, which is the data due to amortization and split verification,
///     aka deferred checks.
/// The additional data is used only by dedicated circuits such as a base proofs or
/// a finalizing block proofs. For the ordinary merger nodes, it is simply `None`.
pub trait PCDCircuit<G: IPACurve>: ConstraintSynthesizer<G::ScalarField> {
    /// Any data that may be needed to bootstrap the circuit that is not covered by the other
    /// fields.
    type SetupData: Clone;

    /// Additional data to be processed by the circuit.
    /// This might be related to recursion (incremental "payload"). In our PCD it is  
    /// supplementary witness data to serve additional business logic of the circuit.
    type AdditionalData;

    /// Elements that are deferred during recursion. The are derived from the PCDs
    /// passed by the nodes "below"
    type SystemInputs: ToConstraintField<G::ScalarField> + Debug + Clone;

    /// PCD type the circuit needs to verify
    type PreviousPCD: PCD;

    /// Initialize the circuit state without explicitly assigning inputs and witnesses.
    /// To be used to generate pk and vk.
    fn init(config: Self::SetupData) -> Self;

    /// Assign a concrete state to the circuit, using previous proofs and some "payload".
    /// As the circuit needs to verify previous proofs, it also needs the corresponding vks;
    fn init_state(
        config: Self::SetupData,
        previous_proofs_data: Vec<Self::PreviousPCD>,
        previous_proofs_vks: Vec<<Self::PreviousPCD as PCD>::PCDVerifierKey>,
        additional_data: Self::AdditionalData,
    ) -> Self;

    /// Extract the system inputs from a concrete instantiation of the circuit.
    /// Return Error if it's not possible to derive SystemInputs.
    fn get_sys_ins(&self) -> Result<&Self::SystemInputs, PCDError>;

    /// Extract the user inputs from a concrete instantiation of the circuit.
    /// Return Error if it's not possible to derive UserInputs.
    fn get_usr_ins(&self) -> Result<Vec<G::ScalarField>, PCDError>;

    // TODO: Think about having an additional get_circuit_inputs() function if
    //       the two above don't turn out to be flexible enough for our applications.
}

/// This trait expresses the verifier for proof carrying data from accumulator SNARKs.
/// The PCD is assumed to process a set of proof carrying data consisting of
///     - a statement,
///     - accumulator SNARK proof (i.e. a SNARK proof plus its accumulator)
pub trait PCD: Sized + Send + Sync {
    type PCDAccumulator: ItemAccumulator;
    type PCDVerifierKey: AsRef<<Self::PCDAccumulator as ItemAccumulator>::AccumulatorVerifierKey>;

    /// Perform only the efficient part (i.e. sublinear w.r.t. the circuit size) of proof verification.
    /// Typically includes few algebraic operations, e.g. the verification of Marlin's sumcheck
    /// equations, batching commitments and their claimed openings, dlog reduction,and so on.
    /// Return the accumulator for the proof if verification was successful,
    /// Error otherwise.
    fn succinct_verify(
        &self,
        vk: &Self::PCDVerifierKey,
    ) -> Result<<Self::PCDAccumulator as ItemAccumulator>::Item, PCDError>;

    /// Perform the non-efficient part of proof verification.
    /// Verify / decide the current accumulator, by checking the non-efficient predicate.
    /// Typically involves one or several MSMs.
    fn hard_verify<R: RngCore>(
        &self,
        acc: <Self::PCDAccumulator as ItemAccumulator>::Item,
        vk: &Self::PCDVerifierKey,
        rng: &mut R,
    ) -> Result<bool, PCDError> {
        <Self::PCDAccumulator as ItemAccumulator>::check_items::<R>(vk.as_ref(), &[acc], rng)
            .map_err(|e| PCDError::FailedHardVerification(e.to_string()))
    }

    /// Perform full verification of `self`, i.e. both succinct and hard part.
    fn verify<R: RngCore>(&self, vk: &Self::PCDVerifierKey, rng: &mut R) -> Result<bool, PCDError> {
        let acc = self.succinct_verify(vk)?;
        self.hard_verify::<R>(acc, vk, rng)
    }

    /// Return an identifier for this PCD
    /// TODO: Return an enum instead of a String when everything will be ready ?
    fn get_id() -> String;
}

/// Node of a PCD scheme, i.e. an entity able to verify and eventually accumulate
/// incoming PCD(s) to produce a new one, defined over a cycle of curves.
/// The kind of PCD(s) the node verifies, the circuit through which a proof of such
/// verification is created, and the new one that it produces, must uniquely define
/// its role inside the PCD scheme.
pub trait PCDNode<
    G1: IPACurve<BaseField = <G2 as Group>::ScalarField>
        + ToConstraintField<<G2 as Group>::ScalarField>,
    G2: IPACurve<BaseField = <G1 as Group>::ScalarField>
        + ToConstraintField<<G1 as Group>::ScalarField>,
> 
{
    /// The key used by the node to create proofs of `Self::Circuit`.
    type ProverKey: Clone + Debug + Eq + PartialEq + CanonicalSerialize + CanonicalDeserialize;
    /// The key used by the node to verify proofs of `Self::Circuit`.
    type VerifierKey: Clone + Debug + Eq + PartialEq + CanonicalSerialize + CanonicalDeserialize;
    /// The PCD the node is able to verify. Its verification procedure should be enforced also in `Self::Circuit`.
    type InputPCD: PCD;
    /// The PCD the node is able to produce. A proof of `Self::Circuit` and the data required to verify
    /// it, should be part of this PCD.
    type OutputPCD: PCD;
    /// The circuit that verifies Self::InputPCD. The proofs created with it and the public inputs required to verify
    /// them should be part of Self::OutputPCD.
    type Circuit: PCDCircuit<G1, PreviousPCD = Self::InputPCD>;

    /// Generate the index-specific (i.e., circuit-specific) prover and verifier
    /// keys from the dedicated PCDCircuit.
    /// This is a deterministic algorithm that anyone can rerun.
    fn index<D: Digest>(
        committer_key: &DLogCommitterKey<G1>,
        config: <Self::Circuit as PCDCircuit<G1>>::SetupData,
    ) -> Result<(Self::ProverKey, Self::VerifierKey), PCDError>;

    /// Create and return a new PCD, given previous PCDs and a PCDCircuit
    /// that (partially) verify them along with some additional data.
    fn prove(
        index_pk: &Self::ProverKey,
        pc_pk: &DLogCommitterKey<G1>,
        config: <Self::Circuit as PCDCircuit<G1>>::SetupData,
        previous: Vec<Self::InputPCD>,
        additional_data: <Self::Circuit as PCDCircuit<G1>>::AdditionalData,
        zk: bool,
        zk_rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::OutputPCD, PCDError>;
}

const GENERAL_PCD_IDENTIFIER: &str = "General";

#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
/// Achieve polymorphism for PCD via an enumerable. This provides nice APIs for
/// the proof aggregation implementation and testing.
pub enum GeneralPCD<'a, G1: IPACurve, G2: IPACurve, FS: FiatShamirRng + 'static> {
    SimpleMarlin(SimpleMarlinPCD<'a, G1, FS>),
    FinalDarlin(FinalDarlinPCD<'a, G1, G2, FS>),
}

// Testing functions
impl<'a, G1, G2, FS> GeneralPCD<'a, G1, G2, FS>
where
    G1: IPACurve<BaseField = <G2 as Group>::ScalarField>
        + ToConstraintField<<G2 as Group>::ScalarField>,
    G2: IPACurve<BaseField = <G1 as Group>::ScalarField>
        + ToConstraintField<<G1 as Group>::ScalarField>,
    FS: FiatShamirRng,
{
    pub fn randomize_usr_ins<R: RngCore>(&mut self, rng: &mut R) {
        match self {
            Self::SimpleMarlin(simple_marlin) => {
                // No sys ins (for now) for SimpleMarlin, so modify the usr_ins instead
                let ins_len = simple_marlin.usr_ins.len();
                simple_marlin.usr_ins = (0..ins_len).map(|_| G1::ScalarField::rand(rng)).collect();
            }
            Self::FinalDarlin(final_darlin) => {
                let ins_len = final_darlin.usr_ins.len();
                final_darlin.usr_ins = (0..ins_len).map(|_| G1::ScalarField::rand(rng)).collect();
            }
        }
    }

    pub fn randomize_sys_ins<R: RngCore>(
        &mut self,
        ck_g1: &DLogCommitterKey<G1>,
        ck_g2: &DLogCommitterKey<G2>,
        rng: &mut R,
    ) {
        match self {
            Self::SimpleMarlin(simple_marlin) => {
                // No sys ins (for now) for SimpleMarlin, so modify the usr_ins instead
                let ins_len = simple_marlin.usr_ins.len();
                simple_marlin.usr_ins = (0..ins_len).map(|_| G1::ScalarField::rand(rng)).collect();
            }
            Self::FinalDarlin(final_darlin) => {
                final_darlin.final_darlin_proof.deferred =
                    FinalDarlinDeferredData::<G1, G2>::generate_random::<R, FS>(rng, ck_g1, ck_g2);
            }
        }
    }
}

/// We can re-use the FinalDarlinPCDVerifierKey for GeneralPCD as it contains both
/// committer keys, and a CoboundaryMarlin and FinalDarlinProof are both verifiable
/// with a standard Marlin Verifier key. Let's introduce a new type just to be clean.
pub type DualPCDVerifierKey<'a, G1, G2, FS> = FinalDarlinPCDVerifierKey<'a, G1, G2, FS>;

impl<'a, G1, G2, FS> PCD for GeneralPCD<'a, G1, G2, FS>
where
    G1: IPACurve<BaseField = <G2 as Group>::ScalarField>
        + ToConstraintField<<G2 as Group>::ScalarField>,
    G2: IPACurve<BaseField = <G1 as Group>::ScalarField>
        + ToConstraintField<<G1 as Group>::ScalarField>,
    FS: FiatShamirRng + 'static,
{
    type PCDAccumulator = DualDLogItemAccumulator<'a, G1, G2, FS>;
    type PCDVerifierKey = DualPCDVerifierKey<'a, G1, G2, FS>;

    fn succinct_verify(
        &self,
        vk: &Self::PCDVerifierKey,
    ) -> Result<<Self::PCDAccumulator as ItemAccumulator>::Item, PCDError> {
        match self {
            Self::SimpleMarlin(simple_marlin) => {
                // Works because a FinalDarlinVk is a MarlinVk
                let simple_marlin_vk =
                    SimpleMarlinPCDVerifierKey(vk.final_darlin_vk, vk.dlog_vks.0);
                let acc = simple_marlin.succinct_verify(&simple_marlin_vk)?;
                Ok(DualDLogItem(vec![acc], vec![]))
            }
            Self::FinalDarlin(final_darlin) => final_darlin.succinct_verify(vk),
        }
    }

    fn get_id() -> String {
        GENERAL_PCD_IDENTIFIER.to_string()
    }
}
