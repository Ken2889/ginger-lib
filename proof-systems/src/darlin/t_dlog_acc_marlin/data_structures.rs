//! The data structures for Coboundary Marlin:
//!     - prover and verifier key,
//!     - the SNARK proof,
//! and implementations for serialization and deserialization.
use crate::darlin::t_dlog_acc_marlin::iop::indexer::Index;
use crate::darlin::t_dlog_acc_marlin::EvaluationsOnDomain;
use crate::darlin::t_dlog_acc_marlin::IOP;
use crate::darlin::IPACurve;
use algebra::serialize::*;
use algebra::{
    get_best_evaluation_domain, DensePolynomial, Group, GroupVec, PrimeField, ToBits, ToBytes,
    ToConstraintField, UniformRand,
};
use bench_utils::add_to_trace;
use derivative::Derivative;
use fiat_shamir::FiatShamirRng;
use marlin::iop::LagrangeKernel;
use num_traits::Zero;
use poly_commit::ipa_pc::InnerProductArgPC;
use poly_commit::{DomainExtendedPolynomialCommitment, PolynomialCommitment};
use rand_core::RngCore;
use std::marker::PhantomData;

/// Our proving system uses IPA/DLOG polynomial commitment scheme.
pub(crate) type PC<G, D> = DomainExtendedPolynomialCommitment<G, InnerProductArgPC<G, D>>;

/// The verification key for a specific R1CS.
#[derive(Derivative)]
#[derivative(
    Clone(bound = ""),
    Debug(bound = ""),
    Eq(bound = ""),
    PartialEq(bound = "")
)]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct VerifierKey<G1: IPACurve, G2: IPACurve, FS: FiatShamirRng + 'static> {
    /// The index itself.
    pub index: Index<G1, G2>,
    /// Commitments of the lagrange polynomials over the input domain.
    pub lagrange_comms: Vec<<PC<G1, FS> as PolynomialCommitment<G1>>::Commitment>,
    /// Hash of the above elements
    pub vk_hash: Vec<u8>,
}

impl<G1: IPACurve, G2: IPACurve, FS: FiatShamirRng + 'static> VerifierKey<G1, G2, FS> {
    pub fn get_hash(&self) -> &[u8] {
        &self.vk_hash
    }
}

/// The prover key for a specific R1CS.
#[derive(Derivative)]
#[derivative(
    Clone(bound = ""),
    Debug(bound = ""),
    Eq(bound = ""),
    PartialEq(bound = "")
)]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct ProverKey<G1: IPACurve, G2: IPACurve, FS: FiatShamirRng + 'static> {
    /// The index verifier key.
    pub index_vk: VerifierKey<G1, G2, FS>,
}

/// The SNARK proof itself.
#[derive(Derivative)]
#[derivative(
    Clone(bound = ""),
    Debug(bound = ""),
    Eq(bound = ""),
    PartialEq(bound = "")
)]
pub struct Proof<G1: IPACurve, G2: IPACurve, FS: FiatShamirRng + 'static> {
    /// Commitments to the polynomials produced by the prover
    pub commitments: Vec<Vec<<PC<G1, FS> as PolynomialCommitment<G1>>::Commitment>>,
    /// Evaluations of these polynomials.
    pub evaluations: Vec<G1::ScalarField>,
    /// A batch evaluation proof from the polynomial commitment.
    pub pc_proof: <PC<G1, FS> as PolynomialCommitment<G1>>::MultiPointProof,

    g2: PhantomData<G2>,
}

/// An item to be collected in an inner-sumcheck accumulator.
#[derive(Clone, Debug, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct SumcheckItem<G: IPACurve> {
    /// Sampling point.
    pub alpha: G::ScalarField,
    /// Batching randomness.
    pub eta: Vec<G::ScalarField>,
    /// Commitment of the batched circuit polynomials.
    pub c: GroupVec<G>,
}

impl<G: IPACurve> ToBytes for SumcheckItem<G> {
    fn write<W: Write>(&self, writer: W) -> std::io::Result<()> {
        use std::io::{Error, ErrorKind};

        self.serialize_without_metadata(writer)
            .map_err(|e| Error::new(ErrorKind::Other, format! {"{:?}", e}))
    }
}

impl<G: IPACurve> SumcheckItem<G> {
    /// Generate a random (but valid) inner sumcheck accumulator item.
    pub fn generate_random<G2: IPACurve, FS: FiatShamirRng + 'static>(
        rng: &mut dyn RngCore,
        index: &Index<G, G2>,
        pc_pk: &<PC<G, FS> as PolynomialCommitment<G>>::CommitterKey,
    ) -> Self {
        // alpha is a random 128 bit challenge.
        let alpha: G::ScalarField = u128::rand(rng).into();
        let eta: Vec<_> = (0..3)
            .into_iter()
            .map(|_| G::ScalarField::rand(rng))
            .collect();

        let num_inputs = index.index_info.num_inputs;
        let num_witness = index.index_info.num_witness;
        let num_constraints = index.index_info.num_constraints;

        let domain_h = get_best_evaluation_domain::<G::ScalarField>(std::cmp::max(
            num_inputs + num_witness,
            num_constraints,
        ))
        .unwrap();

        let l_x_alpha_evals_on_h = domain_h.domain_eval_lagrange_kernel(alpha).unwrap();

        let t_evals_on_h = marlin::IOP::calculate_t(
            vec![&index.a, &index.b, &index.c].into_iter(),
            &eta,
            domain_h.clone(),
            &l_x_alpha_evals_on_h,
        )
        .unwrap();
        let t = EvaluationsOnDomain::from_vec_and_domain(t_evals_on_h.clone(), domain_h.clone())
            .interpolate();
        let (c, _) =
            <PC<G, FS> as PolynomialCommitment<G>>::commit(pc_pk, &t, false, None).unwrap();

        Self { alpha, eta, c }
    }

    /// Generate a random invalid inner sumcheck accumulator item.
    pub fn generate_invalid<G2: IPACurve, FS: FiatShamirRng + 'static>(
        rng: &mut dyn RngCore,
        index: &Index<G, G2>,
        pc_pk: &<PC<G, FS> as PolynomialCommitment<G>>::CommitterKey,
    ) -> Self {
        let mut result = Self::generate_random::<_, FS>(rng, index, pc_pk);
        for el in result.c.iter_mut() {
            *el = G::rand(rng);
        }
        result
    }

    /// Generate the trivial inner sumcheck accumulator item
    pub fn generate_trivial() -> Self {
        Self {
            alpha: G::ScalarField::zero(),
            eta: vec![G::ScalarField::zero(); 3],
            c: GroupVec::<G>::zero(),
        }
    }

    /// Compute the polynomial associated to the accumulator.
    pub fn compute_poly<G2: IPACurve>(
        &self,
        index: &Index<G, G2>,
    ) -> DensePolynomial<G::ScalarField> {
        let num_inputs = index.index_info.num_inputs;
        let num_witness = index.index_info.num_witness;
        let num_constraints = index.index_info.num_constraints;

        let domain_h = get_best_evaluation_domain::<G::ScalarField>(std::cmp::max(
            num_constraints,
            num_inputs + num_witness,
        ))
        .unwrap();

        let alpha = self.alpha;
        let l_x_alpha_evals_on_h = domain_h.domain_eval_lagrange_kernel(alpha).unwrap();

        let t_evals_on_h = marlin::IOP::calculate_t(
            vec![&index.a, &index.b, &index.c].into_iter(),
            &self.eta,
            domain_h.clone(),
            &l_x_alpha_evals_on_h,
        )
        .unwrap();
        let t_poly =
            EvaluationsOnDomain::from_vec_and_domain(t_evals_on_h.clone(), domain_h.clone())
                .interpolate();
        t_poly
    }
}

/// A dual inner-sumcheck accumulator item.
#[derive(Clone, Debug, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct DualSumcheckItem<G1: IPACurve, G2: IPACurve>(pub SumcheckItem<G1>, pub SumcheckItem<G2>);

impl<G1: IPACurve, G2: IPACurve> DualSumcheckItem<G1, G2> {
    /// Generate a random (but valid) dual inner sumcheck accumulator
    pub fn generate_random<FS: FiatShamirRng + 'static>(
        rng: &mut dyn RngCore,
        index_g1: &Index<G1, G2>,
        index_g2: &Index<G2, G1>,
        pc_pk_g1: &<PC<G1, FS> as PolynomialCommitment<G1>>::CommitterKey,
        pc_pk_g2: &<PC<G2, FS> as PolynomialCommitment<G2>>::CommitterKey,
    ) -> Self {
        Self(
            SumcheckItem::generate_random::<G2, FS>(rng, index_g1, pc_pk_g1),
            SumcheckItem::generate_random::<G1, FS>(rng, index_g2, pc_pk_g2),
        )
    }

    /// Generate a random invalid instance of `DualSumcheckItem`, for test purposes only.
    /// The "left" accumulator (`self.0`) is invalid, while the "right" one (`self.1`) is valid.
    pub fn generate_invalid_left<FS: FiatShamirRng + 'static>(
        rng: &mut dyn RngCore,
        index_g1: &Index<G1, G2>,
        index_g2: &Index<G2, G1>,
        pc_pk_g1: &<PC<G1, FS> as PolynomialCommitment<G1>>::CommitterKey,
        pc_pk_g2: &<PC<G2, FS> as PolynomialCommitment<G2>>::CommitterKey,
    ) -> Self {
        Self(
            SumcheckItem::generate_invalid::<G2, FS>(rng, index_g1, pc_pk_g1),
            SumcheckItem::generate_random::<G1, FS>(rng, index_g2, pc_pk_g2),
        )
    }

    /// Generate a random invalid instance of `DualSumcheckItem`, for test purposes only.
    /// The "left" accumulator (`self.0`) is valid, while the "right" one (`self.1`) is invalid.
    pub fn generate_invalid_right<FS: FiatShamirRng + 'static>(
        rng: &mut dyn RngCore,
        index_g1: &Index<G1, G2>,
        index_g2: &Index<G2, G1>,
        pc_pk_g1: &<PC<G1, FS> as PolynomialCommitment<G1>>::CommitterKey,
        pc_pk_g2: &<PC<G2, FS> as PolynomialCommitment<G2>>::CommitterKey,
    ) -> Self {
        Self(
            SumcheckItem::generate_random::<G2, FS>(rng, index_g1, pc_pk_g1),
            SumcheckItem::generate_invalid::<G1, FS>(rng, index_g2, pc_pk_g2),
        )
    }

    /// Generate a random invalid instance of `DualDLogItem`, for test purposes only.
    /// Both accumulators are invalid.
    pub fn generate_invalid<FS: FiatShamirRng + 'static>(
        rng: &mut dyn RngCore,
        index_g1: &Index<G1, G2>,
        index_g2: &Index<G2, G1>,
        pc_pk_g1: &<PC<G1, FS> as PolynomialCommitment<G1>>::CommitterKey,
        pc_pk_g2: &<PC<G2, FS> as PolynomialCommitment<G2>>::CommitterKey,
    ) -> Self {
        Self(
            SumcheckItem::generate_invalid::<G2, FS>(rng, index_g1, pc_pk_g1),
            SumcheckItem::generate_invalid::<G1, FS>(rng, index_g2, pc_pk_g2),
        )
    }

    /// Generate the trivial dual inner sumcheck accumulator
    pub fn generate_trivial() -> Self {
        Self(
            SumcheckItem::generate_trivial(),
            SumcheckItem::generate_trivial(),
        )
    }

    /// Compute the polynomials associated to the dual accumulator.
    pub fn compute_poly(
        &self,
        index_g1: &Index<G1, G2>,
        index_g2: &Index<G2, G1>,
    ) -> (
        DensePolynomial<G1::ScalarField>,
        DensePolynomial<G2::ScalarField>,
    ) {
        (self.0.compute_poly(index_g1), self.1.compute_poly(index_g2))
    }
}

impl<G2, G1> ToConstraintField<G1::ScalarField> for DualSumcheckItem<G2, G1>
where
    G1: IPACurve<BaseField = <G2 as Group>::ScalarField>
        + ToConstraintField<<G2 as Group>::ScalarField>,
    G2: IPACurve<BaseField = <G1 as Group>::ScalarField>
        + ToConstraintField<<G1 as Group>::ScalarField>,
{
    fn to_field_elements(&self) -> Result<Vec<G1::ScalarField>, Box<dyn std::error::Error>> {
        let to_skip = <G1::ScalarField as PrimeField>::size_in_bits() - 128;
        let mut fes = Vec::new();

        // Convert self.0 into G1::ScalarField field elements

        // The commitment c of self.0 consists of native field elements only
        fes.append(&mut self.0.c.to_field_elements()?);

        let mut challenge_bits = Vec::new();
        // The alpha challenge of self.0 is a 128 bit element from G2::ScalarField.
        {
            let bits = self.0.alpha.write_bits();
            challenge_bits.extend_from_slice(&bits[to_skip..]);
        }
        // The eta challenges of self.0 are 3 random elements from G2::ScalarField.
        for fe in self.0.eta.iter() {
            let bits = fe.write_bits();
            challenge_bits.extend_from_slice(&bits);
        }

        // We pack the full bit vector into native field elements as efficient as possible (yet
        // still secure).
        fes.append(&mut challenge_bits.to_field_elements()?);

        // Convert self.1 into G1::ScalarField field elements.

        // The commitments c of self.1 are over G2::ScalarField.
        // We serialize them all to bits and pack them safely into native field elements
        let mut c_g1_bits = Vec::new();
        let c_fes = self.1.c.to_field_elements()?;
        for fe in c_fes {
            c_g1_bits.append(&mut fe.write_bits());
        }
        fes.append(&mut c_g1_bits.to_field_elements()?);

        // The challenges alpha and eta of self.1 are already over G1::ScalarField. Since only alpha
        // is a 128-bit challenge, we wouldn't save anything from packing the challenges into bits
        // as done for the challenges in self.0. Therefore we keep them as they are.
        fes.push(self.1.alpha);
        fes.append(&mut self.1.eta.clone());

        Ok(fes)
    }
}

impl<G1: IPACurve, G2: IPACurve, FS: FiatShamirRng> Proof<G1, G2, FS> {
    /// Construct a new proof.
    pub fn new(
        commitments: Vec<Vec<<PC<G1, FS> as PolynomialCommitment<G1>>::Commitment>>,
        evaluations: Vec<G1::ScalarField>,
        pc_proof: <PC<G1, FS> as PolynomialCommitment<G1>>::MultiPointProof,
    ) -> Self {
        Self {
            commitments,
            evaluations,
            pc_proof,
            g2: PhantomData,
        }
    }

    /// Prints information about the size of the proof.
    pub fn print_size_info(&self) {
        let size_of_fe_in_bytes = G1::ScalarField::zero().serialized_size();
        let mut num_comms_without_degree_bounds = 0;
        let mut size_bytes_comms_without_degree_bounds = 0;
        let mut size_bytes_proofs = 0;
        for c in self.commitments.iter().flatten() {
            num_comms_without_degree_bounds += 1;
            size_bytes_comms_without_degree_bounds += c.serialized_size();
        }

        size_bytes_proofs += self.pc_proof.serialized_size();

        let num_evals = self.evaluations.len();
        let evals_size_in_bytes = num_evals * size_of_fe_in_bytes;
        let arg_size =
            size_bytes_comms_without_degree_bounds + size_bytes_proofs + evals_size_in_bytes;
        let stats = format!(
            "Argument size in bytes: {}\n\n\
             Number of commitments without degree bounds: {}\n\
             Size (in bytes) of commitments without degree bounds: {}\n\
             Size (in bytes) of evaluation proofs: {}\n\n\
             Number of evaluations: {}\n\
             Size (in bytes) of evaluations: {}\n",
            arg_size,
            num_comms_without_degree_bounds,
            size_bytes_comms_without_degree_bounds,
            size_bytes_proofs,
            num_evals,
            evals_size_in_bytes,
        );
        add_to_trace!(|| "Statistics about proof", || stats);
    }
}

/*
    Implement SemanticallyValid for VerifierKey, ProverKey, and Proof.
*/

impl<G1: IPACurve, G2: IPACurve, FS: FiatShamirRng> algebra::SemanticallyValid
    for VerifierKey<G1, G2, FS>
{
    fn is_valid(&self) -> bool {
        true
    }
}

impl<G1: IPACurve, G2: IPACurve, FS: FiatShamirRng> algebra::SemanticallyValid
    for ProverKey<G1, G2, FS>
{
    fn is_valid(&self) -> bool {
        self.index_vk.is_valid()
    }
}

impl<G1: IPACurve, G2: IPACurve, FS: FiatShamirRng> algebra::SemanticallyValid
    for Proof<G1, G2, FS>
{
    fn is_valid(&self) -> bool {
        // Check commitments number and validity
        let num_rounds = 4;
        let comms_per_round = vec![3, 3, 2, 1];

        // Check commitments are grouped into correct num_rounds
        if self.commitments.len() != num_rounds {
            return false;
        };

        // Check that each round has the expected number of commitments
        for i in 0..comms_per_round.len() {
            if self.commitments[i].len() != comms_per_round[i] {
                return false;
            };
        }

        // Check evaluations num
        let evaluations_num = IOP::<G1, G2>::PROVER_POLYNOMIALS.len() +
            3 // boundary polynomial and the two bridge polynomials are evaluated at two different
              // points
        ;
        assert!(self.commitments.is_valid());
        assert!(self.evaluations.is_valid());
        assert!(self.pc_proof.is_valid());
        assert!(self.evaluations.len() == evaluations_num);

        self.commitments.is_valid() &&  // Check that each commitment is valid
            self.evaluations.len() == evaluations_num && // Check correct number of evaluations
            self.evaluations.is_valid() && // Check validity of each evaluation
            self.pc_proof.is_valid() // Check validity of the batch proof.
    }
}

/*
    Serialization and Deserialization utilities.
*/

impl<G1: IPACurve, G2: IPACurve, FS: FiatShamirRng> ToBytes for VerifierKey<G1, G2, FS> {
    #[inline]
    fn write<W: Write>(&self, writer: W) -> std::io::Result<()> {
        self.serialize_without_metadata(writer)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("{:?}", e)))
    }
}

impl<G1: IPACurve, G2: IPACurve, FS: FiatShamirRng> CanonicalSerialize for Proof<G1, G2, FS> {
    fn serialize<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        // Serialize commitments: we know in advance exactly how many polynomials will be
        // committed, so we can skip writing the corresponding sizes.
        for comm in self.commitments.iter().flatten() {
            CanonicalSerialize::serialize(comm, &mut writer)?;
        }

        // Serialize evaluations: again, we know the number in advance.
        for eval in self.evaluations.iter() {
            CanonicalSerialize::serialize(eval, &mut writer)?;
        }

        // Serialize pc_proof
        CanonicalSerialize::serialize(&self.pc_proof, &mut writer)
    }

    fn serialized_size(&self) -> usize {
        let mut size = 0;

        // Commitments size
        self.commitments
            .iter()
            .flatten()
            .for_each(|comm| size += comm.serialized_size());

        let evaluations_num = IOP::<G1, G2>::PROVER_POLYNOMIALS.len() + 3; // boundary polynomial and the two bridge polynomials are evaluated at two different
                                                                           // points

        // Evaluations size
        size += evaluations_num * self.evaluations[0].serialized_size();

        // PC proof size
        size += self.pc_proof.serialized_size();

        size
    }

    fn serialize_without_metadata<W: Write>(
        &self,
        mut writer: W,
    ) -> Result<(), SerializationError> {
        // Serialize commitments: we know in advance exactly how many polynomials will be
        // committed, so we can skip writing the corresponding sizes.
        for comm in self.commitments.iter().flatten() {
            CanonicalSerialize::serialize_without_metadata(comm, &mut writer)?;
        }

        // Serialize evaluations: again, we know the number in advance.
        for eval in self.evaluations.iter() {
            CanonicalSerialize::serialize_without_metadata(eval, &mut writer)?;
        }

        // Serialize pc_proof
        CanonicalSerialize::serialize_without_metadata(&self.pc_proof, &mut writer)
    }

    #[inline]
    fn serialize_uncompressed<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        // Serialize commitments: we know in advance exactly how many polynomials will be
        // committed, so we can skip writing the corresponding sizes.
        for comm in self.commitments.iter().flatten() {
            CanonicalSerialize::serialize_uncompressed(comm, &mut writer)?;
        }

        // Serialize evaluations: again, we know the number in advance.
        for eval in self.evaluations.iter() {
            CanonicalSerialize::serialize_uncompressed(eval, &mut writer)?;
        }

        // Serialize pc_proof
        CanonicalSerialize::serialize_uncompressed(&self.pc_proof, &mut writer)
    }

    #[inline]
    fn uncompressed_size(&self) -> usize {
        let mut size = 0;

        // Commitments size
        self.commitments
            .iter()
            .flatten()
            .for_each(|comm| size += comm.uncompressed_size());

        let evaluations_num = IOP::<G1, G2>::PROVER_POLYNOMIALS.len() + 3; // boundary polynomial and the two bridge polynomials are evaluated at two different
                                                                           // points

        // Evaluations size
        size += evaluations_num * self.evaluations[0].uncompressed_size();

        // PC proof size
        size += self.pc_proof.uncompressed_size();

        size
    }
}

impl<G1: IPACurve, G2: IPACurve, FS: FiatShamirRng> CanonicalDeserialize for Proof<G1, G2, FS> {
    fn deserialize<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        // Deserialize commitments
        let num_rounds = 4;
        let comms_per_round = vec![3, 3, 2, 1];
        let mut commitments = Vec::with_capacity(num_rounds);

        for i in 0..num_rounds {
            // Deserialize round commitments
            let mut round_comms = Vec::with_capacity(comms_per_round[i]);

            for _ in 0..comms_per_round[i] {
                let comm: <PC<G1, FS> as PolynomialCommitment<G1>>::Commitment =
                    CanonicalDeserialize::deserialize(&mut reader)?;
                round_comms.push(comm);
            }

            commitments.push(round_comms);
        }

        // Deserialize evaluations
        let evaluations_num = IOP::<G1, G2>::PROVER_POLYNOMIALS.len() + 3; // boundary polynomial and the two bridge polynomials are evaluated at two different
                                                                           // points

        let mut evaluations = Vec::with_capacity(evaluations_num);
        for _ in 0..evaluations_num {
            let eval: G1::ScalarField = CanonicalDeserialize::deserialize(&mut reader)?;
            evaluations.push(eval);
        }

        // Deserialize pc_proof
        let pc_proof = CanonicalDeserialize::deserialize(&mut reader)?;

        Ok(Self {
            commitments,
            evaluations,
            pc_proof,
            g2: PhantomData,
        })
    }

    fn deserialize_unchecked<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        // Deserialize commitments
        let num_rounds = 4;
        let comms_per_round = vec![3, 3, 2, 1];
        let mut commitments = Vec::with_capacity(num_rounds);

        for i in 0..num_rounds {
            // Deserialize round commitments
            let mut round_comms = Vec::with_capacity(comms_per_round[i]);

            for _ in 0..comms_per_round[i] {
                let comm: <PC<G1, FS> as PolynomialCommitment<G1>>::Commitment =
                    CanonicalDeserialize::deserialize_unchecked(&mut reader)?;
                round_comms.push(comm);
            }

            commitments.push(round_comms);
        }

        // Deserialize evaluations
        let evaluations_num = IOP::<G1, G2>::PROVER_POLYNOMIALS.len() + 3; // boundary polynomial and the two bridge polynomials are evaluated at two different
                                                                           // points

        let mut evaluations = Vec::with_capacity(evaluations_num);
        for _ in 0..evaluations_num {
            let eval: G1::ScalarField = CanonicalDeserialize::deserialize_unchecked(&mut reader)?;
            evaluations.push(eval);
        }

        // Deserialize pc_proof
        let pc_proof = CanonicalDeserialize::deserialize_unchecked(&mut reader)?;

        Ok(Self {
            commitments,
            evaluations,
            pc_proof,
            g2: PhantomData,
        })
    }

    #[inline]
    fn deserialize_uncompressed<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        // Deserialize commitments
        let num_rounds = 4;
        let comms_per_round = vec![3, 3, 2, 1];
        let mut commitments = Vec::with_capacity(num_rounds);

        for i in 0..num_rounds {
            // Deserialize round commitments
            let mut round_comms = Vec::with_capacity(comms_per_round[i]);

            for _ in 0..comms_per_round[i] {
                let comm: <PC<G1, FS> as PolynomialCommitment<G1>>::Commitment =
                    CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;
                round_comms.push(comm);
            }

            commitments.push(round_comms);
        }

        // Deserialize evaluations
        let evaluations_num = IOP::<G1, G2>::PROVER_POLYNOMIALS.len() + 3; // boundary polynomial and the two bridge polynomials are evaluated at two different
                                                                           // points

        let mut evaluations = Vec::with_capacity(evaluations_num);
        for _ in 0..evaluations_num {
            let eval: G1::ScalarField =
                CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;
            evaluations.push(eval);
        }

        // Deserialize pc_proof
        let pc_proof = CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;

        Ok(Self {
            commitments,
            evaluations,
            pc_proof,
            g2: PhantomData,
        })
    }

    #[inline]
    fn deserialize_uncompressed_unchecked<R: Read>(
        mut reader: R,
    ) -> Result<Self, SerializationError> {
        // Deserialize commitments
        let num_rounds = 4;
        let comms_per_round = vec![3, 3, 2, 1];
        let mut commitments = Vec::with_capacity(num_rounds);

        for i in 0..num_rounds {
            // Deserialize round commitments
            let mut round_comms = Vec::with_capacity(comms_per_round[i]);

            for _ in 0..comms_per_round[i] {
                let comm: <PC<G1, FS> as PolynomialCommitment<G1>>::Commitment =
                    CanonicalDeserialize::deserialize_uncompressed_unchecked(&mut reader)?;
                round_comms.push(comm);
            }

            commitments.push(round_comms);
        }

        // Deserialize evaluations
        let evaluations_num = IOP::<G1, G2>::PROVER_POLYNOMIALS.len() + 3; // boundary polynomial and the two bridge polynomials are evaluated at two different
                                                                           // points

        let mut evaluations = Vec::with_capacity(evaluations_num);
        for _ in 0..evaluations_num {
            let eval: G1::ScalarField =
                CanonicalDeserialize::deserialize_uncompressed_unchecked(&mut reader)?;
            evaluations.push(eval);
        }

        // Deserialize pc_proof
        let pc_proof = CanonicalDeserialize::deserialize_uncompressed_unchecked(&mut reader)?;

        Ok(Self {
            commitments,
            evaluations,
            pc_proof,
            g2: PhantomData,
        })
    }
}
