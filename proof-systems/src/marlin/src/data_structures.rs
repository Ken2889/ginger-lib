use crate::ahp::indexer::*;
use crate::ahp::prover::ProverMsg;
use crate::{AHPForR1CS, Vec};
use algebra::serialize::*;
use algebra::{PrimeField, ToBytes};
use derivative::Derivative;
use poly_commit::{LabeledRandomness, PCCommitment, PolynomialCommitment};

/* ************************************************************************* */
/* ************************************************************************* */
/* ************************************************************************* */

/// The universal public parameters for the argument system.
pub type UniversalSRS<F, PC> = <PC as PolynomialCommitment<F>>::UniversalParams;

/* ************************************************************************* */
/* ************************************************************************* */
/* ************************************************************************* */

/// The (AHP) verification key for a specific circuit (i.e., R1CS matrices).
/// Does include only the (commitments) of the index polynomials.
#[derive(Derivative)]
#[derivative(
    Clone(bound = ""),
    Debug(bound = ""),
    Eq(bound = ""),
    PartialEq(bound = "")
)]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct VerifierKey<F: PrimeField, PC: PolynomialCommitment<F>> {
    /// Stores information about the size of the index, as well as its field of
    /// definition.
    pub index_info: IndexInfo<F>,
    /// Commitments to the indexed polynomials.
    pub index_comms: Vec<PC::Commitment>,
}

impl<F: PrimeField, PC: PolynomialCommitment<F>> ToBytes for VerifierKey<F, PC> {
    #[inline]
    fn write<W: Write>(&self, writer: W) -> std::io::Result<()> {
        self.serialize_without_metadata(writer)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("{:?}", e)))
    }
}

impl<F: PrimeField, PC: PolynomialCommitment<F>> algebra::SemanticallyValid for VerifierKey<F, PC> {
    fn is_valid(&self) -> bool {
        // Check that the number of commitments is equal to the expected one (i.e. the number
        // of indexer polynomials).
        if self.index_comms.len() != AHPForR1CS::<F>::INDEXER_POLYNOMIALS.len() {
            return false;
        }

        // Check that each commitment is valid and non-shifted
        for comm in self.index_comms.iter() {
            if !(!comm.has_degree_bound() && comm.is_valid()) {
                return false;
            }
        }

        true
    }
}

impl<F: PrimeField, PC: PolynomialCommitment<F>> VerifierKey<F, PC> {
    /// Iterate over the commitments to indexed polynomials in `self`.
    pub fn iter(&self) -> impl Iterator<Item = &PC::Commitment> {
        self.index_comms.iter()
    }
}

/* ************************************************************************* */
/* ************************************************************************* */
/* ************************************************************************* */

/// Proving key for a specific circuit (i.e., R1CS matrices).
#[derive(Derivative)]
#[derivative(
    Clone(bound = ""),
    Debug(bound = ""),
    Eq(bound = ""),
    PartialEq(bound = "")
)]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct ProverKey<F: PrimeField, PC: PolynomialCommitment<F>> {
    /// The index verifier key.
    pub index_vk: VerifierKey<F, PC>,
    /// The randomness for the index polynomial commitments.
    // TODO: We most likely can randomize the inner sumcheck argument to
    //       obtain zk with respect to the circuit that is proven, but that needs
    //       to be investigated. (Such property might be of interest for private
    //       sidechains.)
    pub index_comm_rands: Vec<LabeledRandomness<PC::Randomness>>,
    /// The index itself.
    pub index: Index<F>,
}

impl<F: PrimeField, PC: PolynomialCommitment<F>> algebra::SemanticallyValid for ProverKey<F, PC> {
    fn is_valid(&self) -> bool {
        self.index_vk.is_valid() && self.index.is_valid()
    }
}

/* ************************************************************************* */
/* ************************************************************************* */
/* ************************************************************************* */

/// A zkSNARK proof.
#[derive(Derivative)]
#[derivative(
    Clone(bound = ""),
    Debug(bound = ""),
    Eq(bound = ""),
    PartialEq(bound = "")
)]
pub struct Proof<F: PrimeField, PC: PolynomialCommitment<F>> {
    /// Commitments to the polynomials produced by the AHP prover.
    pub commitments: Vec<Vec<PC::Commitment>>,
    /// Evaluations of these polynomials.
    pub evaluations: Vec<F>,
    /// The field elements sent by the prover.
    pub prover_messages: Vec<ProverMsg<F>>,
    /// An evaluation proof from the polynomial commitment.
    pub pc_proof: PC::BatchProof,
}

impl<F: PrimeField, PC: PolynomialCommitment<F>> algebra::SemanticallyValid for Proof<F, PC> {
    fn is_valid(&self) -> bool {
        // Check commitments number and validity
        let num_rounds = 3;
        let comms_per_round = vec![3, 3, 2];

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
        let evaluations_num = AHPForR1CS::<F>::PROVER_POLYNOMIALS.len() +
            AHPForR1CS::<F>::INDEXER_POLYNOMIALS.len() +
            2 // boundary polynomials are evaluated at two different points
        ;

        self.commitments.is_valid() &&  // Check that each commitment is valid
            self.evaluations.len() == evaluations_num && // Check correct number of evaluations
            self.evaluations.is_valid() && // Check validity of each evaluation
            self.prover_messages.len() == num_rounds &&// Check correct number of prover messages
            self.prover_messages.is_valid() && // Check prover messages are valid
            self.pc_proof.is_valid() // Check validity of the batch proof.
    }
}

impl<F: PrimeField, PC: PolynomialCommitment<F>> CanonicalSerialize for Proof<F, PC> {
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

        // No need to serialize prover_messages as we don't have any

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

        let evaluations_num = AHPForR1CS::<F>::PROVER_POLYNOMIALS.len() +
            AHPForR1CS::<F>::INDEXER_POLYNOMIALS.len() +
            2 // boundary polynomials are evaluated at two different points
        ;

        // Evaluations size
        size += evaluations_num * self.evaluations[0].serialized_size();

        // No prover messages

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

        // No need to serialize prover_messages as we don't have any

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

        // No need to serialize prover_messages as we don't have any

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

        let evaluations_num = AHPForR1CS::<F>::PROVER_POLYNOMIALS.len() +
            AHPForR1CS::<F>::INDEXER_POLYNOMIALS.len() +
            2 // boundary polynomials are evaluated at two different points
            ;

        // Evaluations size
        size += evaluations_num * self.evaluations[0].uncompressed_size();

        // No prover messages

        // PC proof size
        size += self.pc_proof.uncompressed_size();

        size
    }
}

impl<F: PrimeField, PC: PolynomialCommitment<F>> CanonicalDeserialize for Proof<F, PC> {
    fn deserialize<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        // Deserialize commitments
        let num_rounds = 3;
        let comms_per_round = vec![3, 3, 2];
        let mut commitments = Vec::with_capacity(num_rounds);

        for i in 0..num_rounds {
            // Deserialize round commitments
            let mut round_comms = Vec::with_capacity(comms_per_round[i]);

            for _ in 0..comms_per_round[i] {
                let comm: PC::Commitment = CanonicalDeserialize::deserialize(&mut reader)?;
                round_comms.push(comm);
            }

            commitments.push(round_comms);
        }

        // Deserialize evaluations
        let evaluations_num = AHPForR1CS::<F>::PROVER_POLYNOMIALS.len() +
            AHPForR1CS::<F>::INDEXER_POLYNOMIALS.len() +
            2 // boundary polynomials are evaluated at two different points
        ;

        let mut evaluations = Vec::with_capacity(evaluations_num);
        for _ in 0..evaluations_num {
            let eval: F = CanonicalDeserialize::deserialize(&mut reader)?;
            evaluations.push(eval);
        }

        // Deserialize pc_proof
        let pc_proof = CanonicalDeserialize::deserialize(&mut reader)?;

        Ok(Self {
            commitments,
            evaluations,
            prover_messages: vec![ProverMsg::<F>::EmptyMessage; num_rounds],
            pc_proof,
        })
    }

    fn deserialize_unchecked<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        // Deserialize commitments
        let num_rounds = 3;
        let comms_per_round = vec![3, 3, 2];
        let mut commitments = Vec::with_capacity(num_rounds);

        for i in 0..num_rounds {
            // Deserialize round commitments
            let mut round_comms = Vec::with_capacity(comms_per_round[i]);

            for _ in 0..comms_per_round[i] {
                let comm: PC::Commitment =
                    CanonicalDeserialize::deserialize_unchecked(&mut reader)?;
                round_comms.push(comm);
            }

            commitments.push(round_comms);
        }

        // Deserialize evaluations
        let evaluations_num = AHPForR1CS::<F>::PROVER_POLYNOMIALS.len() +
            AHPForR1CS::<F>::INDEXER_POLYNOMIALS.len() +
            2 // boundary polynomials are evaluated at two different points
            ;

        let mut evaluations = Vec::with_capacity(evaluations_num);
        for _ in 0..evaluations_num {
            let eval: F = CanonicalDeserialize::deserialize_unchecked(&mut reader)?;
            evaluations.push(eval);
        }

        // Deserialize pc_proof
        let pc_proof = CanonicalDeserialize::deserialize_unchecked(&mut reader)?;

        Ok(Self {
            commitments,
            evaluations,
            prover_messages: vec![ProverMsg::<F>::EmptyMessage; num_rounds],
            pc_proof,
        })
    }

    #[inline]
    fn deserialize_uncompressed<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        // Deserialize commitments
        let num_rounds = 3;
        let comms_per_round = vec![3, 3, 2];
        let mut commitments = Vec::with_capacity(num_rounds);

        for i in 0..num_rounds {
            // Deserialize round commitments
            let mut round_comms = Vec::with_capacity(comms_per_round[i]);

            for _ in 0..comms_per_round[i] {
                let comm: PC::Commitment =
                    CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;
                round_comms.push(comm);
            }

            commitments.push(round_comms);
        }

        // Deserialize evaluations
        let evaluations_num = AHPForR1CS::<F>::PROVER_POLYNOMIALS.len() +
            AHPForR1CS::<F>::INDEXER_POLYNOMIALS.len() +
            2 // boundary polynomials are evaluated at two different points
            ;

        let mut evaluations = Vec::with_capacity(evaluations_num);
        for _ in 0..evaluations_num {
            let eval: F = CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;
            evaluations.push(eval);
        }

        // Deserialize pc_proof
        let pc_proof = CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;

        Ok(Self {
            commitments,
            evaluations,
            prover_messages: vec![ProverMsg::<F>::EmptyMessage; num_rounds],
            pc_proof,
        })
    }

    #[inline]
    fn deserialize_uncompressed_unchecked<R: Read>(
        mut reader: R,
    ) -> Result<Self, SerializationError> {
        // Deserialize commitments
        let num_rounds = 3;
        let comms_per_round = vec![3, 3, 2];
        let mut commitments = Vec::with_capacity(num_rounds);

        for i in 0..num_rounds {
            // Deserialize round commitments
            let mut round_comms = Vec::with_capacity(comms_per_round[i]);

            for _ in 0..comms_per_round[i] {
                let comm: PC::Commitment =
                    CanonicalDeserialize::deserialize_uncompressed_unchecked(&mut reader)?;
                round_comms.push(comm);
            }

            commitments.push(round_comms);
        }

        // Deserialize evaluations
        let evaluations_num = AHPForR1CS::<F>::PROVER_POLYNOMIALS.len() +
            AHPForR1CS::<F>::INDEXER_POLYNOMIALS.len() +
            2 // boundary polynomials are evaluated at two different points
            ;

        let mut evaluations = Vec::with_capacity(evaluations_num);
        for _ in 0..evaluations_num {
            let eval: F = CanonicalDeserialize::deserialize_uncompressed_unchecked(&mut reader)?;
            evaluations.push(eval);
        }

        // Deserialize pc_proof
        let pc_proof = CanonicalDeserialize::deserialize_uncompressed_unchecked(&mut reader)?;

        Ok(Self {
            commitments,
            evaluations,
            prover_messages: vec![ProverMsg::<F>::EmptyMessage; num_rounds],
            pc_proof,
        })
    }
}

impl<F: PrimeField, PC: PolynomialCommitment<F>> Proof<F, PC> {
    /// Construct a new proof.
    pub fn new(
        commitments: Vec<Vec<PC::Commitment>>,
        evaluations: Vec<F>,
        prover_messages: Vec<ProverMsg<F>>,
        pc_proof: PC::BatchProof,
    ) -> Self {
        Self {
            commitments,
            evaluations,
            prover_messages,
            pc_proof,
        }
    }

    /// Prints information about the size of the proof.
    pub fn print_size_info(&self) {
        let size_of_fe_in_bytes = F::zero().serialized_size();
        let mut num_comms_without_degree_bounds = 0;
        let mut num_comms_with_degree_bounds = 0;
        let mut size_bytes_comms_without_degree_bounds = 0;
        let mut size_bytes_comms_with_degree_bounds = 0;
        let mut size_bytes_proofs = 0;
        for c in self.commitments.iter().flatten() {
            if !c.has_degree_bound() {
                num_comms_without_degree_bounds += 1;
                size_bytes_comms_without_degree_bounds += c.serialized_size();
            } else {
                num_comms_with_degree_bounds += 1;
                size_bytes_comms_with_degree_bounds += c.serialized_size();
            }
        }

        size_bytes_proofs += self.pc_proof.serialized_size();

        let num_evals = self.evaluations.len();
        let evals_size_in_bytes = num_evals * size_of_fe_in_bytes;
        let num_prover_messages: usize = self
            .prover_messages
            .iter()
            .map(|v| match v {
                ProverMsg::EmptyMessage => 0,
                ProverMsg::FieldElements(elems) => elems.len(),
            })
            .sum();
        let prover_msg_size_in_bytes = num_prover_messages * size_of_fe_in_bytes;
        let arg_size = size_bytes_comms_with_degree_bounds
            + size_bytes_comms_without_degree_bounds
            + size_bytes_proofs
            + prover_msg_size_in_bytes
            + evals_size_in_bytes;
        let stats = format!(
            "Argument size in bytes: {}\n\n\
             Number of commitments without degree bounds: {}\n\
             Size (in bytes) of commitments without degree bounds: {}\n\
             Number of commitments with degree bounds: {}\n\
             Size (in bytes) of commitments with degree bounds: {}\n\n\
             Size (in bytes) of evaluation proofs: {}\n\n\
             Number of evaluations: {}\n\
             Size (in bytes) of evaluations: {}\n\n\
             Number of field elements in prover messages: {}\n\
             Size (in bytes) of prover message: {}\n",
            arg_size,
            num_comms_without_degree_bounds,
            size_bytes_comms_without_degree_bounds,
            num_comms_with_degree_bounds,
            size_bytes_comms_with_degree_bounds,
            size_bytes_proofs,
            num_evals,
            evals_size_in_bytes,
            num_prover_messages,
            prover_msg_size_in_bytes,
        );
        add_to_trace!(|| "Statistics about proof", || stats);
    }

    /// Randomize commiments for testing purpose
    pub fn randomize_commitments(&mut self) {
        for group in self.commitments.iter_mut() {
            for comm in group.iter_mut() {
                comm.randomize();
            }
        }
    }
}
