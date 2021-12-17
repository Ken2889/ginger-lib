use crate::darlin::{MarlinProverKey, MarlinVerifierKey};
use algebra::{
    CanonicalDeserialize, CanonicalSerialize, Curve, Read, SerializationError, ToBytes, Write,
};
use digest::Digest;
use marlin::{Proof, IOP};
use poly_commit::ipa_pc::InnerProductArgPC;
use poly_commit::{DomainExtendedPolynomialCommitment, PolynomialCommitment};

pub type PC<G, D> = DomainExtendedPolynomialCommitment<G, InnerProductArgPC<G, D>>;

#[derive(Derivative)]
#[derivative(
    Clone(bound = ""),
    Debug(bound = ""),
    Eq(bound = ""),
    PartialEq(bound = "")
)]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct DLogAccMarlinProverKey<G: Curve, D: Digest + 'static>(pub MarlinProverKey<G, PC<G, D>>);

#[derive(Derivative)]
#[derivative(
    Clone(bound = ""),
    Debug(bound = ""),
    Eq(bound = ""),
    PartialEq(bound = "")
)]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct DLogAccMarlinVerifierKey<G: Curve, D: Digest + 'static>(
    pub MarlinVerifierKey<G, PC<G, D>>,
);

#[derive(Derivative)]
#[derivative(
    Clone(bound = ""),
    Debug(bound = ""),
    Eq(bound = ""),
    PartialEq(bound = "")
)]
pub struct DLogAccMarlinProof<G: Curve, D: Digest + 'static>(pub Proof<G, PC<G, D>>);

impl<G: Curve, D: Digest + 'static> DLogAccMarlinProof<G, D> {
    /// Construct a new proof.
    pub fn new(
        commitments: Vec<Vec<<PC<G, D> as PolynomialCommitment<G>>::Commitment>>,
        evaluations: Vec<G::ScalarField>,
        pc_proof: <PC<G, D> as PolynomialCommitment<G>>::MultiPointProof,
    ) -> Self {
        Self(Proof::new(commitments, evaluations, pc_proof))
    }

    /// Prints information about the size of the proof.
    pub fn print_size_info(&self) {
        self.0.print_size_info();
    }
}

/*
    Implement SemanticallyValid for VerifierKey, ProverKey, and Proof.
*/

impl<G: Curve, D: Digest + 'static> algebra::SemanticallyValid for DLogAccMarlinVerifierKey<G, D> {
    fn is_valid(&self) -> bool {
        self.0.is_valid()
    }
}

impl<G: Curve, D: Digest + 'static> algebra::SemanticallyValid for DLogAccMarlinProverKey<G, D> {
    fn is_valid(&self) -> bool {
        self.0.index_vk.is_valid() && self.0.index.is_valid()
    }
}

impl<G: Curve, D: Digest + 'static> algebra::SemanticallyValid for DLogAccMarlinProof<G, D> {
    fn is_valid(&self) -> bool {
        // Check commitments number and validity
        let num_rounds = 3;
        let comms_per_round = vec![3, 2, 2];

        // Check commitments are grouped into correct num_rounds
        if self.0.commitments.len() != num_rounds {
            return false;
        };

        // Check that each round has the expected number of commitments
        for i in 0..comms_per_round.len() {
            if self.0.commitments[i].len() != comms_per_round[i] {
                return false;
            };
        }

        // Check evaluations num
        let evaluations_num = IOP::<G::ScalarField>::PROVER_POLYNOMIALS.len() +
            IOP::<G::ScalarField>::INDEXER_POLYNOMIALS.len() +
            2 + // boundary polynomials are evaluated at two different points
            1; // evaluation of bullet polynomial at gamma

        self.0.commitments.is_valid() &&  // Check that each commitment is valid
            self.0.evaluations.len() == evaluations_num && // Check correct number of evaluations
            self.0.evaluations.is_valid() && // Check validity of each evaluation
            self.0.pc_proof.is_valid() // Check validity of the batch proof.
    }
}

/*
    Serialization and Deserialization utilities.
*/

impl<G: Curve, D: Digest + 'static> ToBytes for DLogAccMarlinVerifierKey<G, D> {
    #[inline]
    fn write<W: Write>(&self, writer: W) -> std::io::Result<()> {
        self.0.write(writer)
    }
}

impl<G: Curve, D: Digest + 'static> CanonicalSerialize for DLogAccMarlinProof<G, D> {
    fn serialize<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
        self.0.serialize(writer)
    }

    fn serialized_size(&self) -> usize {
        let mut size = 0;

        // Commitments size
        self.0
            .commitments
            .iter()
            .flatten()
            .for_each(|comm| size += comm.serialized_size());

        let evaluations_num = IOP::<G::ScalarField>::PROVER_POLYNOMIALS.len() +
            IOP::<G::ScalarField>::INDEXER_POLYNOMIALS.len() +
            2 + // boundary polynomials are evaluated at two different points
            1; // evaluation of bullet polynomial at gamma

        // Evaluations size
        size += evaluations_num * self.0.evaluations[0].serialized_size();

        // PC proof size
        size += self.0.pc_proof.serialized_size();

        size
    }

    fn serialize_without_metadata<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
        self.0.serialize_without_metadata(writer)
    }

    #[inline]
    fn serialize_uncompressed<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
        self.0.serialize_uncompressed(writer)
    }

    #[inline]
    fn uncompressed_size(&self) -> usize {
        let mut size = 0;

        // Commitments size
        self.0
            .commitments
            .iter()
            .flatten()
            .for_each(|comm| size += comm.uncompressed_size());

        let evaluations_num = IOP::<G::ScalarField>::PROVER_POLYNOMIALS.len() +
            IOP::<G::ScalarField>::INDEXER_POLYNOMIALS.len() +
            2 + // boundary polynomials are evaluated at two different points
            1; // evaluation of bullet polynomial at gamma

        // Evaluations size
        size += evaluations_num * self.0.evaluations[0].uncompressed_size();

        // PC proof size
        size += self.0.pc_proof.uncompressed_size();

        size
    }
}

impl<G: Curve, D: Digest + 'static> CanonicalDeserialize for DLogAccMarlinProof<G, D> {
    fn deserialize<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        // Deserialize commitments
        let num_rounds = 3;
        let comms_per_round = vec![3, 2, 2];
        let mut commitments = Vec::with_capacity(num_rounds);

        for i in 0..num_rounds {
            // Deserialize round commitments
            let mut round_comms = Vec::with_capacity(comms_per_round[i]);

            for _ in 0..comms_per_round[i] {
                let comm: <PC<G, D> as PolynomialCommitment<G>>::Commitment =
                    CanonicalDeserialize::deserialize(&mut reader)?;
                round_comms.push(comm);
            }

            commitments.push(round_comms);
        }

        // Deserialize evaluations
        let evaluations_num = IOP::<G::ScalarField>::PROVER_POLYNOMIALS.len() +
            IOP::<G::ScalarField>::INDEXER_POLYNOMIALS.len() +
            2 + // boundary polynomials are evaluated at two different points
            1; // evaluation of bullet polynomial at gamma

        let mut evaluations = Vec::with_capacity(evaluations_num);
        for _ in 0..evaluations_num {
            let eval: G::ScalarField = CanonicalDeserialize::deserialize(&mut reader)?;
            evaluations.push(eval);
        }

        // Deserialize pc_proof
        let pc_proof = CanonicalDeserialize::deserialize(&mut reader)?;
        Ok(Self(Proof::new(commitments, evaluations, pc_proof)))
    }

    fn deserialize_unchecked<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        // Deserialize commitments
        let num_rounds = 3;
        let comms_per_round = vec![3, 2, 2];
        let mut commitments = Vec::with_capacity(num_rounds);

        for i in 0..num_rounds {
            // Deserialize round commitments
            let mut round_comms = Vec::with_capacity(comms_per_round[i]);

            for _ in 0..comms_per_round[i] {
                let comm: <PC<G, D> as PolynomialCommitment<G>>::Commitment =
                    CanonicalDeserialize::deserialize_unchecked(&mut reader)?;
                round_comms.push(comm);
            }

            commitments.push(round_comms);
        }

        // Deserialize evaluations
        let evaluations_num = IOP::<G::ScalarField>::PROVER_POLYNOMIALS.len() +
            IOP::<G::ScalarField>::INDEXER_POLYNOMIALS.len() +
            2 + // boundary polynomials are evaluated at two different points
            1; // evaluation of bullet polynomial at gamma

        let mut evaluations = Vec::with_capacity(evaluations_num);
        for _ in 0..evaluations_num {
            let eval: G::ScalarField = CanonicalDeserialize::deserialize_unchecked(&mut reader)?;
            evaluations.push(eval);
        }

        // Deserialize pc_proof
        let pc_proof = CanonicalDeserialize::deserialize_unchecked(&mut reader)?;

        Ok(Self(Proof::new(commitments, evaluations, pc_proof)))
    }

    #[inline]
    fn deserialize_uncompressed<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        // Deserialize commitments
        let num_rounds = 3;
        let comms_per_round = vec![3, 2, 2];
        let mut commitments = Vec::with_capacity(num_rounds);

        for i in 0..num_rounds {
            // Deserialize round commitments
            let mut round_comms = Vec::with_capacity(comms_per_round[i]);

            for _ in 0..comms_per_round[i] {
                let comm: <PC<G, D> as PolynomialCommitment<G>>::Commitment =
                    CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;
                round_comms.push(comm);
            }

            commitments.push(round_comms);
        }

        // Deserialize evaluations
        let evaluations_num = IOP::<G::ScalarField>::PROVER_POLYNOMIALS.len() +
            IOP::<G::ScalarField>::INDEXER_POLYNOMIALS.len() +
            2 + // boundary polynomials are evaluated at two different points
            1; // evaluation of bullet polynomial at gamma

        let mut evaluations = Vec::with_capacity(evaluations_num);
        for _ in 0..evaluations_num {
            let eval: G::ScalarField = CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;
            evaluations.push(eval);
        }

        // Deserialize pc_proof
        let pc_proof = CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;

        Ok(Self(Proof::new(commitments, evaluations, pc_proof)))
    }

    #[inline]
    fn deserialize_uncompressed_unchecked<R: Read>(
        mut reader: R,
    ) -> Result<Self, SerializationError> {
        // Deserialize commitments
        let num_rounds = 3;
        let comms_per_round = vec![3, 2, 2];
        let mut commitments = Vec::with_capacity(num_rounds);

        for i in 0..num_rounds {
            // Deserialize round commitments
            let mut round_comms = Vec::with_capacity(comms_per_round[i]);

            for _ in 0..comms_per_round[i] {
                let comm: <PC<G, D> as PolynomialCommitment<G>>::Commitment =
                    CanonicalDeserialize::deserialize_uncompressed_unchecked(&mut reader)?;
                round_comms.push(comm);
            }

            commitments.push(round_comms);
        }

        // Deserialize evaluations
        let evaluations_num = IOP::<G::ScalarField>::PROVER_POLYNOMIALS.len() +
            IOP::<G::ScalarField>::INDEXER_POLYNOMIALS.len() +
            2 + // boundary polynomials are evaluated at two different points
            1; // evaluation of bullet polynomial at gamma

        let mut evaluations = Vec::with_capacity(evaluations_num);
        for _ in 0..evaluations_num {
            let eval: G::ScalarField =
                CanonicalDeserialize::deserialize_uncompressed_unchecked(&mut reader)?;
            evaluations.push(eval);
        }

        // Deserialize pc_proof
        let pc_proof = CanonicalDeserialize::deserialize_uncompressed_unchecked(&mut reader)?;

        Ok(Self(Proof::new(commitments, evaluations, pc_proof)))
    }
}
