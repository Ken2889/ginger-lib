//! Data structures for the domain extended polynomial commitment scheme.
//! Introduces
//! * `DomainExtendedCommitment` and their `DomainExtendedRandomness` as vector variant
//!    of the non-extended scheme, and implements group operations for these.
//! * `DomainExtendedMultiPointProof` for the [HaloInfinite] batch evaluation proof of
//!    the domain extended scheme, including implementations of serialization traits.
//!
//! [HaloInfinite]: https://eprint.iacr.org/2020/1536
use crate::*;
use algebra::groups::{Group, GroupVec};
use std::{
    convert::TryFrom,
    io::{Read, Write},
};

/// Multi-point multi-poly opening proof according to [BDFG2020](https://eprint.iacr.org/2020/081).
/// Contains an extra (domain extended) commitment `h_comm` which cannot be reproduced by
/// linear combinations.
#[derive(Derivative)]
#[derivative(
    Clone(bound = ""),
    Debug(bound = ""),
    Eq(bound = ""),
    PartialEq(bound = "")
)]
pub struct DomainExtendedMultiPointProof<G, P>
where
    G: Group,
    P: PCProof,
{
    /// This is a "classical" single-point multi-poly proof which involves all commitments:
    /// commitments from the initial claim and the new "h_commitment"
    pub proof: P,

    /// Commitment to the h(X) polynomial
    pub h_commitment: GroupVec<G>,

    /// Evaluations of the polynomials on the batch evaluation point
    #[cfg(feature="boneh-with-single-point-batch")]
    pub(crate) evaluations: Vec<G::ScalarField>,
}

impl<G, P> BDFGMultiPointProof<G> for DomainExtendedMultiPointProof<G, P>
where
    G: Group,
    P: PCProof,
{
    type Commitment = GroupVec<G>;
    type Proof = P;

    #[inline]
    #[cfg(not(feature = "boneh-with-single-point-batch"))]
    fn new(proof: Self::Proof, h_commitment: Self::Commitment) -> Self {
        Self {
            proof,
            h_commitment,
        }
    }

    #[inline]
    #[cfg(feature = "boneh-with-single-point-batch")]
    fn new(proof: Self::Proof, h_commitment: Self::Commitment, evaluations: Vec<G::ScalarField>) -> Self {
        Self {
            proof,
            h_commitment,
            evaluations,
        }
    }

    #[inline]
    fn get_proof(&self) -> &Self::Proof {
        &self.proof
    }

    #[inline]
    fn get_h_commitment(&self) -> &Self::Commitment {
        &self.h_commitment
    }

    #[cfg(feature="boneh-with-single-point-batch")]
    fn get_evaluations(&self) -> &Vec<G::ScalarField> {
        &self.evaluations
    }
}

impl<G, P> SemanticallyValid for DomainExtendedMultiPointProof<G, P>
where
    G: Group,
    P: PCProof,
{
    fn is_valid(&self) -> bool {
        self.proof.is_valid() && self.h_commitment.is_valid()
    }
}

impl<G, P> CanonicalSerialize for DomainExtendedMultiPointProof<G, P>
where
    G: Group,
    P: PCProof,
{
    fn serialize<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        // Serialize proof
        CanonicalSerialize::serialize(&self.proof, &mut writer)?;

        // Serialize h_comm
        // More than enough for practical applications
        let h_comm_len = u8::try_from(self.h_commitment.len())
            .map_err(|_| SerializationError::NotEnoughSpace)?;
        CanonicalSerialize::serialize(&h_comm_len, &mut writer)?;

        // Save only one of the coordinates of the point and one byte of flags in order
        // to be able to reconstruct the other coordinate
        for item in self.h_commitment.iter() {
            CanonicalSerialize::serialize(item, &mut writer)?;
        }

        // serialize evaluations over batch point, if available
        #[cfg(feature = "boneh-with-single-point-batch")]
        CanonicalSerialize::serialize(&self.evaluations, &mut writer)?;

        Ok(())
    }

    fn serialized_size(&self) -> usize {
        #[cfg(not(feature = "boneh-with-single-point-batch"))]
         return self.proof.serialized_size()
            + 1
            + (self.h_commitment.len() * self.h_commitment[0].serialized_size());

        #[cfg(feature = "boneh-with-single-point-batch")]
            return self.proof.serialized_size() + self.evaluations.serialized_size()
            + 1
            + (self.h_commitment.len() * self.h_commitment[0].serialized_size());
    }

    fn serialize_without_metadata<W: Write>(
        &self,
        mut writer: W,
    ) -> Result<(), SerializationError> {
        // Serialize proof
        CanonicalSerialize::serialize_without_metadata(&self.proof, &mut writer)?;

        // Serialize h_comm
        for item in self.h_commitment.iter() {
            CanonicalSerialize::serialize_without_metadata(item, &mut writer)?;
        }

        // serialize evaluations over batch point, if available
        #[cfg(feature = "boneh-with-single-point-batch")]
        CanonicalSerialize::serialize_without_metadata(&self.evaluations, &mut writer)?;

        Ok(())
    }

    #[inline]
    fn serialize_uncompressed<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        // Serialize proof
        CanonicalSerialize::serialize_uncompressed(&self.proof, &mut writer)?;

        // Serialize h_comm
        // More than enough for practical applications
        let h_comm_len = u8::try_from(self.h_commitment.len())
            .map_err(|_| SerializationError::NotEnoughSpace)?;
        CanonicalSerialize::serialize_uncompressed(&h_comm_len, &mut writer)?;

        // Save only one of the coordinates of the point and one byte of flags in order
        // to be able to reconstruct the other coordinate
        for item in self.h_commitment.iter() {
            CanonicalSerialize::serialize_uncompressed(item, &mut writer)?;
        }

        // serialize evaluations over batch point, if available
        #[cfg(feature = "boneh-with-single-point-batch")]
        CanonicalSerialize::serialize_uncompressed(&self.evaluations, &mut writer)?;

        Ok(())
    }

    #[inline]
    fn uncompressed_size(&self) -> usize {
        #[cfg(not(feature = "boneh-with-single-point-batch"))]
            return self.proof.uncompressed_size()
            + 1
            + (self.h_commitment.len() * self.h_commitment[0].uncompressed_size());

        #[cfg(feature = "boneh-with-single-point-batch")]
            return self.proof.uncompressed_size() + self.evaluations.uncompressed_size()
            + 1
            + (self.h_commitment.len() * self.h_commitment[0].uncompressed_size());
    }
}

impl<G, P> CanonicalDeserialize for DomainExtendedMultiPointProof<G, P>
where
    G: Group,
    P: PCProof,
{
    fn deserialize<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        // Read proof
        let proof: P = CanonicalDeserialize::deserialize(&mut reader)?;

        // Read commitment to h(X)
        let h_comm_len: u8 = CanonicalDeserialize::deserialize(&mut reader)?;
        let mut h_commitment = GroupVec::with_capacity(h_comm_len as usize);
        for _ in 0..(h_comm_len as usize) {
            let item: G = CanonicalDeserialize::deserialize(&mut reader)?;
            h_commitment.push(item);
        }

        #[cfg(not(feature="boneh-with-single-point-batch"))]
            return Ok(Self {
            proof,
            h_commitment,
        });

        #[cfg(feature="boneh-with-single-point-batch")]
            return {
            let evaluations: Vec<G::ScalarField> = CanonicalDeserialize::deserialize(&mut reader)?;

            Ok(Self {
                proof,
                h_commitment,
                evaluations,
            })
        };
    }

    fn deserialize_unchecked<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        // Read proof
        let proof: P = CanonicalDeserialize::deserialize_unchecked(&mut reader)?;

        // Read commitment to h(X)
        let h_comm_len: u8 = CanonicalDeserialize::deserialize_unchecked(&mut reader)?;
        let mut h_commitment = GroupVec::with_capacity(h_comm_len as usize);
        for _ in 0..(h_comm_len as usize) {
            let item: G = CanonicalDeserialize::deserialize_unchecked(&mut reader)?;
            h_commitment.push(item);
        }

        #[cfg(not(feature="boneh-with-single-point-batch"))]
            return Ok(Self {
            proof,
            h_commitment,
        });

        #[cfg(feature="boneh-with-single-point-batch")]
            return {
            let evaluations: Vec<G::ScalarField> = CanonicalDeserialize::deserialize_unchecked(&mut reader)?;

            Ok(Self {
                proof,
                h_commitment,
                evaluations,
            })
        };
    }

    #[inline]
    fn deserialize_uncompressed<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        // Read proof
        let proof: P = CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;

        // Read commitment to h(X)
        let h_comm_len: u8 = CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;
        let mut h_commitment = GroupVec::with_capacity(h_comm_len as usize);
        for _ in 0..(h_comm_len as usize) {
            let item: G = CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;
            h_commitment.push(item);
        }

        #[cfg(not(feature="boneh-with-single-point-batch"))]
            return Ok(Self {
            proof,
            h_commitment,
        });

        #[cfg(feature="boneh-with-single-point-batch")]
            return {
            let evaluations: Vec<G::ScalarField> = CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;

            Ok(Self {
                proof,
                h_commitment,
                evaluations,
            })
        };
    }

    #[inline]
    fn deserialize_uncompressed_unchecked<R: Read>(
        mut reader: R,
    ) -> Result<Self, SerializationError> {
        // Read proof
        let proof: P = CanonicalDeserialize::deserialize_uncompressed_unchecked(&mut reader)?;

        // Read commitment to h(X)
        let h_comm_len: u8 = CanonicalDeserialize::deserialize_uncompressed_unchecked(&mut reader)?;
        let mut h_commitment = GroupVec::with_capacity(h_comm_len as usize);
        for _ in 0..(h_comm_len as usize) {
            let item: G = CanonicalDeserialize::deserialize_uncompressed_unchecked(&mut reader)?;
            h_commitment.push(item);
        }

        #[cfg(not(feature="boneh-with-single-point-batch"))]
            return Ok(Self {
            proof,
            h_commitment,
        });

        #[cfg(feature="boneh-with-single-point-batch")]
            return {
            let evaluations: Vec<G::ScalarField> = CanonicalDeserialize::deserialize_uncompressed_unchecked(&mut reader)?;

            Ok(Self {
                proof,
                h_commitment,
                evaluations,
            })
        };
    }
}
