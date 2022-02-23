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
}

impl<G, P> PCMultiPointProof<G> for DomainExtendedMultiPointProof<G, P>
where
    G: Group,
    P: PCProof,
{
    type Commitment = GroupVec<G>;
    type Proof = P;

    #[inline]
    fn new(proof: Self::Proof, h_commitment: Self::Commitment) -> Self {
        Self {
            proof,
            h_commitment,
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

        Ok(())
    }

    fn serialized_size(&self) -> usize {
        self.proof.serialized_size()
            + 1
            + (self.h_commitment.len() * self.h_commitment[0].serialized_size())
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

        Ok(())
    }

    #[inline]
    fn uncompressed_size(&self) -> usize {
        self.proof.uncompressed_size()
            + 1
            + (self.h_commitment.len() * self.h_commitment[0].uncompressed_size())
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

        Ok(Self {
            proof,
            h_commitment,
        })
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

        Ok(Self {
            proof,
            h_commitment,
        })
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

        Ok(Self {
            proof,
            h_commitment,
        })
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

        Ok(Self {
            proof,
            h_commitment,
        })
    }
}
