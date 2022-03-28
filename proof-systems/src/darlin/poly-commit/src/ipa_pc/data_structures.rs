//! Data structures for the dlog commitment scheme from [BCMS20]:
//! * [`VerifierKey`], [`CommitterKey`]
//! * [`Commitment`], [`Randomness`], [`Proof`], [`MultiPointProof`]
//! and the implementation of their corresponding traits from [data_structures.rs](/src/data_structures.rs).
//! In addition scheme-specific structs [`SuccinctCheckPolynomial`] and [`VerifierState`] are
//! introduced.
//!
//! [BCMS20]: https://eprint.iacr.org/2020/499
use super::IPACurve;
use crate::*;
use crate::{PCKey, Vec};
use algebra::PrimeField;
use std::{
    convert::TryFrom,
    io::{Read, Write},
    vec,
};

/// `CommitterKey` is used to commit to, and create evaluation proofs for, a given
/// polynomial.
#[derive(Derivative)]
#[derivative(
    Hash(bound = ""),
    Clone(bound = ""),
    Debug(bound = ""),
    Eq(bound = ""),
    PartialEq(bound = "")
)]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct CommitterKey<G: IPACurve> {
    /// The base point vector used for the coefficients of the polynomial.
    pub comm_key: Vec<G::AffineRep>,

    /// The base point used by the opening proof to reduce to a non-blinded
    /// opening assertion.
    pub h: G,

    /// The base point that is to be used for hiding.
    pub s: G,

    /// The hash of the universal parameters from which this key was derived from
    pub hash: Vec<u8>,
}

impl<G: IPACurve> SemanticallyValid for CommitterKey<G> {
    // Technically this function is redundant, since the keys are generated
    // through a deterministic procedure starting from a public string.
    fn is_valid(&self) -> bool {
        G::batch_from_affine(&self.comm_key).is_valid() && self.h.is_valid() && self.s.is_valid()
    }
}

impl<G: IPACurve> PCKey for CommitterKey<G> {
    /// Outputs the maximum degree supported by this key
    fn degree(&self) -> usize {
        self.comm_key.len() - 1
    }

    /// Returns the hash of `self` instance.
    fn get_hash(&self) -> &[u8] {
        self.hash.as_slice()
    }

    fn trim(&self, degree: usize) -> Result<Self, Error> {
        // Passing degree 0
        if degree == 0 {
            return Err(Error::DegreeIsZero);
        }

        // Ensure that degree + 1 is a power of two
        let degree = (degree + 1).next_power_of_two() - 1;
        if degree > self.degree() {
            return Err(Error::TrimmingDegreeTooLarge);
        }

        let trim_time = start_timer!(|| format!("Trimming to supported degree of {}", degree));

        let ck = CommitterKey {
            comm_key: self.comm_key[..(degree + 1)].to_vec(),
            h: self.h.clone(),
            s: self.s.clone(),
            hash: self.hash.clone(),
        };

        end_timer!(trim_time);

        Ok(ck)
    }
}

/// `VerifierKey` is used to check evaluation proofs for a given commitment.
pub type VerifierKey<G> = CommitterKey<G>;

/// An opening proof for a single-point multi-poly assertion.
#[derive(Derivative)]
#[derivative(
    Default(bound = ""),
    Hash(bound = ""),
    Clone(bound = ""),
    Debug(bound = ""),
    Eq(bound = ""),
    PartialEq(bound = "")
)]
pub struct Proof<G: IPACurve> {
    /// Vector of left elements for each of the log_d iterations in `open`
    pub l_vec: Vec<G>,

    /// Vector of right elements for each of the log_d iterations within `open`
    pub r_vec: Vec<G>,

    /// Committer key from the last iteration within `open`
    pub final_comm_key: G,

    /// The witness from the last iteration within `open`
    pub c: G::ScalarField,

    /// The commitment of the optional mask polynomial, used in the reduction to the non-blinded
    /// opening assertion.
    pub hiding_comm: Option<G>,

    /// The masked randomness of polynomial
    pub rand: Option<G::ScalarField>,
}

impl<G: IPACurve> PCProof for Proof<G> {
    fn degree(&self) -> Result<usize, Error> {
        if self.l_vec.len() != self.r_vec.len() {
            Err(Error::IncorrectInputLength(
                format!(
                    "expected l_vec size and r_vec size to be equal; instead l_vec size is {:} and r_vec size is {:}",
                    self.l_vec.len(),
                    self.r_vec.len()
                )
            ))?
        }
        Ok(self.l_vec.len() - 1)
    }
}

impl<G: IPACurve> SemanticallyValid for Proof<G> {
    fn is_valid(&self) -> bool {
        self.l_vec.is_valid() &&
            self.r_vec.is_valid() &&
            self.l_vec.len() == self.r_vec.len() &&
            self.final_comm_key.is_valid() &&
            self.c.is_valid() &&
            {
                if self.hiding_comm.is_some() {
                    self.hiding_comm.as_ref().unwrap().is_valid() && self.rand.is_some()
                } else {
                    self.rand.is_none()
                }
            } &&
            // No need to re-check the hiding comm as the && operator is short-circuit
            {
                if self.rand.is_some() {
                    self.rand.as_ref().unwrap().is_valid()
                } else {
                    true
                }
            }
    }
}

impl<G: IPACurve> CanonicalSerialize for Proof<G> {
    fn serialize<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        // l_vec
        // More than enough for practical applications
        let l_vec_len =
            u8::try_from(self.l_vec.len()).map_err(|_| SerializationError::NotEnoughSpace)?;
        CanonicalSerialize::serialize(&l_vec_len, &mut writer)?;

        // Save only one of the coordinates of the point and one byte of flags in order
        // to be able to reconstruct the other coordinate
        for p in self.l_vec.iter() {
            CanonicalSerialize::serialize(p, &mut writer)?;
        }

        // We know r_vec must be equal in size to l_vec, so no need to serialize it too
        if self.l_vec.len() != self.r_vec.len() {
            return Err(SerializationError::InvalidData);
        }

        // Save only one of the coordinates of the point and one byte of flags in order
        // to be able to reconstruct the other coordinate
        for p in self.r_vec.iter() {
            CanonicalSerialize::serialize(p, &mut writer)?;
        }

        // Serialize the other fields
        CanonicalSerialize::serialize(&self.final_comm_key, &mut writer)?;
        CanonicalSerialize::serialize(&self.c, &mut writer)?;
        CanonicalSerialize::serialize(&self.hiding_comm, &mut writer)?;
        CanonicalSerialize::serialize(&self.rand, &mut writer)
    }

    fn serialized_size(&self) -> usize {
        1 + self
            .l_vec
            .iter()
            .map(|item| item.serialized_size())
            .sum::<usize>()
            + self
                .r_vec
                .iter()
                .map(|item| item.serialized_size())
                .sum::<usize>()
            + self.final_comm_key.serialized_size()
            + self.c.serialized_size()
            + self.hiding_comm.serialized_size()
            + self.rand.serialized_size()
    }

    #[inline]
    fn serialize_without_metadata<W: Write>(
        &self,
        mut writer: W,
    ) -> Result<(), SerializationError> {
        for p in self.l_vec.iter() {
            CanonicalSerialize::serialize_without_metadata(p, &mut writer)?;
        }

        for p in self.r_vec.iter() {
            CanonicalSerialize::serialize_without_metadata(p, &mut writer)?;
        }

        CanonicalSerialize::serialize_without_metadata(&self.final_comm_key, &mut writer)?;
        CanonicalSerialize::serialize_without_metadata(&self.c, &mut writer)?;
        CanonicalSerialize::serialize_without_metadata(&self.hiding_comm, &mut writer)?;
        CanonicalSerialize::serialize_without_metadata(&self.rand, &mut writer)
    }

    #[inline]
    fn serialize_uncompressed<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        // l_vec
        // More than enough for practical applications
        let l_vec_len =
            u8::try_from(self.l_vec.len()).map_err(|_| SerializationError::NotEnoughSpace)?;
        CanonicalSerialize::serialize_uncompressed(&l_vec_len, &mut writer)?;

        for p in self.l_vec.iter() {
            CanonicalSerialize::serialize_uncompressed(p, &mut writer)?;
        }

        // We know r_vec must be equal in size to l_vec, so no need to serialize it too
        if self.l_vec.len() != self.r_vec.len() {
            return Err(SerializationError::InvalidData);
        }

        for p in self.r_vec.iter() {
            CanonicalSerialize::serialize_uncompressed(p, &mut writer)?;
        }

        // Serialize the other fields
        CanonicalSerialize::serialize_uncompressed(&self.final_comm_key, &mut writer)?;
        CanonicalSerialize::serialize_uncompressed(&self.c, &mut writer)?;
        CanonicalSerialize::serialize_uncompressed(&self.hiding_comm, &mut writer)?;
        CanonicalSerialize::serialize_uncompressed(&self.rand, &mut writer)
    }

    #[inline]
    fn uncompressed_size(&self) -> usize {
        1 + self
            .l_vec
            .iter()
            .map(|item| item.uncompressed_size())
            .sum::<usize>()
            + self
                .r_vec
                .iter()
                .map(|item| item.uncompressed_size())
                .sum::<usize>()
            + self.final_comm_key.uncompressed_size()
            + self.c.uncompressed_size()
            + self.hiding_comm.uncompressed_size()
            + self.rand.uncompressed_size()
    }
}

impl<G: IPACurve> CanonicalDeserialize for Proof<G> {
    fn deserialize<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        // Read l_vec
        let l_vec_len: u8 = CanonicalDeserialize::deserialize(&mut reader)?;
        let mut l_vec = Vec::with_capacity(l_vec_len as usize);
        for _ in 0..(l_vec_len as usize) {
            let c: G = CanonicalDeserialize::deserialize(&mut reader)?;
            l_vec.push(c);
        }

        // Read r_vec
        let r_vec_len = l_vec_len;
        let mut r_vec = Vec::with_capacity(r_vec_len as usize);
        for _ in 0..(r_vec_len as usize) {
            let c: G = CanonicalDeserialize::deserialize(&mut reader)?;
            r_vec.push(c);
        }

        // Read other fields
        let final_comm_key: G = CanonicalDeserialize::deserialize(&mut reader)?;
        let c: G::ScalarField = CanonicalDeserialize::deserialize(&mut reader)?;
        let hiding_comm: Option<G> = CanonicalDeserialize::deserialize(&mut reader)?;
        let rand: Option<G::ScalarField> = CanonicalDeserialize::deserialize(&mut reader)?;

        Ok(Self {
            l_vec,
            r_vec,
            final_comm_key,
            c,
            hiding_comm,
            rand,
        })
    }

    fn deserialize_unchecked<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        // Read l_vec
        let l_vec_len: u8 = CanonicalDeserialize::deserialize_unchecked(&mut reader)?;
        let mut l_vec = Vec::with_capacity(l_vec_len as usize);
        for _ in 0..(l_vec_len as usize) {
            let c: G = CanonicalDeserialize::deserialize_unchecked(&mut reader)?;
            l_vec.push(c);
        }

        // Read r_vec
        let r_vec_len = l_vec_len;
        let mut r_vec = Vec::with_capacity(r_vec_len as usize);
        for _ in 0..(r_vec_len as usize) {
            let c: G = CanonicalDeserialize::deserialize_unchecked(&mut reader)?;
            r_vec.push(c);
        }

        // Read other fields
        let final_comm_key: G = CanonicalDeserialize::deserialize_unchecked(&mut reader)?;
        let c: G::ScalarField = CanonicalDeserialize::deserialize_unchecked(&mut reader)?;
        let hiding_comm: Option<G> = CanonicalDeserialize::deserialize_unchecked(&mut reader)?;
        let rand: Option<G::ScalarField> =
            CanonicalDeserialize::deserialize_unchecked(&mut reader)?;

        Ok(Self {
            l_vec,
            r_vec,
            final_comm_key,
            c,
            hiding_comm,
            rand,
        })
    }

    #[inline]
    fn deserialize_uncompressed<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        // Read l_vec
        let l_vec_len: u8 = CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;
        let mut l_vec = Vec::with_capacity(l_vec_len as usize);
        for _ in 0..(l_vec_len as usize) {
            let c: G = CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;
            l_vec.push(c);
        }

        // Read r_vec
        let r_vec_len = l_vec_len;
        let mut r_vec = Vec::with_capacity(r_vec_len as usize);
        for _ in 0..(r_vec_len as usize) {
            let c: G = CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;
            r_vec.push(c);
        }

        // Read other fields
        let final_comm_key: G = CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;
        let c: G::ScalarField = CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;
        let hiding_comm: Option<G> = CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;
        let rand: Option<G::ScalarField> =
            CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;

        Ok(Self {
            l_vec,
            r_vec,
            final_comm_key,
            c,
            hiding_comm,
            rand,
        })
    }

    #[inline]
    fn deserialize_uncompressed_unchecked<R: Read>(
        mut reader: R,
    ) -> Result<Self, SerializationError> {
        // Read l_vec
        let l_vec_len: u8 = CanonicalDeserialize::deserialize_uncompressed_unchecked(&mut reader)?;
        let mut l_vec = Vec::with_capacity(l_vec_len as usize);
        for _ in 0..(l_vec_len as usize) {
            let c: G = CanonicalDeserialize::deserialize_uncompressed_unchecked(&mut reader)?;
            l_vec.push(c);
        }

        // Read r_vec
        let r_vec_len = l_vec_len;
        let mut r_vec = Vec::with_capacity(r_vec_len as usize);
        for _ in 0..(r_vec_len as usize) {
            let c: G = CanonicalDeserialize::deserialize_uncompressed_unchecked(&mut reader)?;
            r_vec.push(c);
        }

        // Read other fields
        let final_comm_key: G =
            CanonicalDeserialize::deserialize_uncompressed_unchecked(&mut reader)?;
        let c: G::ScalarField =
            CanonicalDeserialize::deserialize_uncompressed_unchecked(&mut reader)?;
        let hiding_comm: Option<G> =
            CanonicalDeserialize::deserialize_uncompressed_unchecked(&mut reader)?;
        let rand: Option<G::ScalarField> =
            CanonicalDeserialize::deserialize_uncompressed_unchecked(&mut reader)?;

        Ok(Self {
            l_vec,
            r_vec,
            final_comm_key,
            c,
            hiding_comm,
            rand,
        })
    }
}

/// Multi-point multi-poly opening proof according to Boneh et al.
/// Contains an extra commitment `h_comm` which cannot be reproduced by
/// linear combinations.     
#[derive(Derivative)]
#[derivative(
    Default(bound = ""),
    Hash(bound = ""),
    Clone(bound = ""),
    Debug(bound = ""),
    Eq(bound = ""),
    PartialEq(bound = "")
)]
pub struct MultiPointProof<G: IPACurve> {
    /// This is a "classical" single-point multi-poly proof which involves all commitments:
    /// commitments from the initial claim and the new "h_comm"
    pub proof: Proof<G>,

    /// Commitment to the h(X) polynomial
    pub h_commitment: G,
}

impl<G: IPACurve> BDFGMultiPointProof<G> for MultiPointProof<G> {
    type Commitment = G;
    type Proof = Proof<G>;

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

impl<G: IPACurve> SemanticallyValid for MultiPointProof<G> {
    fn is_valid(&self) -> bool {
        self.proof.is_valid() && self.h_commitment.is_valid()
    }
}

impl<G: IPACurve> CanonicalSerialize for MultiPointProof<G> {
    fn serialize<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        // Serialize proof
        CanonicalSerialize::serialize(&self.proof, &mut writer)?;

        // Save only one of the coordinates of the point and one byte of flags in order
        // to be able to reconstruct the other coordinate
        CanonicalSerialize::serialize(&self.h_commitment, &mut writer)?;

        Ok(())
    }

    fn serialized_size(&self) -> usize {
        self.proof.serialized_size() + self.h_commitment.serialized_size()
    }

    fn serialize_without_metadata<W: Write>(
        &self,
        mut writer: W,
    ) -> Result<(), SerializationError> {
        // Serialize proof
        CanonicalSerialize::serialize_without_metadata(&self.proof, &mut writer)?;

        // Serialize h_comm
        CanonicalSerialize::serialize_without_metadata(&self.h_commitment, &mut writer)?;

        Ok(())
    }

    #[inline]
    fn serialize_uncompressed<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        // Serialize proof
        CanonicalSerialize::serialize_uncompressed(&self.proof, &mut writer)?;

        // Save only one of the coordinates of the point and one byte of flags in order
        // to be able to reconstruct the other coordinate
        CanonicalSerialize::serialize_uncompressed(&self.h_commitment, &mut writer)?;

        Ok(())
    }

    #[inline]
    fn uncompressed_size(&self) -> usize {
        self.proof.uncompressed_size() + self.h_commitment.uncompressed_size()
    }
}

impl<G: IPACurve> CanonicalDeserialize for MultiPointProof<G> {
    fn deserialize<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        // Read proof
        let proof: Proof<G> = CanonicalDeserialize::deserialize(&mut reader)?;

        // Read commitment to h(X)
        let h_commitment: G = CanonicalDeserialize::deserialize(&mut reader)?;

        Ok(Self {
            proof,
            h_commitment,
        })
    }

    fn deserialize_unchecked<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        // Read proof
        let proof: Proof<G> = CanonicalDeserialize::deserialize_unchecked(&mut reader)?;

        // Read commitment to h(X)
        let h_commitment: G = CanonicalDeserialize::deserialize_unchecked(&mut reader)?;

        Ok(Self {
            proof,
            h_commitment,
        })
    }

    #[inline]
    fn deserialize_uncompressed<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        // Read proof
        let proof: Proof<G> = CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;

        // Read commitment to h(X)
        let h_commitment: G = CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;

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
        let proof: Proof<G> =
            CanonicalDeserialize::deserialize_uncompressed_unchecked(&mut reader)?;

        // Read commitment to h(X)
        let h_commitment: G =
            CanonicalDeserialize::deserialize_uncompressed_unchecked(&mut reader)?;

        Ok(Self {
            proof,
            h_commitment,
        })
    }
}

/// The `SuccinctCheckPolynomial` is the dlog reduction polynomial
///     h(X) = Product_{i=0}^{d-1} (1 + xi_{d-i} * X^{2^i}),
/// where (xi_1,...xi_d) are the challenges of the dlog reduction steps.
/// This polynomial has the special property that it has a succinct description
/// and can be evaluated in `O(log(degree))` time, and the final committer key
/// G_final can be computed via an MSM from its coefficients.
#[derive(Clone, Debug, Eq, PartialEq, Default)]
pub struct SuccinctCheckPolynomial<G: IPACurve> {
    #[doc(hidden)]
    pub chals: Vec<G::ScalarField>,
    #[cfg(feature = "circuit-friendly")]
    #[doc(hidden)]
    pub endo_chals: Vec<G::ScalarField>,
}

impl<G: IPACurve> SuccinctCheckPolynomial<G> {
    /// Construct Self starting from the challenges.
    /// Will automatically calculate also the endo versions of them
    #[cfg(feature = "circuit-friendly")]
    pub fn from_chals(chals: Vec<G::ScalarField>) -> Self {
        use algebra::ToBits;

        let endo_chals = chals
            .iter()
            .map(|chal| {
                // Serialize FE
                let mut bits = chal.write_bits();
                // Reverse bits as endo_rep_to_scalar requires them to be in LE
                bits.reverse();
                // We know that only the first 128 bits are relevant
                bits = bits[..128].to_vec();
                // Read endo scalar
                G::endo_rep_to_scalar(bits).unwrap()
            })
            .collect();
        Self { chals, endo_chals }
    }

    /// Construct Self starting from the challenges
    #[cfg(not(feature = "circuit-friendly"))]
    pub fn from_chals(chals: Vec<G::ScalarField>) -> Self {
        Self { chals }
    }

    /// Get endo chals from this polynomial
    #[cfg(feature = "circuit-friendly")]
    pub fn get_chals(&self) -> &[G::ScalarField] {
        self.endo_chals.as_slice()
    }

    /// Get chals from this polynomial
    #[cfg(not(feature = "circuit-friendly"))]
    pub fn get_chals(&self) -> &[G::ScalarField] {
        self.chals.as_slice()
    }

    /// Slightly optimized way to compute it, taken from
    /// [o1-labs/marlin](https://github.com/o1-labs/marlin/blob/master/dlog/commitment/src/commitment.rs#L175)
    fn _compute_succinct_poly_coeffs(
        &self,
        mut init_coeffs: Vec<G::ScalarField>,
    ) -> Vec<G::ScalarField> {
        let challenges = self.get_chals();
        let log_d = challenges.len();
        let mut k: usize = 0;
        let mut pow: usize = 1;
        for i in 1..1 << log_d {
            k += if i == pow { 1 } else { 0 };
            pow <<= if i == pow { 1 } else { 0 };
            init_coeffs[i] = init_coeffs[i - (pow >> 1)] * challenges[log_d - 1 - (k - 1)];
        }
        init_coeffs
    }

    /// Computes the coefficients of the underlying degree `d` polynomial.
    pub fn compute_coeffs(&self) -> Vec<G::ScalarField> {
        self._compute_succinct_poly_coeffs(vec![G::ScalarField::one(); 1 << self.chals.len()])
    }

    /// Computes the coefficients of the underlying degree `d` polynomial, scaled by
    /// a factor `scale`.
    pub fn compute_scaled_coeffs(&self, scale: G::ScalarField) -> Vec<G::ScalarField> {
        self._compute_succinct_poly_coeffs(vec![scale; 1 << self.chals.len()])
    }

    /// Evaluate `self` at `point` in time `O(log_d)`.
    pub fn evaluate(&self, point: G::ScalarField) -> G::ScalarField {
        let challenges = self.get_chals();
        let log_d = challenges.len();

        let mut product = G::ScalarField::one();
        for (i, challenge) in challenges.iter().enumerate() {
            let i = i + 1;
            let elem_degree: u64 = (1 << (log_d - i)) as u64;
            let elem = point.pow([elem_degree]);
            product *= &(G::ScalarField::one() + &(elem * challenge));
        }

        product
    }
}

impl<G: IPACurve> CanonicalSerialize for SuccinctCheckPolynomial<G> {
    #[inline]
    fn serialize<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        let len = self.chals.len() as u8;
        CanonicalSerialize::serialize(&len, &mut writer)?;
        for item in self.chals.iter() {
            // Each field element is, in reality, only 128 bits long
            let fe128 = item.into_repr().as_ref()[0] as u128
                + ((item.into_repr().as_ref()[1] as u128) << 64);
            CanonicalSerialize::serialize(&fe128, &mut writer)?;
        }
        Ok(())
    }

    #[inline]
    fn serialized_size(&self) -> usize {
        1 + self.chals.len() * 16
    }
}

impl<G: IPACurve> CanonicalDeserialize for SuccinctCheckPolynomial<G> {
    #[inline]
    fn deserialize<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        let len = <u8 as CanonicalDeserialize>::deserialize(&mut reader)?;
        let mut values = Vec::new();
        for _ in 0..len {
            // Each field element is, in reality, only 128 bits long
            let fe128 = u128::deserialize(&mut reader)?;
            values.push(fe128.into());
        }
        Ok(SuccinctCheckPolynomial::<G>::from_chals(values))
    }
}

impl<G: IPACurve> SemanticallyValid for SuccinctCheckPolynomial<G> {
    #[cfg(feature = "circuit-friendly")]
    fn is_valid(&self) -> bool {
        self.chals.is_valid() && self.endo_chals.is_valid()
    }

    #[cfg(not(feature = "circuit-friendly"))]
    fn is_valid(&self) -> bool {
        self.chals.is_valid()
    }
}

/// Succinct check polynomial tagged with a label
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LabeledSuccinctCheckPolynomial<'a, G: IPACurve> {
    label: PolynomialLabel,
    check_poly: &'a SuccinctCheckPolynomial<G>,
}

impl<'a, G: IPACurve> LabeledSuccinctCheckPolynomial<'a, G> {
    pub fn new(label: PolynomialLabel, check_poly: &'a SuccinctCheckPolynomial<G>) -> Self {
        Self {
            label,
            check_poly
        }
    }

    pub fn get_label(&self) -> &PolynomialLabel {
        &self.label
    }

    pub fn get_poly(&self) -> &SuccinctCheckPolynomial<G> {
        self.check_poly
    }
}

/// The succinct part of the verifier returns a succinct-check polynomial and final comm key
#[derive(Clone, Debug, Eq, PartialEq, Default)]
pub struct DLogItem<G: IPACurve> {
    /// check_poly = h(X) = prod (1 + xi_{log(d+1) - i} * X^{2^i} )
    pub check_poly: SuccinctCheckPolynomial<G>,
    /// final comm key
    pub final_comm_key: G,
}

impl<G: IPACurve> CanonicalSerialize for DLogItem<G> {
    fn serialize<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        // GFinal will always be 1 segment and without any shift
        CanonicalSerialize::serialize(&self.final_comm_key, &mut writer)?;

        CanonicalSerialize::serialize(&self.check_poly, &mut writer)
    }

    fn serialized_size(&self) -> usize {
        self.final_comm_key.serialized_size() + self.check_poly.serialized_size()
    }

    fn serialize_without_metadata<W: Write>(
        &self,
        mut writer: W,
    ) -> Result<(), SerializationError> {
        CanonicalSerialize::serialize_without_metadata(&self.final_comm_key, &mut writer)?;

        CanonicalSerialize::serialize_without_metadata(&self.check_poly, &mut writer)
    }

    fn serialize_uncompressed<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        // GFinal will always be 1 segment and without any shift
        CanonicalSerialize::serialize_uncompressed(&self.final_comm_key, &mut writer)?;

        CanonicalSerialize::serialize_uncompressed(&self.check_poly, &mut writer)
    }

    fn uncompressed_size(&self) -> usize {
        self.final_comm_key.uncompressed_size() + self.check_poly.uncompressed_size()
    }
}

impl<G: IPACurve> CanonicalDeserialize for DLogItem<G> {
    fn deserialize<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        // GFinal will always be 1 segment and without any shift
        let final_comm_key = CanonicalDeserialize::deserialize(&mut reader)?;

        let check_poly = CanonicalDeserialize::deserialize(&mut reader)?;

        Ok(Self {
            final_comm_key,
            check_poly,
        })
    }

    fn deserialize_unchecked<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        // GFinal will always be 1 segment and without any shift
        let final_comm_key = CanonicalDeserialize::deserialize_unchecked(&mut reader)?;

        let check_poly = CanonicalDeserialize::deserialize_unchecked(&mut reader)?;

        Ok(Self {
            final_comm_key,
            check_poly,
        })
    }

    #[inline]
    fn deserialize_uncompressed<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        // GFinal will always be 1 segment and without any shift
        let final_comm_key = CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;

        let check_poly = CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;

        Ok(Self {
            final_comm_key,
            check_poly,
        })
    }

    #[inline]
    fn deserialize_uncompressed_unchecked<R: Read>(
        mut reader: R,
    ) -> Result<Self, SerializationError> {
        // GFinal will always be 1 segment and without any shift
        let final_comm_key = CanonicalDeserialize::deserialize_uncompressed_unchecked(&mut reader)?;

        let check_poly = CanonicalDeserialize::deserialize_uncompressed_unchecked(&mut reader)?;

        Ok(Self {
            final_comm_key,
            check_poly,
        })
    }
}

impl<G: IPACurve> SemanticallyValid for DLogItem<G> {
    fn is_valid(&self) -> bool {
        self.final_comm_key.is_valid() && self.check_poly.is_valid()
    }
}

impl<G: IPACurve> PCVerifierState for DLogItem<G> {}
