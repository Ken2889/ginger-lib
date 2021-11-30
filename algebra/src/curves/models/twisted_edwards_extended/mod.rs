use crate::{
    bytes::{FromBytes, ToBytes},
    groups::Group,
    curves::{
        Curve,
        models::MontgomeryModelParameters as MontgomeryParameters,
        models::TEModelParameters as Parameters,
    },
    fields::{BitIterator, Field, PrimeField, SquareRootField},
    CanonicalDeserialize, CanonicalDeserializeWithFlags, CanonicalSerialize,
    CanonicalSerializeWithFlags, Error, FromBytesChecked, EdwardsFlags,
    SemanticallyValid, SerializationError, UniformRand,
};
use rand::{
    distributions::{Distribution, Standard},
    Rng,
};
use serde::{Deserialize, Serialize};
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use std::{
    fmt::{Display, Formatter, Result as FmtResult},
    io::{Error as IoError, ErrorKind, Read, Result as IoResult, Write},
    convert::TryFrom,
    marker::PhantomData,
};

#[cfg(test)]
pub mod tests;

#[derive(Derivative)]
#[derivative(
Copy(bound = "P: Parameters"),
Clone(bound = "P: Parameters"),
PartialEq(bound = "P: Parameters"),
Eq(bound = "P: Parameters"),
Debug(bound = "P: Parameters"),
Hash(bound = "P: Parameters")
)]
#[derive(Serialize, Deserialize)]
pub struct AffineRep<P: Parameters> {
    pub x: P::BaseField,
    pub y: P::BaseField,
    #[derivative(Debug = "ignore")]
    #[serde(skip)]
    _params: PhantomData<P>,
}

impl<P: Parameters> AffineRep<P> {
    pub fn new(x: P::BaseField, y: P::BaseField) -> Self {
        Self {
            x,
            y,
            _params: PhantomData,
        }
    }
}

impl<P: Parameters> Display for AffineRep<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "AffineRep(x={}, y={})", self.x, self.y)
    }
}

impl<P: Parameters> Neg for AffineRep<P> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        Self::new(-self.x, self.y)
    }
}

#[derive(Derivative)]
#[derivative(
Copy(bound = "P: Parameters"),
Clone(bound = "P: Parameters"),
Eq(bound = "P: Parameters"),
Debug(bound = "P: Parameters"),
Hash(bound = "P: Parameters")
)]
#[derive(Serialize, Deserialize)]
pub struct TEExtended<P: Parameters> {
    pub x: P::BaseField,
    pub y: P::BaseField,
    pub t: P::BaseField,
    pub z: P::BaseField,
    #[derivative(Debug = "ignore")]
    #[serde(skip)]
    _params: PhantomData<P>,
}

impl<P: Parameters> TEExtended<P> {
    pub fn new(x: P::BaseField, y: P::BaseField, t: P::BaseField, z: P::BaseField) -> Self {
        Self {
            x,
            y,
            t,
            z,
            _params: PhantomData,
        }
    }
}

impl<P: Parameters> Display for TEExtended<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "Projective(x={}, y={}, t={}, z={})", self.x, self.y, self.t, self.z)
    }
}

impl<P: Parameters> PartialEq for TEExtended<P> {
    fn eq(&self, other: &Self) -> bool {
        if self.is_zero() {
            return other.is_zero();
        }

        if other.is_zero() {
            return false;
        }

        (self.x * &other.z) == (other.x * &self.z) && (self.y * &other.z) == (other.y * &self.z)
    }
}

impl<P: Parameters> Distribution<TEExtended<P>> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> TEExtended<P> {
        loop {
            let x = P::BaseField::rand(rng);
            let greatest = rng.gen();

            if let Some(p) = TEExtended::get_point_from_x(x, greatest) {
                return p.scale_by_cofactor();
            }
        }
    }
}

impl<P: Parameters> ToBytes for TEExtended<P> {
    #[inline]
    fn write<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.x.write(&mut writer)?;
        self.y.write(&mut writer)?;
        self.t.write(&mut writer)?;
        self.z.write(writer)
    }
}

impl<P: Parameters> FromBytes for TEExtended<P> {
    #[inline]
    fn read<R: Read>(mut reader: R) -> IoResult<Self> {
        let x = P::BaseField::read(&mut reader)?;
        let y = P::BaseField::read(&mut reader)?;
        let t = P::BaseField::read(&mut reader)?;
        let z = P::BaseField::read(reader)?;
        Ok(Self::new(x, y, t, z))
    }
}

impl<P: Parameters> FromBytesChecked for TEExtended<P> {
    fn read_checked<R: Read>(mut reader: R) -> IoResult<Self> {
        let x = P::BaseField::read_checked(&mut reader)?;
        let y = P::BaseField::read_checked(&mut reader)?;
        let t = P::BaseField::read_checked(&mut reader)?;
        let z = P::BaseField::read_checked(reader)?;
        let point = Self::new(x, y, t, z);
        if !point.group_membership_test() {
            return Err(IoError::new(
                ErrorKind::InvalidData,
                "invalid point: group membership test failed",
            ));
        }
        Ok(point)
    }
}

impl<P: Parameters> Default for TEExtended<P> {
    #[inline]
    fn default() -> Self {
        Self::zero()
    }
}

impl<P: Parameters> SemanticallyValid for TEExtended<P> {
    fn is_valid(&self) -> bool {
        self.x.is_valid()
            && self.y.is_valid()
            && self.z.is_valid()
            && self.t.is_valid()
            && self.group_membership_test()
    }
}

impl<P: Parameters> CanonicalSerialize for TEExtended<P> {
    #[allow(unused_qualifications)]
    #[inline]
    fn serialize<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
        if self.is_zero() {
            let flags = EdwardsFlags::default();
            // Serialize 0.
            P::BaseField::zero().serialize_with_flags(writer, flags)
        } else {
            let self_affine = self.into_affine().unwrap();
            let flags = EdwardsFlags::from_y_parity(self_affine.y.is_odd());
            self_affine.x.serialize_with_flags(writer, flags)
        }
    }

    #[inline]
    fn serialized_size(&self) -> usize {
        P::BaseField::zero().serialized_size_with_flags::<EdwardsFlags>()
    }

    #[allow(unused_qualifications)]
    #[inline]
    fn serialize_uncompressed<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        let self_affine = self.into_affine().unwrap();
        self_affine.x.serialize_uncompressed(&mut writer)?;
        self_affine.y.serialize_uncompressed(&mut writer)?;
        Ok(())
    }

    #[inline]
    fn uncompressed_size(&self) -> usize {
        self.x.serialized_size() + self.y.serialized_size()
    }
}

impl<P: Parameters> CanonicalDeserialize for TEExtended<P> {
    #[allow(unused_qualifications)]
    fn deserialize<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let p = Self::deserialize_unchecked(reader)?;
        if !p.is_zero() && !p.is_in_correct_subgroup_assuming_on_curve() {
            return Err(SerializationError::InvalidData);
        }
        Ok(p)
    }

    #[allow(unused_qualifications)]
    fn deserialize_unchecked<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let (x, flags): (P::BaseField, EdwardsFlags) =
            CanonicalDeserializeWithFlags::deserialize_with_flags(reader)?;
        if x == P::BaseField::zero() {
            Ok(Self::zero())
        } else {
            let p = TEExtended::<P>::get_point_from_x_and_parity(x, flags.is_odd())
                .ok_or(SerializationError::InvalidData)?;
            Ok(p)
        }
    }

    #[allow(unused_qualifications)]
    fn deserialize_uncompressed<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let p = Self::deserialize_uncompressed_unchecked(reader)?;

        if !p.group_membership_test() {
            return Err(SerializationError::InvalidData);
        }
        Ok(p)
    }

    #[allow(unused_qualifications)]
    fn deserialize_uncompressed_unchecked<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        let x: P::BaseField = CanonicalDeserialize::deserialize(&mut reader)?;
        let y: P::BaseField = CanonicalDeserialize::deserialize(&mut reader)?;

        let p = TEExtended::<P>::new(x, y, x * &y, P::BaseField::one());
        Ok(p)
    }
}

impl<P: Parameters> Neg for TEExtended<P> {
    type Output = Self;

    #[inline]
    fn neg(mut self) -> Self {
        self.x = -self.x;
        self.t = -self.t;
        self
    }
}

impl<'a, P: Parameters> AddAssign<&'a Self> for TEExtended<P> {
    fn add_assign(&mut self, other: &'a Self) {
        // See "Twisted Edwards Curves Revisited"
        // Huseyin Hisil, Kenneth Koon-Ho Wong, Gary Carter, and Ed Dawson
        // 3.1 Unified Addition in E^e

        // A = x1 * x2
        let a = self.x * &other.x;

        // B = y1 * y2
        let b = self.y * &other.y;

        // C = d * t1 * t2
        let c = P::COEFF_D * &self.t * &other.t;

        // D = z1 * z2
        let d = self.z * &other.z;

        // H = B - aA
        let h = b - &P::mul_by_a(&a);

        // E = (x1 + y1) * (x2 + y2) - A - B
        let e = (self.x + &self.y) * &(other.x + &other.y) - &a - &b;

        // F = D - C
        let f = d - &c;

        // G = D + C
        let g = d + &c;

        // x3 = E * F
        self.x = e * &f;

        // y3 = G * H
        self.y = g * &h;

        // t3 = E * H
        self.t = e * &h;

        // z3 = F * G
        self.z = f * &g;
    }
}

impl<'a, P: Parameters> Add<&'a Self> for TEExtended<P> {
    type Output = Self;

    #[inline]
    fn add(self, other: &'a Self) -> Self {
        let mut copy = self;
        copy += other;
        copy
    }
}

impl<P: Parameters> AddAssign<Self> for TEExtended<P> {
    #[inline]
    fn add_assign(&mut self, other: Self) {
        *self += &other;
    }
}

impl<P: Parameters> Add<Self> for TEExtended<P> {
    type Output = Self;

    #[inline]
    fn add(self, other: Self) -> Self {
        self + &other
    }
}

impl<'a, P: Parameters> SubAssign<&'a Self> for TEExtended<P> {
    fn sub_assign(&mut self, other: &'a Self) {
        *self += &(-(*other));
    }
}

impl<'a, P: Parameters> Sub<&'a Self> for TEExtended<P> {
    type Output = Self;

    #[inline]
    fn sub(self, other: &'a Self) -> Self {
        let mut copy = self;
        copy -= other;
        copy
    }
}

impl<P: Parameters> SubAssign<Self> for TEExtended<P> {
    #[inline]
    fn sub_assign(&mut self, other: Self) {
        *self -= &other;
    }
}

impl<P: Parameters> Sub<Self> for TEExtended<P> {
    type Output = Self;

    #[inline]
    fn sub(self, other: Self) -> Self {
        self - &other
    }
}

impl<'a, P: Parameters> MulAssign<&'a P::ScalarField> for TEExtended<P> {

    /// WARNING: This implementation doesn't take costant time with respect
    /// to the exponent, and therefore is susceptible to side-channel attacks.
    /// Be sure to use it in applications where timing (or similar) attacks
    /// are not possible.
    /// TODO: Add a side-channel secure variant.
    fn mul_assign(&mut self, other: &'a P::ScalarField) {
        if !self.is_zero() {
            *self = self.mul_bits(BitIterator::new(Into::<<P::ScalarField as PrimeField>::BigInt>::into(*other)))
        }
    }
}

impl<'a, P: Parameters> Mul<&'a P::ScalarField> for TEExtended<P> {
    type Output = Self;

    #[inline]
    fn mul(self, other: &'a P::ScalarField) -> Self {
        let mut copy = self;
        copy *= other;
        copy
    }
}

// The affine point X, Y is represented in the Jacobian
// coordinates with Z = 1.
impl<P: Parameters> From<AffineRep<P>> for TEExtended<P> {
    #[inline]
    fn from(p: AffineRep<P>) -> TEExtended<P> {
        Self::new(p.x, p.y, p.x * &p.y, P::BaseField::one())
    }
}

// The projective point X, Y, Z is represented in the affine
// coordinates as X/Z^2, Y/Z^3.
impl<P: Parameters> TryFrom<TEExtended<P>> for AffineRep<P> {
    type Error = Error;

    #[inline]
    fn try_from(p: TEExtended<P>) -> Result<AffineRep<P>, Error> {
        if p.is_zero() {
            Ok(AffineRep::new(P::BaseField::zero(), P::BaseField::one()))
        } else if p.z.is_one() {
            // If Z is one, the point is already normalized.
            Ok(AffineRep::new(p.x, p.y))
        } else {
            // Z is nonzero, so it must have an inverse in a field.
            let z_inv = p.z.inverse().unwrap();
            let x = p.x * &z_inv;
            let y = p.y * &z_inv;
            Ok(AffineRep::new(x, y))
        }
    }
}


impl<P: Parameters> Group for TEExtended<P> {
    type ScalarField = P::ScalarField;

    // The point at infinity is conventionally represented as (1:1:0)
    #[inline]
    fn zero() -> Self {
        Self::new(
            P::BaseField::zero(),
            P::BaseField::one(),
            P::BaseField::zero(),
            P::BaseField::one(),
        )
    }

    // The point at infinity is always represented by
    // Z = 0.
    #[inline]
    fn is_zero(&self) -> bool {
        self.x.is_zero() && self.y == self.z && !self.y.is_zero() && self.t.is_zero()
    }

    fn double_in_place(&mut self) -> &mut Self {
        let tmp = *self;
        *self += &tmp;
        self
    }
}

impl<P: Parameters> Curve for TEExtended<P> {
    type BaseField = P::BaseField;
    type AffineRep = AffineRep<P>;

    fn add_affine<'a>(&self, other: &'a Self::AffineRep) -> Self
    {
        let mut copy = *self;
        copy.add_affine_assign(other);
        copy
    }

    fn add_affine_assign<'a>(&mut self, other: &'a Self::AffineRep)
    {
        // A = X1*X2
        let a = self.x * &other.x;
        // B = Y1*Y2
        let b = self.y * &other.y;
        // C = T1*d*T2
        let c = P::COEFF_D * &self.t * &other.x * &other.y;
        // D = Z1
        let d = self.z;
        // E = (X1+Y1)*(X2+Y2)-A-B
        let e = (self.x + &self.y) * &(other.x + &other.y) - &a - &b;
        // F = D-C
        let f = d - &c;
        // G = D+C
        let g = d + &c;
        // H = B-a*A
        let h = b - &P::mul_by_a(&a);
        // X3 = E*F
        self.x = e * &f;
        // Y3 = G*H
        self.y = g * &h;
        // T3 = E*H
        self.t = e * &h;
        // Z3 = F*G
        self.z = f * &g;
    }

    /// WARNING: This implementation doesn't take costant time with respect
    /// to the exponent, and therefore is susceptible to side-channel attacks.
    /// Be sure to use it in applications where timing (or similar) attacks
    /// are not possible.
    /// TODO: Add a side-channel secure variant.
    fn mul_bits<S: AsRef<[u64]>>(&self, bits: BitIterator<S>) -> Self {
        let mut res = Self::zero();
        let self_affine = self.into_affine().unwrap();
        for i in bits {
            res.double_in_place();
            if i {
                res.add_affine_assign(&self_affine);
            }
        }
        res
    }

    fn scale_by_cofactor(&self) -> Self {
        let cofactor = BitIterator::new(P::COFACTOR);
        self.mul_bits(cofactor)
    }

    fn scale_by_cofactor_inv(&self) -> Self {
        let cofactor_inv = BitIterator::new(Into::<<P::ScalarField as PrimeField>::BigInt>::into(P::COFACTOR_INV));
        self.mul_bits(cofactor_inv)
    }

    #[inline]
    fn prime_subgroup_generator() -> Self {
        Self::new(
            P::AFFINE_GENERATOR_COEFFS.0,
            P::AFFINE_GENERATOR_COEFFS.1,
            P::AFFINE_GENERATOR_COEFFS.0 * &P::AFFINE_GENERATOR_COEFFS.1,
            P::BaseField::one(),
        )
    }

    #[inline]
    fn group_membership_test(&self) -> bool {
        self.is_on_curve()
            && if !self.is_zero() {
            self.is_in_correct_subgroup_assuming_on_curve()
        } else {
            true
        }
    }

    fn is_on_curve(&self) -> bool {
        let x2 = self.x.square();
        let y2 = self.y.square();

        let lhs = y2 + &P::mul_by_a(&x2);
        let rhs = P::BaseField::one() + &(P::COEFF_D * &(x2 * &y2));

        lhs == rhs
    }

    #[inline]
    fn is_in_correct_subgroup_assuming_on_curve(&self) -> bool {
        self.mul_bits(BitIterator::new(P::ScalarField::characteristic()))
            .is_zero()
    }

    #[inline]
    fn is_normalized(&self) -> bool {
        self.is_zero() || self.z.is_one()
    }

    #[inline]
    fn normalize(&self) -> Self {
        let mut copy = *self;
        copy.normalize_assign();
        copy
    }

    fn normalize_assign(&mut self) {
        if !self.is_normalized() {
            let dz = self.z.inverse().unwrap();
            self.x *= &dz; // x/z
            self.y *= &dz; // y/z
            self.t *= &dz; // y/z
            self.z = P::BaseField::one(); // z = 1
        }
    }

    #[inline]
    fn batch_normalization(v: &mut [Self]) {
        // Montgomery’s Trick and Fast Implementation of Masked AES
        // Genelle, Prouff and Quisquater
        // Section 3.2

        // First pass: compute [a, ab, abc, ...]
        let mut prod = Vec::with_capacity(v.len());
        let mut tmp = P::BaseField::one();
        for g in v
            .iter_mut()
            // Ignore normalized elements
            .filter(|g| !g.is_normalized())
        {
            tmp.mul_assign(&g.z);
            prod.push(tmp);
        }

        // Invert `tmp`.
        tmp = tmp.inverse().unwrap(); // Guaranteed to be nonzero.

        // Second pass: iterate backwards to compute inverses
        for (g, s) in v
            .iter_mut()
            // Backwards
            .rev()
            // Ignore normalized elements
            .filter(|g| !g.is_normalized())
            // Backwards, skip last element, fill in one for last term.
            .zip(
                prod.into_iter()
                    .rev()
                    .skip(1)
                    .chain(Some(P::BaseField::one())),
            )
        {
            // tmp := tmp * g.z; g.z := tmp * s = 1/z
            let newtmp = tmp * &g.z;
            g.z = tmp * &s;
            tmp = newtmp;
        }

        // Perform affine transformations
        for g in v.iter_mut().filter(|g| !g.is_normalized()) {
            g.x *= &g.z; // x/z
            g.y *= &g.z;
            g.t *= &g.z;
            g.z = P::BaseField::one(); // z = 1
        }
    }

    /// Attempts to construct an affine point given an x-coordinate. The
    /// point is not guaranteed to be in the prime order subgroup.
    ///
    /// If and only if `greatest` is set will the lexicographically
    /// largest y-coordinate be selected.
    #[allow(dead_code)]
    fn get_point_from_x(x: P::BaseField, greatest: bool) -> Option<Self> {
        let x2 = x.square();
        let one = P::BaseField::one();
        let numerator = P::mul_by_a(&x2) - &one;
        let denominator = P::COEFF_D * &x2 - &one;
        let y2 = denominator.inverse().map(|denom| denom * &numerator);
        y2.and_then(|y2| y2.sqrt()).map(|y| {
            let negy = -y;
            let y = if (y < negy) ^ greatest { y } else { negy };
            Self::new(x, y, x * &y, P::BaseField::one())
        })
    }

    /// Attempts to construct an affine point given an x-coordinate. The
    /// point is not guaranteed to be in the prime order subgroup.
    ///
    /// If and only if `parity` is set will the odd y-coordinate be selected.
    #[allow(dead_code)]
    fn get_point_from_x_and_parity(x: P::BaseField, parity: bool) -> Option<Self> {
        let x2 = x.square();
        let one = P::BaseField::one();
        let numerator = P::mul_by_a(&x2) - &one;
        let denominator = P::COEFF_D * &x2 - &one;
        let y2 = denominator.inverse().map(|denom| denom * &numerator);
        y2.and_then(|y2| y2.sqrt()).map(|y| {
            let negy = -y;
            let y = if y.is_odd() ^ parity { negy } else { y };
            Self::new(x, y, x * &y, P::BaseField::one())
        })
    }

    fn from_random_bytes(bytes: &[u8]) -> Option<Self> {
        P::BaseField::from_random_bytes_with_flags::<EdwardsFlags>(bytes).and_then(|(x, flags)| {
            // if x is valid and is zero, then parse this
            // point as infinity.
            if x.is_zero() {
                Some(Self::zero())
            } else {
                Self::get_point_from_x_and_parity(x, flags.is_odd())
            }
        })
    }

    #[inline]
    fn recommended_wnaf_for_scalar(scalar: <Self::ScalarField as PrimeField>::BigInt) -> usize {
        P::empirical_recommended_wnaf_for_scalar(scalar)
    }

    #[inline]
    fn recommended_wnaf_for_num_scalars(num_scalars: usize) -> usize {
        P::empirical_recommended_wnaf_for_num_scalars(num_scalars)
    }

    fn sum_buckets_affine(_: &mut [Vec<Self::AffineRep>]) {
        unimplemented!()
    }
}

#[derive(Derivative)]
#[derivative(
    Copy(bound = "P: MontgomeryParameters"),
    Clone(bound = "P: MontgomeryParameters"),
    PartialEq(bound = "P: MontgomeryParameters"),
    Eq(bound = "P: MontgomeryParameters"),
    Debug(bound = "P: MontgomeryParameters"),
    Hash(bound = "P: MontgomeryParameters")
)]
pub struct MontgomeryAffine<P: MontgomeryParameters> {
    pub x: P::BaseField,
    pub y: P::BaseField,
    #[derivative(Debug = "ignore")]
    _params: PhantomData<P>,
}

impl<P: MontgomeryParameters> Display for MontgomeryAffine<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "MontgomeryGroupAffine(x={}, y={})", self.x, self.y)
    }
}

impl<P: MontgomeryParameters> MontgomeryAffine<P> {
    pub fn new(x: P::BaseField, y: P::BaseField) -> Self {
        Self {
            x,
            y,
            _params: PhantomData,
        }
    }
}
