use crate::{
    bytes::{FromBytes, ToBytes},
    groups::Group,
    curves::{
        Curve, EndoMulCurve,
        models::{EndoMulParameters as EndoParameters, SWModelParameters as Parameters},
    },
    fields::{BitIterator, Field, PrimeField, SquareRootField},
    CanonicalDeserialize, CanonicalDeserializeWithFlags, CanonicalSerialize,
    CanonicalSerializeWithFlags, Error, FromBytesChecked, SWFlags,
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
        Self::new(self.x, -self.y)
    }
}

impl<P: Parameters> ToBytes for AffineRep<P> {
    #[inline]
    fn write<W: Write>(&self, mut writer: W) -> IoResult<()> {
        CanonicalSerialize::serialize(&self, &mut writer)
            .map_err(|e| IoError::new(ErrorKind::Other, format!{"{:?}", e}))
    }
}

impl<P: Parameters> FromBytes for AffineRep<P> {
    #[inline]
    fn read<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(CanonicalDeserialize::deserialize_unchecked(&mut reader)
            .map_err(|e| IoError::new(ErrorKind::Other, format!{"{:?}", e}))?
        )
    }
}

impl<P: Parameters> CanonicalSerialize for AffineRep<P> {
    #[allow(unused_qualifications)]
    #[inline]
    fn serialize<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
        let flags = SWFlags::from_y_parity(self.y.is_odd());
        self.x.serialize_with_flags(writer, flags)
    }

    #[inline]
    fn serialized_size(&self) -> usize {
        P::BaseField::zero().serialized_size_with_flags::<SWFlags>()
    }

    #[allow(unused_qualifications)]
    #[inline]
    fn serialize_uncompressed<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        CanonicalSerialize::serialize(&self.x, &mut writer)?;
        self.y.serialize_with_flags(&mut writer, SWFlags::default())?;
        Ok(())
    }

    #[inline]
    fn uncompressed_size(&self) -> usize {
        self.x.serialized_size() + self.y.serialized_size_with_flags::<SWFlags>()
    }
}

impl<P: Parameters> CanonicalDeserialize for AffineRep<P> {
    #[allow(unused_qualifications)]
    fn deserialize<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let p = Self::deserialize_unchecked(reader)?;
        if !Projective::<P>::from_affine(&p).is_in_correct_subgroup_assuming_on_curve() {
            return Err(SerializationError::InvalidData);
        }
        Ok(p)
    }

    #[allow(unused_qualifications)]
    fn deserialize_unchecked<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let (x, flags): (P::BaseField, SWFlags) =
            CanonicalDeserializeWithFlags::deserialize_with_flags(reader)?;
        if flags.is_infinity() {
            Err(SerializationError::InvalidData)?
        } else {
            let p = Projective::<P>::get_point_from_x_and_parity(x, flags.is_odd().unwrap())
                .ok_or(SerializationError::InvalidData)?;
            Ok(p.into_affine().map_err(|_| SerializationError::InvalidData)?)
        }
    }

    #[allow(unused_qualifications)]
    fn deserialize_uncompressed<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let p = Self::deserialize_uncompressed_unchecked(reader)?;

        if !Projective::<P>::from_affine(&p).group_membership_test() {
            return Err(SerializationError::InvalidData);
        }
        Ok(p)
    }

    #[allow(unused_qualifications)]
    fn deserialize_uncompressed_unchecked<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        let x: P::BaseField = CanonicalDeserialize::deserialize(&mut reader)?;
        let (y, flags): (P::BaseField, SWFlags) =
            CanonicalDeserializeWithFlags::deserialize_with_flags(&mut reader)?;
        if flags.is_infinity() {
            Err(SerializationError::InvalidData)?
        }
        Ok(AffineRep::new(x, y))
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
pub struct Projective<P: Parameters> {
    pub x: P::BaseField,
    pub y: P::BaseField,
    pub z: P::BaseField,
    #[derivative(Debug = "ignore")]
    #[serde(skip)]
    _params: PhantomData<P>,
}

impl<P: Parameters> Projective<P> {
    pub fn new(x: P::BaseField, y: P::BaseField, z: P::BaseField) -> Self {
        Self {
            x,
            y,
            z,
            _params: PhantomData,
        }
    }
}

impl<P: Parameters> Display for Projective<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "Projective(x={}, y={}, z={})", self.x, self.y, self.z)
    }
}

impl<P: Parameters> PartialEq for Projective<P> {
    fn eq(&self, other: &Self) -> bool {
        if self.is_zero() {
            return other.is_zero();
        }

        if other.is_zero() {
            return false;
        }

        if (self.x * &other.z) != (other.x * &self.z) || (self.y * &other.z) != (other.y * &self.z)
        {
            false
        } else {
            true
        }
    }
}

impl<P: Parameters> Distribution<Projective<P>> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Projective<P> {
        let res = Projective::prime_subgroup_generator() * &P::ScalarField::rand(rng);
        debug_assert!(res.is_in_correct_subgroup_assuming_on_curve());
        res
    }
}

impl<P: Parameters> ToBytes for Projective<P> {
    #[inline]
    fn write<W: Write>(&self, mut writer: W) -> IoResult<()> {
        let normalized = self.normalize();
        normalized.x.write(&mut writer)?;
        normalized.y.write(&mut writer)
    }
}

impl<P: Parameters> FromBytes for Projective<P> {
    #[inline]
    fn read<R: Read>(mut reader: R) -> IoResult<Self> {
        let x = P::BaseField::read(&mut reader)?;
        let y = P::BaseField::read(&mut reader)?;
        let z = P::BaseField::one();
        Ok(Self::new(x, y, z))
    }
}

impl<P: Parameters> FromBytesChecked for Projective<P> {
    fn read_checked<R: Read>(mut reader: R) -> IoResult<Self> {
        let x = P::BaseField::read_checked(&mut reader)?;
        let y = P::BaseField::read_checked(&mut reader)?;
        let z = P::BaseField::one();
        let point = Self::new(x, y, z);
        if !point.group_membership_test() {
            return Err(IoError::new(
                ErrorKind::InvalidData,
                "invalid point: group membership test failed",
            ));
        }
        Ok(point)
    }
}

impl<P: Parameters> Default for Projective<P> {
    #[inline]
    fn default() -> Self {
        Self::zero()
    }
}

impl<P: Parameters> SemanticallyValid for Projective<P> {
    fn is_valid(&self) -> bool {
        self.x.is_valid() && self.y.is_valid() && self.z.is_valid() && self.group_membership_test()
    }
}

impl<P: Parameters> CanonicalSerialize for Projective<P> {
    #[allow(unused_qualifications)]
    #[inline]
    fn serialize<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
        if self.is_zero() {
            let flags = SWFlags::infinity();
            // Serialize 0.
            P::BaseField::zero().serialize_with_flags(writer, flags)
        } else {
            let self_affine = self.into_affine().unwrap();
            let flags = SWFlags::from_y_parity(self_affine.y.is_odd());
            self_affine.x.serialize_with_flags(writer, flags)
        }
    }

    #[inline]
    fn serialized_size(&self) -> usize {
        P::BaseField::zero().serialized_size_with_flags::<SWFlags>()
    }

    #[allow(unused_qualifications)]
    #[inline]
    fn serialize_uncompressed<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        if self.is_zero() {
            CanonicalSerialize::serialize(&self.x, &mut writer)?;
            self.y.serialize_with_flags(&mut writer, SWFlags::infinity())?;
        } else {
            let self_affine = self.into_affine().unwrap();
            CanonicalSerialize::serialize(&self_affine.x, &mut writer)?;
            self_affine.y.serialize_with_flags(&mut writer, SWFlags::default())?;
        };
        Ok(())
    }

    #[inline]
    fn uncompressed_size(&self) -> usize {
        self.x.serialized_size() + self.y.serialized_size_with_flags::<SWFlags>()
    }
}

impl<P: Parameters> CanonicalDeserialize for Projective<P> {
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
        let (x, flags): (P::BaseField, SWFlags) =
            CanonicalDeserializeWithFlags::deserialize_with_flags(reader)?;
        if flags.is_infinity() {
            Ok(Self::zero())
        } else {
            let p = Projective::<P>::get_point_from_x_and_parity(x, flags.is_odd().unwrap())
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
        let (y, flags): (P::BaseField, SWFlags) =
            CanonicalDeserializeWithFlags::deserialize_with_flags(&mut reader)?;
        let p = Projective::<P>::new(x, y, if flags.is_infinity() { P::BaseField::zero() } else { P::BaseField::one() });
        Ok(p)
    }
}

impl<P: Parameters> Neg for Projective<P> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        if !self.is_zero() {
            Self::new(self.x, -self.y, self.z)
        } else {
            self
        }
    }
}

impl<'a, P: Parameters> AddAssign<&'a Self> for Projective<P> {
    fn add_assign(&mut self, other: &'a Self) {
        if self.is_zero() {
            *self = *other;
            return;
        }

        if other.is_zero() {
            return;
        }

        // https://www.hyperelliptic.org/EFD/g1p/data/shortw/projective/addition/add-1998-cmo-2
        if self == other {
            self.double_in_place();
        } else {
            // Y1Z2 = Y1*Z2
            let y1z2 = self.y * &other.z;
            // X1Z2 = X1*Z2
            let x1z2 = self.x * &other.z;
            // Z1Z2 = Z1*Z2
            let z1z2 = self.z * &other.z;
            // u = Y2*Z1-Y1Z2
            let u = (self.z * &other.y) - &y1z2;
            // uu = u^2
            let uu = u.square();
            // v = X2*Z1-X1Z2
            let v = (self.z * &other.x) - &x1z2;
            // vv = v^2
            let vv = v.square();
            // vvv = v*vv
            let vvv = v * &vv;
            // R = vv*X1Z2
            let r = vv * &x1z2;
            // A = uu*Z1Z2-vvv-2*R
            let a = (uu * &z1z2) - &(vvv + &r + &r);
            // X3 = v*A
            self.x = v * &a;
            // Y3 = u*(R-A)-vvv*Y1Z2
            self.y = ((r - &a) * &u) - &(vvv * &y1z2);
            // Z3 = vvv*Z1Z2
            self.z = vvv * &z1z2;
        }
    }
}

impl<'a, P: Parameters> Add<&'a Self> for Projective<P> {
    type Output = Self;

    #[inline]
    fn add(self, other: &'a Self) -> Self {
        let mut copy = self;
        copy += other;
        copy
    }
}

impl<P: Parameters> AddAssign<Self> for Projective<P> {
    #[inline]
    fn add_assign(&mut self, other: Self) {
        *self += &other;
    }
}

impl<P: Parameters> Add<Self> for Projective<P> {
    type Output = Self;

    #[inline]
    fn add(self, other: Self) -> Self {
        self + &other
    }
}

impl<'a, P: Parameters> SubAssign<&'a Self> for Projective<P> {
    fn sub_assign(&mut self, other: &'a Self) {
        *self += &(-(*other));
    }
}

impl<'a, P: Parameters> Sub<&'a Self> for Projective<P> {
    type Output = Self;

    #[inline]
    fn sub(self, other: &'a Self) -> Self {
        let mut copy = self;
        copy -= other;
        copy
    }
}

impl<P: Parameters> SubAssign<Self> for Projective<P> {
    #[inline]
    fn sub_assign(&mut self, other: Self) {
        *self -= &other;
    }
}

impl<P: Parameters> Sub<Self> for Projective<P> {
    type Output = Self;

    #[inline]
    fn sub(self, other: Self) -> Self {
        self - &other
    }
}

impl<'a, P: Parameters> MulAssign<&'a P::ScalarField> for Projective<P> {

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

impl<'a, P: Parameters> Mul<&'a P::ScalarField> for Projective<P> {
    type Output = Self;

    #[inline]
    fn mul(self, other: &'a P::ScalarField) -> Self {
        let mut copy = self;
        copy *= other;
        copy
    }
}

// The affine point X, Y is represented in the Projective
// coordinates with Z = 1.
impl<P: Parameters> From<AffineRep<P>> for Projective<P> {
    #[inline]
    fn from(p: AffineRep<P>) -> Projective<P> {
        Self::new(p.x, p.y, P::BaseField::one())
    }
}

// The projective point X, Y, Z is represented in the affine
// coordinates as X/Z^2, Y/Z^3.
impl<P: Parameters> TryFrom<Projective<P>> for AffineRep<P> {
    type Error = Error;

    #[inline]
    fn try_from(p: Projective<P>) -> Result<AffineRep<P>, Error> {
        if p.is_zero() {
            Err("Zero projective cannot be convrted to affine".to_owned())?
        } else if p.z.is_one() {
            // If Z is one, the point is already normalized.
            Ok(AffineRep::new(p.x, p.y))
        } else {
            let normalized = p.normalize();
            Ok(AffineRep::new(normalized.x, normalized.y))
        }
    }
}


impl<P: Parameters> Group for Projective<P> {
    type ScalarField = P::ScalarField;

    // The point at infinity is conventionally represented as (1:1:0)
    #[inline]
    fn zero() -> Self {
        Self::new(
            P::BaseField::one(),
            P::BaseField::one(),
            P::BaseField::zero(),
        )
    }

    // The point at infinity is always represented by
    // Z = 0.
    #[inline]
    fn is_zero(&self) -> bool {
        self.z.is_zero()
    }

    fn double_in_place(&mut self) -> &mut Self {
        if self.is_zero() {
            self
        } else {
            // https://www.hyperelliptic.org/EFD/g1p/auto-shortw-projective.html#doubling-dbl-2007-bl

            // XX = X1^2
            let xx = self.x.square();
            // ZZ = Z1^2
            let zz = self.z.square();
            // w = a*ZZ + 3*XX
            let w = P::mul_by_a(&zz) + &(xx + &xx.double());
            // s = 2*Y1*Z1
            let mut s = self.y * &(self.z);
            s.double_in_place();
            // sss = s^3
            let mut sss = s.square();
            sss *= &s;
            // R = Y1*s
            let r = self.y * &s;
            // RR = R2
            let rr = r.square();
            // B = (X1+R)^2-XX-RR
            let b = (self.x + &r).square() - &xx - &rr;
            // h = w2-2*B
            let h = w.square() - &(b + &b);
            // X3 = h*s
            self.x = h * &s;
            // Y3 = w*(B-h)-2*RR
            self.y = w * &(b - &h) - &(rr + &rr);
            // Z3 = sss
            self.z = sss;

            self
        }
    }
}

impl<P: Parameters> Curve for Projective<P> {
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
        if self.is_zero() {
            self.x = other.x;
            self.y = other.y;
            self.z = P::BaseField::one();
            return;
        }
        let mut v = other.x * &self.z;
        let mut u = other.y * &self.z;
        if u == self.y && v == self.x {
            // x1 / z1 == x2 / z2 <==> x1 * z2 == x2 * z1;
            // Here, z2 = 1, so we have x1 == x2 * z1;
            self.double_in_place();
        } else {
            // https://www.hyperelliptic.org/EFD/g1p/auto-shortw-projective.html#addition-madd-1998-cmo
            // u = Y2*Z1-Y1
            u -= &self.y;
            // uu = u^2
            let uu = u.square();
            // v = X2*Z1-X1
            v -= &self.x;
            // vv = v2
            let vv = v.square();
            // vvv = v*vv
            let vvv = v * &vv;
            // r = vv*X1
            let r = vv * &self.x;
            // a = uu*Z1-vvv-2*r
            let a = uu * &self.z - &vvv - &r.double();
            // X3 = v*a
            self.x = v * &a;
            // Y3 = u*(R-A)-vvv*Y1
            self.y = u * &(r - &a) - &(vvv * &self.y);
            // Z3 = vvv*Z1
            self.z = vvv * &self.z;
        }
    }

    /// WARNING: This implementation doesn't take costant time with respect
    /// to the exponent, and therefore is susceptible to side-channel attacks.
    /// Be sure to use it in applications where timing (or similar) attacks
    /// are not possible.
    /// TODO: Add a side-channel secure variant.
    fn mul_bits<S: AsRef<[u64]>>(&self, bits: BitIterator<S>) -> Self {
        if self.is_zero() {
            return *self;
        }
        Self::mul_bits_affine(&self.into_affine().unwrap(), bits)
    }

    fn mul_bits_affine<'a, S: AsRef<[u64]>>(affine: &'a Self::AffineRep, bits: BitIterator<S>) -> Self {
        let mut res = Self::zero();
        for i in bits {
            res.double_in_place();
            if i {
                res.add_affine_assign(&affine);
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
        if self.is_zero() {
            true
        } else {
            // Check that the point is on the curve
            let y2 = self.y.square();
            let x3b = P::add_b(&((self.x.square() * &self.x) + &P::mul_by_a(&self.x)));
            y2 == x3b
        }
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
            g.x *= &g.z; // x/z^2
            g.y *= &g.z;
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
        // Compute x^3 + ax + b
        let x3b = P::add_b(&((x.square() * &x) + &P::mul_by_a(&x)));

        x3b.sqrt().map(|y| {
            let negy = -y;
            let y = if (y < negy) ^ greatest { y } else { negy };
            Self::new(x, y, P::BaseField::one())
        })
    }

    /// Attempts to construct an affine point given an x-coordinate. The
    /// point is not guaranteed to be in the prime order subgroup.
    ///
    /// If and only if `parity` is set will the odd y-coordinate be selected.
    #[allow(dead_code)]
    fn get_point_from_x_and_parity(x: P::BaseField, parity: bool) -> Option<Self> {
        // Compute x^3 + ax + b
        let x3b = P::add_b(&((x.square() * &x) + &P::mul_by_a(&x)));

        x3b.sqrt().map(|y| {
            let negy = -y;
            let y = if y.is_odd() ^ parity { negy } else { y };
            Self::new(x, y, P::BaseField::one())
        })
    }

    fn from_random_bytes(bytes: &[u8]) -> Option<Self> {
        P::BaseField::from_random_bytes_with_flags::<SWFlags>(bytes).and_then(|(x, flags)| {
            // if x is valid and is zero and only the infinity flag is set, then parse this
            // point as infinity. For all other choices, get the original point.
            if x.is_zero() && flags.is_infinity() {
                Some(Self::zero())
            } else if let Some(y_is_odd) = flags.is_odd() {
                Self::get_point_from_x_and_parity(x, y_is_odd) // Unwrap is safe because it's not zero.
            } else {
                None
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

    fn sum_buckets_affine(to_add: &mut [Vec<Self::AffineRep>]) {
        let zero = P::BaseField::zero();
        let one = P::BaseField::one();
        let length = to_add.iter().map(|l| l.len()).fold(0, |x, y| x + y);
        let mut denoms = vec![zero; length / 2];

        while to_add.iter().position(|x| x.len() > 1) != None {
            let mut dx: usize = 0;
            for p in to_add.iter_mut() {
                if p.len() < 2 {
                    continue;
                }
                let len = if p.len() % 2 == 0 {
                    p.len()
                } else {
                    p.len() - 1
                };
                for i in (0..len).step_by(2) {
                    denoms[dx] = {
                        if p[i].x == p[i + 1].x {
                            if p[i + 1].y == zero {
                                one
                            } else {
                                p[i + 1].y.double()
                            }
                        } else {
                            p[i].x - &p[i + 1].x
                        }
                    };
                    dx += 1;
                }
            }

            denoms.truncate(dx);
            crate::fields::batch_inversion(&mut denoms);
            dx = 0;

            for p in to_add.iter_mut() {
                if p.len() < 2 {
                    continue;
                }
                let len = if p.len() % 2 == 0 {
                    p.len()
                } else {
                    p.len() - 1
                };

                let mut zeros = vec![false; p.len()];

                for i in (0..len).step_by(2) {
                    let j = i / 2;
                    if zeros[i + 1] {
                        p[j] = p[i];
                    } else if zeros[i] {
                        p[j] = p[i + 1];
                    } else if p[i + 1].x == p[i].x && (p[i + 1].y != p[i].y || p[i + 1].y.is_zero())
                    {
                        zeros[j] = true;
                    } else if p[i + 1].x == p[i].x && p[i + 1].y == p[i].y {
                        let sq = p[i].x.square();
                        let s = (sq.double() + &sq + &P::COEFF_A) * &denoms[dx];
                        let x = s.square() - &p[i].x.double();
                        let y = -p[i].y - &(s * &(x - &p[i].x));
                        p[j].x = x;
                        p[j].y = y;
                    } else {
                        let s = (p[i].y - &p[i + 1].y) * &denoms[dx];
                        let x = s.square() - &p[i].x - &p[i + 1].x;
                        let y = -p[i].y - &(s * &(x - &p[i].x));
                        p[j].x = x;
                        p[j].y = y;
                    }
                    dx += 1;
                }

                let len = p.len();
                if len % 2 == 1 {
                    p[len / 2] = p[len - 1];
                    p.truncate(len / 2 + 1);
                } else {
                    p.truncate(len / 2);
                }
            }
        }
    }
}

impl<P: EndoParameters> EndoMulCurve for Projective<P> {
    fn apply_endomorphism(&self) -> Self {
        let mut self_e = self.clone();
        self_e.x.mul_assign(P::ENDO_COEFF);
        self_e
    }

    fn endo_rep_to_scalar(bits: Vec<bool>) -> Result<Self::ScalarField, Error> {
        let mut a: P::ScalarField = 2u64.into();
        let mut b: P::ScalarField = 2u64.into();

        let one = P::ScalarField::one();
        let one_neg = one.neg();

        let mut bits = bits;
        if bits.len() % 2 == 1 {
            bits.push(false);
        }

        if bits.len() > P::LAMBDA {
            Err("Endo mul bits length exceeds LAMBDA")?
        }

        for i in (0..(bits.len() / 2)).rev() {
            a.double_in_place();
            b.double_in_place();

            let s = if bits[i * 2] { &one } else { &one_neg };

            if bits[i * 2 + 1] {
                a.add_assign(s);
            } else {
                b.add_assign(s);
            }
        }

        Ok(a.mul(P::ENDO_SCALAR) + &b)
    }

    /// Endomorphism-based multiplication of a curve point
    /// with a scalar in little-endian endomorphism representation.
    fn endo_mul(&self, bits: Vec<bool>) -> Result<Self, Error> {

        let self_affine = self.into_affine()?;
        let self_affine_neg = self_affine.neg();

        let self_e = self.apply_endomorphism();
        let self_affine_e = self_e.into_affine()?;

        let self_affine_e_neg = self_affine_e.neg();

        let mut acc = self_e;
        acc.add_affine_assign(&self_affine);
        acc.double_in_place();

        let mut bits = bits;
        if bits.len() % 2 == 1 {
            bits.push(false);
        }

        if bits.len() > P::LAMBDA {
            Err("Endo mul bits length exceeds LAMBDA")?
        }

        for i in (0..(bits.len() / 2)).rev() {
            let s = if bits[i * 2 + 1] {
                if bits[i * 2] {
                    &self_affine_e
                } else {
                    &self_affine_e_neg
                }
            } else {
                if bits[i * 2] {
                    &self_affine
                } else {
                    &self_affine_neg
                }
            };

            acc.double_in_place();
            acc.add_affine_assign(s);
        }

        Ok(acc)
    }
}
