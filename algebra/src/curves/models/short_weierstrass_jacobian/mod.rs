use crate::{
    bits::{BitSerializationError, FromBits, FromCompressedBits, ToBits, ToCompressedBits},
    bytes::{FromBytes, ToBytes},
    curves::{
        models::{EndoMulParameters as EndoParameters, SWModelParameters as Parameters},
        Curve, EndoMulCurve,
    },
    fields::{BitIterator, Field, PrimeField, SquareRootField},
    groups::Group,
    CanonicalDeserialize, CanonicalDeserializeWithFlags, CanonicalSerialize,
    CanonicalSerializeWithFlags, Error, FromBytesChecked, SWFlags, SemanticallyValid,
    SerializationError, UniformRand,
};
use rand::{
    distributions::{Distribution, Standard},
    Rng,
};
use serde::{Deserialize, Serialize};
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use std::{
    convert::TryFrom,
    fmt::{Display, Formatter, Result as FmtResult},
    io::{Error as IoError, ErrorKind, Read, Result as IoResult, Write},
    marker::PhantomData,
};
use num_traits::{Zero, One};

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
            .map_err(|e| IoError::new(ErrorKind::Other, format! {"{:?}", e}))
    }
}

impl<P: Parameters> FromBytes for AffineRep<P> {
    #[inline]
    fn read<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(CanonicalDeserialize::deserialize_unchecked(&mut reader)
            .map_err(|e| IoError::new(ErrorKind::Other, format! {"{:?}", e}))?)
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
        self.y
            .serialize_with_flags(&mut writer, SWFlags::default())?;
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
        if !Jacobian::<P>::from_affine(&p).is_in_correct_subgroup_assuming_on_curve() {
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
            let p = Jacobian::<P>::get_point_from_x_and_parity(x, flags.is_odd().unwrap())
                .ok_or(SerializationError::InvalidData)?;
            Ok(p.into_affine()
                .map_err(|_| SerializationError::InvalidData)?)
        }
    }

    #[allow(unused_qualifications)]
    fn deserialize_uncompressed<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let p = Self::deserialize_uncompressed_unchecked(reader)?;

        if !Jacobian::<P>::from_affine(&p).group_membership_test() {
            return Err(SerializationError::InvalidData);
        }
        Ok(p)
    }

    #[allow(unused_qualifications)]
    fn deserialize_uncompressed_unchecked<R: Read>(
        mut reader: R,
    ) -> Result<Self, SerializationError> {
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
pub struct Jacobian<P: Parameters> {
    pub x: P::BaseField,
    pub y: P::BaseField,
    pub z: P::BaseField,
    #[derivative(Debug = "ignore")]
    #[serde(skip)]
    _params: PhantomData<P>,
}

impl<P: Parameters> Jacobian<P> {
    pub fn new(x: P::BaseField, y: P::BaseField, z: P::BaseField) -> Self {
        Self {
            x,
            y,
            z,
            _params: PhantomData,
        }
    }
}

impl<P: Parameters> Display for Jacobian<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "Jacobian(x={}, y={}, z={})", self.x, self.y, self.z)
    }
}

impl<P: Parameters> PartialEq for Jacobian<P> {
    fn eq(&self, other: &Self) -> bool {
        if self.is_zero() {
            return other.is_zero();
        }

        if other.is_zero() {
            return false;
        }

        // The points (X, Y, Z) and (X', Y', Z')
        // are equal when (X * Z^2) = (X' * Z'^2)
        // and (Y * Z^3) = (Y' * Z'^3).
        let z1 = self.z.square();
        let z2 = other.z.square();

        if (self.x * &z2 != other.x * &z1)
            || (self.y * &(z2 * &other.z) != other.y * &(z1 * &self.z))
        {
            false
        } else {
            true
        }
    }
}

impl<P: Parameters> Distribution<Jacobian<P>> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Jacobian<P> {
        loop {
            let x = P::BaseField::rand(rng);
            let greatest = rng.gen();

            if let Some(mut p) = Jacobian::<P>::get_point_from_x(x, greatest) {
                if P::COFACTOR != &[0x1] {
                    p = p.scale_by_cofactor();
                }
                return p;
            }
        }
    }
}

impl<P: Parameters> ToBytes for Jacobian<P> {
    #[inline]
    fn write<W: Write>(&self, mut writer: W) -> IoResult<()> {
        CanonicalSerialize::serialize(&self, &mut writer)
            .map_err(|e| IoError::new(ErrorKind::Other, format! {"{:?}", e}))
    }
}

impl<P: Parameters> FromBytes for Jacobian<P> {
    #[inline]
    fn read<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(CanonicalDeserialize::deserialize_unchecked(&mut reader)
            .map_err(|e| IoError::new(ErrorKind::Other, format! {"{:?}", e}))?)
    }
}

impl<P: Parameters> FromBytesChecked for Jacobian<P> {
    fn read_checked<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(CanonicalDeserialize::deserialize(&mut reader)
            .map_err(|e| IoError::new(ErrorKind::Other, format! {"{:?}", e}))?)
    }
}

impl<P: Parameters> Default for Jacobian<P> {
    #[inline]
    fn default() -> Self {
        Self::zero()
    }
}

impl<P: Parameters> SemanticallyValid for Jacobian<P> {
    fn is_valid(&self) -> bool {
        self.x.is_valid() && self.y.is_valid() && self.z.is_valid() && self.group_membership_test()
    }
}

impl<P: Parameters> CanonicalSerialize for Jacobian<P> {
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
            self.y
                .serialize_with_flags(&mut writer, SWFlags::infinity())?;
        } else {
            let self_affine = self.into_affine().unwrap();
            CanonicalSerialize::serialize(&self_affine.x, &mut writer)?;
            self_affine
                .y
                .serialize_with_flags(&mut writer, SWFlags::default())?;
        };
        Ok(())
    }

    #[inline]
    fn uncompressed_size(&self) -> usize {
        self.x.serialized_size() + self.y.serialized_size_with_flags::<SWFlags>()
    }
}

impl<P: Parameters> CanonicalDeserialize for Jacobian<P> {
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
            let p = Jacobian::<P>::get_point_from_x_and_parity(x, flags.is_odd().unwrap())
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
    fn deserialize_uncompressed_unchecked<R: Read>(
        mut reader: R,
    ) -> Result<Self, SerializationError> {
        let x: P::BaseField = CanonicalDeserialize::deserialize(&mut reader)?;
        let (y, flags): (P::BaseField, SWFlags) =
            CanonicalDeserializeWithFlags::deserialize_with_flags(&mut reader)?;
        let p = Jacobian::<P>::new(
            x,
            y,
            if flags.is_infinity() {
                P::BaseField::zero()
            } else {
                P::BaseField::one()
            },
        );
        Ok(p)
    }
}

impl<P: Parameters> Neg for Jacobian<P> {
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

impl<'a, P: Parameters> AddAssign<&'a Self> for Jacobian<P> {
    fn add_assign(&mut self, other: &'a Self) {
        if self.is_zero() {
            *self = *other;
            return;
        }

        if other.is_zero() {
            return;
        }

        // http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-add-2007-bl
        // Works for all curves.

        // Z1Z1 = Z1^2
        let z1z1 = self.z.square();

        // Z2Z2 = Z2^2
        let z2z2 = other.z.square();

        // U1 = X1*Z2Z2
        let u1 = self.x * &z2z2;

        // U2 = X2*Z1Z1
        let u2 = other.x * &z1z1;

        // S1 = Y1*Z2*Z2Z2
        let s1 = self.y * &other.z * &z2z2;

        // S2 = Y2*Z1*Z1Z1
        let s2 = other.y * &self.z * &z1z1;

        if u1 == u2 && s1 == s2 {
            // The two points are equal, so we double.
            self.double_in_place();
        } else {
            // If we're adding -a and a together, self.z becomes zero as H becomes zero.

            // H = U2-U1
            let h = u2 - &u1;

            // I = (2*H)^2
            let i = (h.double()).square();

            // J = H*I
            let j = h * &i;

            // r = 2*(S2-S1)
            let r = (s2 - &s1).double();

            // V = U1*I
            let v = u1 * &i;

            // X3 = r^2 - J - 2*V
            self.x = r.square() - &j - &(v.double());

            // Y3 = r*(V - X3) - 2*S1*J
            self.y = r * &(v - &self.x) - &*(s1 * &j).double_in_place();

            // Z3 = ((Z1+Z2)^2 - Z1Z1 - Z2Z2)*H
            self.z = ((self.z + &other.z).square() - &z1z1 - &z2z2) * &h;
        }
    }
}

impl<'a, P: Parameters> Add<&'a Self> for Jacobian<P> {
    type Output = Self;

    #[inline]
    fn add(self, other: &'a Self) -> Self {
        let mut copy = self;
        copy += other;
        copy
    }
}

impl<P: Parameters> AddAssign<Self> for Jacobian<P> {
    #[inline]
    fn add_assign(&mut self, other: Self) {
        *self += &other;
    }
}

impl<P: Parameters> Add<Self> for Jacobian<P> {
    type Output = Self;

    #[inline]
    fn add(self, other: Self) -> Self {
        self + &other
    }
}

impl<'a, P: Parameters> SubAssign<&'a Self> for Jacobian<P> {
    #[inline]
    fn sub_assign(&mut self, other: &'a Self) {
        *self += &(-(*other));
    }
}

impl<'a, P: Parameters> Sub<&'a Self> for Jacobian<P> {
    type Output = Self;

    #[inline]
    fn sub(self, other: &'a Self) -> Self {
        let mut copy = self;
        copy -= other;
        copy
    }
}

impl<P: Parameters> SubAssign<Self> for Jacobian<P> {
    #[inline]
    fn sub_assign(&mut self, other: Self) {
        *self -= &other;
    }
}

impl<P: Parameters> Sub<Self> for Jacobian<P> {
    type Output = Self;

    #[inline]
    fn sub(self, other: Self) -> Self {
        self - &other
    }
}

impl<'a, P: Parameters> MulAssign<&'a P::ScalarField> for Jacobian<P> {
    /// WARNING: This implementation doesn't take costant time with respect
    /// to the exponent, and therefore is susceptible to side-channel attacks.
    /// Be sure to use it in applications where timing (or similar) attacks
    /// are not possible.
    /// TODO: Add a side-channel secure variant.
    fn mul_assign(&mut self, other: &'a P::ScalarField) {
        if !self.is_zero() {
            *self = self.mul_bits(BitIterator::new(Into::<
                <P::ScalarField as PrimeField>::BigInt,
            >::into(*other)))
        }
    }
}

impl<'a, P: Parameters> Mul<&'a P::ScalarField> for Jacobian<P> {
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
impl<P: Parameters> From<AffineRep<P>> for Jacobian<P> {
    #[inline]
    fn from(p: AffineRep<P>) -> Jacobian<P> {
        Self::new(p.x, p.y, P::BaseField::one())
    }
}

// The projective point X, Y, Z is represented in the affine
// coordinates as X/Z^2, Y/Z^3.
impl<P: Parameters> TryFrom<Jacobian<P>> for AffineRep<P> {
    type Error = Error;

    #[inline]
    fn try_from(p: Jacobian<P>) -> Result<AffineRep<P>, Error> {
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

impl<P: Parameters> ToCompressedBits for Jacobian<P> {
    #[inline]
    fn compress(&self) -> Vec<bool> {
        // Strictly speaking, self.x is zero already when self.infinity is true, but
        // to guard against implementation mistakes we do not assume this.
        let p = if self.is_zero() {
            P::BaseField::zero()
        } else {
            self.x
        };
        let mut res = p.write_bits();

        // Add infinity flag
        res.push(self.is_zero());

        // Add parity coordinate (set by default to false if self is infinity)
        res.push(!self.is_zero() && self.y.is_odd());

        res
    }
}

impl<P: Parameters> FromCompressedBits for Jacobian<P> {
    #[inline]
    fn decompress(compressed: Vec<bool>) -> Result<Self, Error> {
        let len = compressed.len() - 1;
        let parity_flag_set = compressed[len];
        let infinity_flag_set = compressed[len - 1];

        //Mask away the flag bits and try to get the x coordinate
        let x = P::BaseField::read_bits(compressed[0..(len - 1)].to_vec())?;
        match (infinity_flag_set, parity_flag_set, x.is_zero()) {
            //If the infinity flag is set, return the value assuming
            //the x-coordinate is zero and the parity bit is not set.
            (true, false, true) => Ok(Self::zero()),

            //If infinity flag is not set, then we attempt to construct
            //a point from the x coordinate and the parity.
            (false, _, _) => {
                //Attempt to get the y coordinate from its parity and x
                match Self::get_point_from_x_and_parity(x, parity_flag_set) {
                    //Check p belongs to the subgroup we expect
                    Some(p) => {
                        if p.is_in_correct_subgroup_assuming_on_curve() {
                            Ok(p)
                        } else {
                            let e = BitSerializationError::NotInCorrectSubgroup;
                            Err(Box::new(e))
                        }
                    }
                    _ => Err(Box::new(BitSerializationError::NotOnCurve)),
                }
            }

            //Other combinations are illegal
            _ => Err(Box::new(BitSerializationError::InvalidFlags)),
        }
    }
}

impl<P: Parameters> Zero for Jacobian<P> {
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
}

impl<P: Parameters> Group for Jacobian<P> {
    type ScalarField = P::ScalarField;

    fn double_in_place(&mut self) -> &mut Self {
        if self.is_zero() {
            return self;
        }

        if P::COEFF_A.is_zero() {
            // A = X1^2
            let mut a = self.x.square();

            // B = Y1^2
            let b = self.y.square();

            // C = B^2
            let mut c = b.square();

            // D = 2*((X1+B)2-A-C)
            let d = ((self.x + &b).square() - &a - &c).double();

            // E = 3*A
            let e = a + &*a.double_in_place();

            // F = E^2
            let f = e.square();

            // Z3 = 2*Y1*Z1
            self.z.mul_assign(&self.y);
            self.z.double_in_place();

            // X3 = F-2*D
            self.x = f - &d - &d;

            // Y3 = E*(D-X3)-8*C
            self.y = (d - &self.x) * &e - &*c.double_in_place().double_in_place().double_in_place();
            self
        } else {
            // http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l
            // XX = X1^2
            let xx = self.x.square();

            // YY = Y1^2
            let yy = self.y.square();

            // YYYY = YY^2
            let mut yyyy = yy.square();

            // ZZ = Z1^2
            let zz = self.z.square();

            // S = 2*((X1+YY)^2-XX-YYYY)
            let s = ((self.x + &yy).square() - &xx - &yyyy).double();

            // M = 3*XX+a*ZZ^2
            let m = xx + &xx + &xx + &P::mul_by_a(&zz.square());

            // T = M^2-2*S
            let t = m.square() - &s.double();

            // X3 = T
            self.x = t;
            // Y3 = M*(S-T)-8*YYYY
            let old_y = self.y;
            self.y = m * &(s - &t) - &*yyyy.double_in_place().double_in_place().double_in_place();
            // Z3 = (Y1+Z1)^2-YY-ZZ
            self.z = (old_y + &self.z).square() - &yy - &zz;
            self
        }
    }
}

impl<P: Parameters> Curve for Jacobian<P> {
    type BaseField = P::BaseField;
    type AffineRep = AffineRep<P>;

    fn add_affine<'a>(&self, other: &'a Self::AffineRep) -> Self {
        let mut copy = *self;
        copy.add_assign_affine(other);
        copy
    }

    fn add_assign_affine<'a>(&mut self, other: &'a Self::AffineRep) {
        if self.is_zero() {
            self.x = other.x;
            self.y = other.y;
            self.z = P::BaseField::one();
            return;
        }

        // http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-madd-2007-bl
        // Works for all curves.

        // Z1Z1 = Z1^2
        let z1z1 = self.z.square();

        // U2 = X2*Z1Z1
        let u2 = other.x * &z1z1;

        // S2 = Y2*Z1*Z1Z1
        let s2 = (other.y * &self.z) * &z1z1;

        if self.x == u2 && self.y == s2 {
            // The two points are equal, so we double.
            self.double_in_place();
        } else {
            // If we're adding -a and a together, self.z becomes zero as H becomes zero.

            // H = U2-X1
            let h = u2 - &self.x;

            // HH = H^2
            let hh = h.square();

            // I = 4*HH
            let mut i = hh;
            i.double_in_place().double_in_place();

            // J = H*I
            let mut j = h * &i;

            // r = 2*(S2-Y1)
            let r = (s2 - &self.y).double();

            // V = X1*I
            let v = self.x * &i;

            // X3 = r^2 - J - 2*V
            self.x = r.square();
            self.x -= &j;
            self.x -= &v;
            self.x -= &v;

            // Y3 = r*(V-X3)-2*Y1*J
            j *= &self.y; // J = 2*Y1*J
            j.double_in_place();
            self.y = v - &self.x;
            self.y *= &r;
            self.y -= &j;

            // Z3 = (Z1+H)^2-Z1Z1-HH
            self.z += &h;
            self.z.square_in_place();
            self.z -= &z1z1;
            self.z -= &hh;
        }
    }

    fn add_in_place_affine_many(to_add: &mut [Vec<Self::AffineRep>]) {
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

    fn mul_bits_affine<'a, S: AsRef<[u64]>>(
        affine: &'a Self::AffineRep,
        bits: BitIterator<S>,
    ) -> Self {
        let mut res = Self::zero();
        for i in bits {
            res.double_in_place();
            if i {
                res.add_assign_affine(&affine);
            }
        }
        res
    }

    fn scale_by_cofactor(&self) -> Self {
        let cofactor = BitIterator::new(P::COFACTOR);
        self.mul_bits(cofactor)
    }

    fn scale_by_cofactor_inv(&self) -> Self {
        let cofactor_inv = BitIterator::new(Into::<<P::ScalarField as PrimeField>::BigInt>::into(
            P::COFACTOR_INV,
        ));
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
            let normalized = self.normalize();
            let y2 = normalized.y.square();
            let x3b =
                P::add_b(&((normalized.x.square() * &normalized.x) + &P::mul_by_a(&normalized.x)));
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
            let dz2 = dz.square(); // 1/z
            self.x *= &dz2; // x/z^2
            self.y *= &(dz2 * &dz); // y/z^3
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
        #[cfg(not(feature = "parallel"))]
        {
            // Perform affine transformations
            for g in v.iter_mut().filter(|g| !g.is_normalized()) {
                let z2 = g.z.square(); // 1/z
                g.x *= &z2; // x/z^2
                g.y *= &(z2 * &g.z); // y/z^3
                g.z = P::BaseField::one(); // z = 1
            }
        }

        #[cfg(feature = "parallel")]
        {
            use rayon::prelude::*;
            // Perform affine transformations
            v.par_iter_mut()
                .filter(|g| !g.is_normalized())
                .for_each(|g| {
                    let z2 = g.z.square(); // 1/z
                    g.x *= &z2; // x/z^2
                    g.y *= &(z2 * &g.z); // y/z^3
                    g.z = P::BaseField::one(); // z = 1
                });
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
}

impl<P: EndoParameters> EndoMulCurve for Jacobian<P> {
    type Params = P;

    fn apply_endomorphism(&self) -> Self {
        let mut self_e = self.clone();
        self_e.x.mul_assign(P::ENDO_COEFF);
        self_e
    }
}
