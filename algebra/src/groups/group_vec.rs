use super::Group;
use crate::{bytes::{FromBytes, ToBytes, FromBytesChecked}, serialize::{CanonicalSerialize, CanonicalDeserialize, SerializationError}, SemanticallyValid, ToConstraintField, Error, UniformRand};
use std::{
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign, Index},
    io::{Read, Write, Error as IoError, ErrorKind, Result as IoResult},
    fmt::{Display, Formatter, Result as FmtResult},
    vec::IntoIter,
};
use core::slice::Iter;
use rand::Rng;

#[derive(Clone, PartialEq, Eq, Debug, Hash, CanonicalSerialize, CanonicalDeserialize)]
pub struct GroupVec<G: Group> (Vec<G>);

impl<G: Group> GroupVec<G> {

    pub fn new(items: Vec<G>) -> Self { GroupVec(items) }

    pub fn with_capacity(capacity: usize) -> Self {
        GroupVec(Vec::with_capacity(capacity))
    }

    pub fn get_vec(&self) -> Vec<G> { self.0.clone() }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn push(&mut self, item: G) {
        self.0.push(item)
    }

    pub fn iter(&self) -> Iter<'_, G> {
        self.0.iter()
    }

    pub fn into_iter(&self) -> IntoIter<G> {
        self.0.clone().into_iter()
    }

    pub fn rand<R: Rng + ?Sized>(len: u16, rng: &mut R) -> Self {
        Self::new((0..len).map(|_| G::rand(rng)).collect::<Vec<G>>())
    }
}

impl<G: Group> Index<usize> for GroupVec<G> {
    type Output = G;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl<G: Group> Default for GroupVec<G> {
    #[inline]
    fn default() -> Self {
        Self::zero()
    }
}

impl<G: Group> FromBytes for GroupVec<G> {
    #[inline]
    fn read<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(GroupVec(CanonicalDeserialize::deserialize_unchecked(&mut reader)
            .map_err(|e| IoError::new(ErrorKind::Other, format!{"{:?}", e}))?
        ))
    }
}

impl<G: Group> ToBytes for GroupVec<G> {
    #[inline]
    fn write<W: Write>(&self, mut writer: W) -> IoResult<()> {
        CanonicalSerialize::serialize(&self.0, &mut writer)
            .map_err(|e| IoError::new(ErrorKind::Other, format!{"{:?}", e}))
    }
}

impl<G: Group> FromBytesChecked for GroupVec<G> {
    fn read_checked<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(GroupVec(CanonicalDeserialize::deserialize(&mut reader)
            .map_err(|e| IoError::new(ErrorKind::Other, format!{"{:?}", e}))?
        ))
    }
}

impl<G: Group> SemanticallyValid for GroupVec<G> {
    fn is_valid(&self) -> bool {
        for item in self.0.iter() {
            if !item.is_valid() {
                return false;
            }
        }
        true
    }
}

impl<G: Group> Display for GroupVec<G> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        for (i, item) in self.0.iter().enumerate() {
            writeln!(f, "[{}]: {}", i, item)?;
        }
        Ok(())
    }
}

impl<G: Group> ToConstraintField<G::BaseField> for GroupVec<G> {
    fn to_field_elements(&self) -> Result<Vec<G::BaseField>, Error> {
        self.0.to_field_elements()
    }
}


impl<G: Group> Neg for GroupVec<G> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        GroupVec(self.0.iter().map(|item| -item.clone()).collect::<Vec<_>>())
    }
}

impl<'a, G: Group> AddAssign<&'a Self> for GroupVec<G> {
    fn add_assign(&mut self, other: &'a Self) {
        if self.0.len() < other.0.len() {
            self.0.resize(other.0.len(), G::zero());
        }
        for (i, item) in other.0.iter().enumerate() {
            self.0[i] += item;
        }
    }
}

impl<'a, G: Group> Add<&'a Self> for GroupVec<G> {
    type Output = Self;

    #[inline]
    fn add(self, other: &'a Self) -> Self {
        let mut copy = self;
        copy += other;
        copy
    }
}

impl<G: Group> AddAssign<Self> for GroupVec<G> {
    #[inline]
    fn add_assign(&mut self, other: Self) {
        *self += &other;
    }
}

impl<G: Group> Add<Self> for GroupVec<G> {
    type Output = Self;

    #[inline]
    fn add(self, other: Self) -> Self {
        self + &other
    }
}

impl<'a, G: Group> SubAssign<&'a Self> for GroupVec<G> {
    fn sub_assign(&mut self, other: &'a Self) {
        if self.0.len() < other.0.len() {
            self.0.resize(other.0.len(), G::zero());
        }
        for (i, item) in other.0.iter().enumerate() {
            self.0[i] -= item;
        }
    }
}

impl<'a, G: Group> Sub<&'a Self> for GroupVec<G> {
    type Output = Self;

    #[inline]
    fn sub(self, other: &'a Self) -> Self {
        let mut copy = self;
        copy -= other;
        copy
    }
}

impl<G: Group> SubAssign<Self> for GroupVec<G> {
    #[inline]
    fn sub_assign(&mut self, other: Self) {
        *self -= &other;
    }
}

impl<G: Group> Sub<Self> for GroupVec<G> {
    type Output = Self;

    #[inline]
    fn sub(self, other: Self) -> Self {
        self - &other
    }
}

impl<'a, G: Group> MulAssign<&'a G::ScalarField> for GroupVec<G> {

    fn mul_assign(&mut self, other: &'a G::ScalarField) {
        for i in 0..self.0.len() {
            self.0[i] *= other;
        }
    }
}

impl<'a, G: Group> Mul<&'a G::ScalarField> for GroupVec<G> {
    type Output = Self;

    #[inline]
    fn mul(self, other: &'a G::ScalarField) -> Self {
        let mut copy = self;
        copy *= other;
        copy
    }
}

impl<G: Group> UniformRand for GroupVec<G> {
    fn rand<R: Rng + ?Sized>(rng: &mut R) -> Self {
        Self::rand(rng.gen(), rng)
    }
}

impl<G: Group> Group for GroupVec<G> {
    type BaseField = G::BaseField;
    type ScalarField = G::ScalarField;

    fn zero() -> Self {
        GroupVec(vec![])
    }

    fn is_zero(&self) -> bool {
        self.0.len() == 0
    }

    fn double_in_place(&mut self) -> &mut Self {
        for (i, item) in self.0.clone().iter().enumerate() {
            self.0[i] += item;
        }
        self
    }
}