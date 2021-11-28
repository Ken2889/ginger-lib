use super::Group;
use crate::{
    bytes::{FromBytes, ToBytes, FromBytesChecked},
    serialize::{CanonicalSerialize, CanonicalDeserialize, SerializationError},
    SemanticallyValid,
};
use std::{
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
    io::{Read, Write, Result as IoResult},
    fmt::{Display, Formatter, Result as FmtResult},
};

#[derive(Clone, PartialEq, Eq, Debug, Hash, CanonicalSerialize, CanonicalDeserialize)]
pub struct GroupVec<G: Group> (Vec<G>);

impl<G: Group> Default for GroupVec<G> {
    #[inline]
    fn default() -> Self {
        Self::zero()
    }
}

impl<G: Group> FromBytes for GroupVec<G> {
    #[inline]
    fn read<R: Read>(mut reader: R) -> IoResult<Self> {
        let len = u64::read(&mut reader)?;
        let mut items = vec![];
        for _ in 0..(len as usize) {
            let item = G::read(&mut reader)?;
            items.push(item)
        }
        Ok(GroupVec(items))
    }
}

impl<G: Group> ToBytes for GroupVec<G> {
    #[inline]
    fn write<W: Write>(&self, mut writer: W) -> IoResult<()> {
        (self.0.len() as u64).write(&mut writer)?;
        for item in self.0.iter() {
            item.write(&mut writer)?;
        }
        Ok(())
    }
}

impl<G: Group> FromBytesChecked for GroupVec<G> {
    fn read_checked<R: Read>(mut reader: R) -> IoResult<Self> {
        let len = u64::read(&mut reader)?;
        let mut items = vec![];
        for _ in 0..(len as usize) {
            let item = G::read_checked(&mut reader)?;
            items.push(item)
        }
        Ok(GroupVec(items))
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

impl<G: Group> Group for GroupVec<G> {
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
