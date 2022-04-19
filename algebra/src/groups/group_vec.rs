use super::Group;
use crate::{
    bytes::{FromBytes, ToBytes, FromBytesChecked},
    serialize::{CanonicalSerialize, CanonicalDeserialize, SerializationError},
    SemanticallyValid,
};
use std::{
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign, Index},
    io::{Read, Write, Error as IoError, ErrorKind, Result as IoResult},
    fmt::{Display, Formatter, Result as FmtResult},
    vec::IntoIter,
};
use rand::{
    distributions::{Distribution, Standard},
    Rng,
};
use itertools::{EitherOrBoth, Itertools};
use core::slice::Iter;
use num_traits::Zero;
use serde::*;

#[derive(Clone, Debug, Hash, CanonicalSerialize, CanonicalDeserialize, Serialize, Deserialize)]
#[serde(bound(deserialize = "G: Group"))]
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

// The trait PartialEq cannot be simply derived, because this would cause wrong results when
// comparing vectors which are equal apart from a different number of trailing zeros (in
// particular when comparing different representations of the zero vector).
impl<G: Group> PartialEq<Self> for GroupVec<G> {
    fn eq(&self, other: &Self) -> bool {
        self.0
            .iter()
            .zip_longest(other.0.iter())
            .all(|elems| match elems {
                EitherOrBoth::Both(g1, g2) => g1 == g2,
                EitherOrBoth::Left(g) => g.is_zero(),
                EitherOrBoth::Right(g) => g.is_zero(),
            })
    }
}

impl<G: Group> Eq for GroupVec<G> {}

impl<G: Group> Distribution<GroupVec<G>> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, _rng: &mut R) -> GroupVec<G> {
        unimplemented!("use the specific function `rand` which allows to specify the length of the vector")
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

impl<G: Group> Zero for GroupVec<G> {
    #[inline]
    fn zero() -> Self {
        GroupVec(vec![])
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0.is_empty() || self.0.iter().all(|ge| ge.is_zero())
    }
}

impl<G: Group> Neg for GroupVec<G> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        GroupVec(self.0.iter().map(|item| -item.clone()).collect::<Vec<_>>())
    }
}

impl<'a, G: Group> Neg for &'a GroupVec<G> {
    type Output = GroupVec<G>;

    #[inline]
    fn neg(self) -> Self::Output {
        let copy = self.clone();
        -copy
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

impl<'a, 'b, G: Group> Add<&'a GroupVec<G>> for &'b GroupVec<G> {
    type Output = GroupVec<G>;

    #[inline]
    fn add(self, other: &'a GroupVec<G>) -> Self::Output {
        let copy = self.clone();
        copy + other
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

impl<'a, 'b, G: Group> Sub<&'a GroupVec<G>> for &'b GroupVec<G> {
    type Output = GroupVec<G>;

    #[inline]
    fn sub(self, other: &'a GroupVec<G>) -> Self::Output {
        let copy = self.clone();
        copy - other
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

impl<'a, 'b, G: Group> Mul<&'a G::ScalarField> for &'b GroupVec<G> {
    type Output = GroupVec<G>;

    #[inline]
    fn mul(self, other: &'a G::ScalarField) -> Self::Output {
        let copy = self.clone();
        copy * other
    }
}

impl<G: Group> Group for GroupVec<G> {
    type ScalarField = G::ScalarField;

    fn double_in_place(&mut self) -> &mut Self {
        for (i, item) in self.0.clone().iter().enumerate() {
            self.0[i] += item;
        }
        self
    }
}

#[cfg(all(test, feature = "tweedle"))]
mod tests {
    use super::*;
    use crate::{
        fields::tweedle::Fr,
        curves::tweedle::dee::DeeJacobian as TweedleDee, UniformRand,
    };
    use rand::{SeedableRng, thread_rng};
    use num_traits::{Zero, One};
    use rand_xorshift::XorShiftRng;

    const MAX_LENGTH: u16 = 10;

    // Copy of group_test in algebra/src/groups/tests.rs, needed as GroupVec doesn't implement Copy.
    #[test]
    fn group_vec_group_test() {
        let (a, mut b) = {
            let rng = &mut thread_rng();
            let a_len: u16 = rng.gen_range(1..MAX_LENGTH);
            let b_len: u16 = rng.gen_range(1..MAX_LENGTH);
            (GroupVec::<TweedleDee>::rand(a_len, rng), GroupVec::<TweedleDee>::rand(b_len, rng))
        };

        let mut rng = XorShiftRng::seed_from_u64(1231275789u64);
        let zero = GroupVec::<TweedleDee>::zero();
        let fr_zero = Fr::zero();
        let fr_one = Fr::one();
        let fr_two = fr_one + &fr_one;
        assert_eq!(zero.is_zero(), true);
        assert_eq!(&(&a).mul(&fr_one), &a);
        assert_eq!((&a).mul(&fr_two), &a + &a);
        assert_eq!(&(&a).mul(&fr_zero), &zero);
        assert_eq!(&((&a).mul(&fr_zero) - &a), &-&a);
        assert_eq!(&((&a).mul(&fr_one) - &a), &zero);
        assert_eq!(&((&a).mul(&fr_two) - &a), &a);
    
        // a + 0 = a
        assert_eq!(&(&a + &zero), &a);
        // a - 0 = a
        assert_eq!(&(&a - &zero), &a);
        // a - a = 0
        assert_eq!(&(&a - &a), &zero);
        // 0 - a = -a
        assert_eq!(&(&zero - &a), &-&a);
        // a.double() = a + a
        assert_eq!(&(a.double()), &(&a + &a));
        // b.double() = b + b
        assert_eq!(&(b.double()), &(&b + &b));
        // a + b = b + a
        assert_eq!(&(&a + &b), &(&b + &a));
        // a - b = -(b - a)
        assert_eq!(&(&a - &b), &-&(&b - &a));
        // (a + b) + a = a + (b + a)
        assert_eq!(&(&(&a + &b) + &a), &(&a + &(&b + &a)));
        // (a + b).double() = (a + b) + (b + a)
        assert_eq!(&(&(&a + &b).double()), &(&(&(&a + &b) + &(&b + &a))));
    
        // Check that double_in_place and double give the same result
        let original_b = b.clone();
        b.double_in_place();
        assert_eq!(&original_b.double(), &b);
    
        let fr_rand1 = Fr::rand(&mut rng);
        let fr_rand2 = Fr::rand(&mut rng);
        let a_rand1 = (&a).mul(&fr_rand1);
        let a_rand2 = (&a).mul(&fr_rand2);
        let fr_three = fr_two + &fr_rand1;
        let a_two = (&a).mul(&fr_two);
        assert_eq!(&a_two, &a.double(), "(a * 2)  != a.double()");
        let a_six = (&a).mul(&(fr_three * &fr_two));
        assert_eq!((&a_two).mul(&fr_three), a_six, "(a * 2) * 3 != a * (2 * 3)");
    
        assert_eq!(
            (&a_rand1).mul(&fr_rand2),
            (&a_rand2).mul(&fr_rand1),
            "(a * r1) * r2 != (a * r2) * r1"
        );
        assert_eq!(
            (&a_rand2).mul(&fr_rand1),
            (&a).mul(&(fr_rand1 * &fr_rand2)),
            "(a * r2) * r1 != a * (r1 * r2)"
        );
        assert_eq!(
            (&a_rand1).mul(&fr_rand2),
            (&a).mul(&(fr_rand1 * &fr_rand2)),
            "(a * r1) * r2 != a * (r1 * r2)"
        );
    }

    #[test]
    fn double_group_vec_random() {
        let rng = &mut thread_rng();
        for len in 0..MAX_LENGTH {
            let gv = GroupVec::<TweedleDee>::rand(len, rng);
            let gv_double = &gv + &gv;
            let gv_quad = &gv_double + &gv_double;
            assert_eq!(&(&(&gv + &gv) + &gv) + &gv, gv_quad);
        }
    }

    #[test]
    fn add_group_vec_random() {
        let rng = &mut thread_rng();
        for a_len in 0..MAX_LENGTH {
            for b_len in 0..MAX_LENGTH {
                let gv1 = GroupVec::<TweedleDee>::rand(a_len, rng);
                let gv2 = GroupVec::<TweedleDee>::rand(b_len, rng);
                let res1 = &gv1 + &gv2;
                let res2 = &gv2 + &gv1;
                assert_eq!(res1, res2);
            }
        }
    }

    #[test]
    fn add_group_vec_with_mul() {
        let rng = &mut thread_rng();
        for a_len in 0..MAX_LENGTH {
            for b_len in 0..MAX_LENGTH {
                let mut gv1 = GroupVec::rand(a_len, rng);
                let gv2 = GroupVec::rand(b_len, rng);
                let scalar = Fr::rand(rng);
                let scalar_gv2 = GroupVec::new(
                    gv2.0.iter().map(|c| scalar * c).collect(),
                );
                let res2 = &scalar_gv2 + &gv1;
                gv1 += gv2 * &scalar;
                let res1 = gv1;
                assert_eq!(res1, res2);
            }
        }
    }

    #[test]
    fn sub_group_vec() {
        let rng = &mut thread_rng();
        let gv1 = GroupVec::<TweedleDee>::rand(5, rng);
        let gv2 = GroupVec::<TweedleDee>::rand(3, rng);
        let res1 = &gv1 - &gv2;
        let res2 = &gv2 - &gv1;
        assert_eq!(
            &res1 + &gv2,
            gv1,
            "Subtraction should be inverse of addition!"
        );
        assert_eq!(res1, -res2, "gv2 - gv1 = -(gv1 - gv2)");
    }

    #[test]
    fn cmp_group_vec() {
        use rand::Rng;

        let rng = &mut thread_rng();

        for group_elements_len in 0..MAX_LENGTH {
            // Sample random group_elements
            let mut group_elements = (0..group_elements_len).map(|_| TweedleDee::rand(rng)).collect::<Vec<_>>();

            // Init gv a with such group_elements
            let a = GroupVec::<TweedleDee>::new(group_elements.clone());

            // Pad with 0s up to max_len
            group_elements.append(&mut vec![TweedleDee::zero(); (MAX_LENGTH - group_elements_len) as usize]);
            let mut b = GroupVec::<TweedleDee>::new(group_elements.clone());

            // We expect gvs to be considered equal
            assert_eq!(a, b);

            // Changing one coeff will lead to inequality
            let random_idx: usize = rng.gen_range(group_elements_len as usize..MAX_LENGTH as usize);
            b.0[random_idx] = TweedleDee::rand(rng);
            assert_ne!(a, b);
        }
    }
}
