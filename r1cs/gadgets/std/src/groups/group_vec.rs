use std::borrow::Borrow;
use std::fmt::Debug;
use std::marker::PhantomData;
use num_traits::Zero;
use algebra::{Field, Group, GroupVec};
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use crate::boolean::Boolean;
use crate::eq::EqGadget;
use crate::groups:: GroupGadget;
use crate::prelude::{CondSelectGadget, UInt8};
use crate::{ToBitsGadget, ToBytesGadget};
use crate::alloc::{AllocGadget, ConstantGadget};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GroupGadgetVec<ConstraintF: Field, G: Group, GG: GroupGadget<G, ConstraintF>> {
    vec: Vec<GG>,
    _field: PhantomData<ConstraintF>,
    _group: PhantomData<G>,
}

impl<ConstraintF: Field, G: Group, GG: GroupGadget<G, ConstraintF>> GroupGadgetVec<ConstraintF, G, GG> {

    pub fn new(items: Vec<GG>) -> Self { Self {
        vec: items,
        _field: PhantomData,
        _group: PhantomData,
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            vec: Vec::with_capacity(capacity),
            _field: PhantomData,
            _group: PhantomData
        }
    }

    pub fn get_vec(&self) -> Vec<GG> { self.vec.clone() }

    pub fn len(&self) -> usize {
        self.vec.len()
    }

    pub fn push(&mut self, item: GG) {
        self.vec.push(item)
    }

    pub fn iter(&self) -> impl DoubleEndedIterator<Item=&GG> {
        self.vec.iter()
    }

    pub fn into_iter(&self) -> impl IntoIterator<Item=GG> {
        self.vec.clone().into_iter()
    }

    /// this function allows to generate the zero element of `GroupGadgetVec as GroupGadget`.
    /// It replaces the `zero` function of `GroupGadget`, as the latter does not allow to specify
    /// the length of the zero vector
    pub fn zero<CS: ConstraintSystemAbstract<ConstraintF>>(mut cs: CS, length: u16) -> Result<Self, SynthesisError> {
        Ok(
            Self::new(
            (0..length).map(|i| GG::zero(cs.ns(|| format!("alloc {}-th zero element", i)))).collect::<Result<Vec<_>, SynthesisError>>()?
            )
        )
    }
}


impl<ConstraintF: Field, G: Group, GG: GroupGadget<G, ConstraintF>> ToBytesGadget<ConstraintF> for GroupGadgetVec<ConstraintF, G, GG> {
    fn to_bytes<CS: ConstraintSystemAbstract<ConstraintF>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let mut res_vec = Vec::new();
        for (i, el) in self.iter().enumerate() {
            let el_to_bytes = el.to_bytes(cs.ns(|| format!("convert element {} to bytes", i)))?;
            res_vec.extend_from_slice(el_to_bytes.as_slice());
        }
        Ok(res_vec)
    }

    fn to_bytes_strict<CS: ConstraintSystemAbstract<ConstraintF>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let mut res_vec = Vec::new();
        for (i, el) in self.iter().enumerate() {
            let el_to_bytes = el.to_bytes_strict(cs.ns(|| format!("convert element {} to bytes with check", i)))?;
            res_vec.extend_from_slice(el_to_bytes.as_slice());
        }
        Ok(res_vec)
    }
}

impl<ConstraintF: Field, G: Group, GG: GroupGadget<G, ConstraintF>> EqGadget<ConstraintF> for GroupGadgetVec<ConstraintF, G, GG> {
    fn is_eq<CS: ConstraintSystemAbstract<ConstraintF>>(&self, mut cs: CS, other: &Self) -> Result<Boolean, SynthesisError> {
        if self.len() != other.len() {
            Err(SynthesisError::Unsatisfiable)?
        }
        let mut are_elements_eq = Vec::with_capacity(self.len());
        for (i, (el1, el2)) in self.iter().zip(other.iter()).enumerate() {
            let is_eq = el1.is_eq(cs.ns(|| format!("self[{}] == other[{}]", i,i)), el2)?;
            are_elements_eq.push(is_eq);
        }
        Boolean::kary_and(cs.ns(|| "compute equality flag from element wise flags"), &are_elements_eq)
    }
}

impl<ConstraintF: Field, G: Group, GG: GroupGadget<G, ConstraintF>> ToBitsGadget<ConstraintF> for GroupGadgetVec<ConstraintF, G, GG> {
    fn to_bits<CS: ConstraintSystemAbstract<ConstraintF>>(&self, mut cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        let mut res_vec = Vec::new();
        for (i, el) in self.iter().enumerate() {
            let el_to_bits = el.to_bits(cs.ns(|| format!("convert element {} to bits", i)))?;
            res_vec.extend_from_slice(el_to_bits.as_slice());
        }
        Ok(res_vec)
    }

    fn to_bits_strict<CS: ConstraintSystemAbstract<ConstraintF>>(&self, mut cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        let mut res_vec = Vec::new();
        for (i, el) in self.iter().enumerate() {
            let el_to_bits = el.to_bits_strict(cs.ns(|| format!("convert element {} to bits with check", i)))?;
            res_vec.extend_from_slice(el_to_bits.as_slice());
        }
        Ok(res_vec)
    }
}

impl<ConstraintF: Field, G: Group, GG: GroupGadget<G, ConstraintF>> CondSelectGadget<ConstraintF> for GroupGadgetVec<ConstraintF, G, GG> {
    fn conditionally_select<CS: ConstraintSystemAbstract<ConstraintF>>(mut cs: CS, cond: &Boolean, first: &Self, second: &Self) -> Result<Self, SynthesisError> {
        if first.len() != second.len() {
            Err(SynthesisError::Other(format!("cond select between group gadget vectors with different lengths: self.len = {}, other.len = {}", first.len(), second.len())))?
        }

        let mut res_vec = Vec::new();
        for (i,(el1, el2)) in first.iter().zip(second.iter()).enumerate() {
            res_vec.push(GG::conditionally_select(cs.ns(|| format!("cond select element {}", i)), cond, el1, el2)?);
        }

        Ok(Self::new(res_vec))
    }

    fn cost() -> usize {
        unimplemented!()
    }
}

impl<ConstraintF: Field, G: Group, GG: GroupGadget<G, ConstraintF>> AllocGadget<GroupVec<G>, ConstraintF> for GroupGadgetVec<ConstraintF, G, GG> {
    fn alloc<F, T, CS: ConstraintSystemAbstract<ConstraintF>>(mut cs: CS, f: F) -> Result<Self, SynthesisError> where F: FnOnce() -> Result<T, SynthesisError>, T: Borrow<GroupVec<G>> {
        let t = f()?;
        let vec = t.borrow();
        let mut gadget_vec = Vec::with_capacity(vec.len());
        for (i, el) in vec.iter().enumerate() {
            gadget_vec.push(GG::alloc(cs.ns(|| format!("alloc gadget for element {}", i)), || Ok(el))?);
        }
        Ok(Self::new(gadget_vec))
    }

    fn alloc_input<F, T, CS: ConstraintSystemAbstract<ConstraintF>>(mut cs: CS, f: F) -> Result<Self, SynthesisError> where F: FnOnce() -> Result<T, SynthesisError>, T: Borrow<GroupVec<G>> {
        let t = f()?;
        let vec = t.borrow();
        let mut gadget_vec = Vec::with_capacity(vec.len());
        for (i, el) in vec.iter().enumerate() {
            gadget_vec.push(GG::alloc(cs.ns(|| format!("alloc gadget for element {}", i)), || Ok(el))?);
        }
        Ok(Self::new(gadget_vec))
    }
}

impl<ConstraintF: Field, G: Group, GG: GroupGadget<G, ConstraintF>> ConstantGadget<GroupVec<G>, ConstraintF> for GroupGadgetVec<ConstraintF, G, GG> {
    fn from_value<CS: ConstraintSystemAbstract<ConstraintF>>(mut cs: CS, value: &GroupVec<G>) -> Self {
        let mut res_vec = Vec::with_capacity(value.len());
        for (i, el) in value.iter().enumerate() {
            res_vec.push(GG::from_value(cs.ns(|| format!("alloc constant element {}", i)), el));
        }

        Self::new(res_vec)
    }

    fn get_constant(&self) -> GroupVec<G> {
        let mut res_vec = Vec::with_capacity(self.len());
        for el in self.iter() {
            res_vec.push(el.get_constant());
        }

        GroupVec::<G>::new(res_vec)
    }
}

impl<ConstraintF: Field, G: Group, GG: GroupGadget<G, ConstraintF>> GroupGadget<GroupVec<G>, ConstraintF> for GroupGadgetVec<ConstraintF, G, GG> {
    type Value = Vec<GG::Value>;
    type Variable = Vec<GG::Variable>;

    fn get_value(&self) -> Option<Self::Value> {
        let mut vec = Vec::with_capacity(self.len());
        for gg in self.iter() {
            match gg.get_value() {
                Some(g) => vec.push(g),
                None => return None,
            };
        }
        Some(vec)
    }

    fn get_variable(&self) -> Self::Variable {
        let mut variables = Vec::with_capacity(self.len());
        for gg in self.iter() {
            variables.push(gg.get_variable());
        }
        variables
    }

    fn zero<CS: ConstraintSystemAbstract<ConstraintF>>(_cs: CS) -> Result<Self, SynthesisError> {
        unimplemented!("use the publicly available function `zero` of `GroupGadgetVec`, which allows to specify the length of the zero element to be generated")
    }

    fn is_zero<CS: ConstraintSystemAbstract<ConstraintF>>(&self, mut cs: CS) -> Result<Boolean, SynthesisError> {
        let mut zero_flags = Vec::with_capacity(self.len());
        for (i, gg) in self.iter().enumerate() {
            zero_flags.push(gg.is_zero(cs.ns(|| format!("check if element {} is zero", i)))?);
        }
        // ToDo: this will be really cheap once we optimize kary_and as in zcash
        Boolean::kary_and(cs.ns(|| "check if all elements are zero"), zero_flags.as_slice())
    }

    fn add<CS: ConstraintSystemAbstract<ConstraintF>>(&self, mut cs: CS, other: &Self) -> Result<Self, SynthesisError> {
        let mut sum_vec = self.iter()
            .zip(other.iter())
            .enumerate()
            .map(|(i,(el1, el2))| {
                el1.add(cs.ns(|| format!("self[{}]+other[{}]",i,i)), el2)
            }).collect::<Result<Vec<_>, SynthesisError>>()?;
        let self_len = self.len();
        let other_len = other.len();
        if self_len > other_len {
            sum_vec.extend_from_slice(&self.vec.as_slice()[other_len..])
        } else {
            sum_vec.extend_from_slice(&other.vec.as_slice()[self_len..])
        }
        Ok(Self::new(sum_vec))
    }

    fn add_constant<CS: ConstraintSystemAbstract<ConstraintF>>(&self, mut cs: CS, other: &GroupVec<G>) -> Result<Self, SynthesisError> {
        if other.is_zero() {
            return Ok(self.clone());
        }
        let mut sum_vec = self.iter()
            .zip(other.iter())
            .enumerate()
            .map(|(i,(el1, el2))| {
                el1.add_constant(cs.ns(|| format!("self[{}]+other[{}]",i,i)), el2)
            }).collect::<Result<Vec<_>, SynthesisError>>()?;
        let self_len = self.len();
        let other_len = other.len();
        if self_len > other_len {
            sum_vec.extend_from_slice(&self.vec.as_slice()[other_len..])
        } else {
            let other_vec = other.iter().skip(self_len).enumerate().map(|(i, el)| GG::from_value(cs.ns(|| format!("alloc constant element {} of other", self_len+i)), el)).collect::<Vec<_>>();
            sum_vec.extend_from_slice(&other_vec.as_slice())
        }
        Ok(Self::new(sum_vec))
    }

    fn double_in_place<CS: ConstraintSystemAbstract<ConstraintF>>(&mut self, mut cs: CS) -> Result<(), SynthesisError> {
        for (i, el) in self.vec.iter_mut().enumerate() {
            el.double_in_place(cs.ns(|| format!("double self[{}]", i)))?
        }
        Ok(())
    }

    fn negate<CS: ConstraintSystemAbstract<ConstraintF>>(&self, mut cs: CS) -> Result<Self, SynthesisError> {
        let res_vec = self.iter().enumerate().map(|(i, el)| {
            el.negate(cs.ns(|| format!("negate self[{}]", i)))
        }).collect::<Result<Vec<_>, SynthesisError>>()?;
        Ok(Self::new(res_vec))
    }

    fn mul_bits<'a, CS: ConstraintSystemAbstract<ConstraintF>>(&self, mut cs: CS, bits: impl Iterator<Item=&'a Boolean>) -> Result<Self, SynthesisError> {
        let mut res_vec = Vec::with_capacity(self.len());
        let bits = bits.cloned().collect::<Vec<_>>();
        for (i,el) in self.iter().enumerate() {
            let el_times_bits = el.mul_bits(cs.ns(|| format!("self[{}]*bits", i)), bits.iter())?;
            res_vec.push(el_times_bits)
        }
        Ok(Self::new(res_vec))
    }


    fn mul_bits_fixed_base<CS: ConstraintSystemAbstract<ConstraintF>>(base: &GroupVec<G>, mut cs: CS, bits: &[Boolean]) -> Result<Self, SynthesisError> {
        let mut res_vec = Vec::with_capacity(base.len());
        for (i, el) in base.iter().enumerate() {
            res_vec.push(GG::mul_bits_fixed_base(el, cs.ns(|| format!("mul bits for fixed base {}", i)), bits)?);
        }

        Ok(Self::new(res_vec))
    }


    fn cost_of_add() -> usize {
        unimplemented!()
    }

    fn cost_of_double() -> usize {
        unimplemented!()
    }

    fn mul_bits_fixed_base_with_precomputed_base_powers<'a, CS, I, B>(&mut self, _cs: CS, _scalar_bits_with_base_powers: I) -> Result<(), SynthesisError> where CS: ConstraintSystemAbstract<ConstraintF>, I: Iterator<Item=(B, &'a GroupVec<G>)>, B: Borrow<Boolean>, GroupVec<G>: 'a {
        unimplemented!()
    }

    fn mul_bits_fixed_base_with_3_bit_signed_digit_precomputed_base_powers<'a, CS, I, J, B>(_cs: CS, _bases: &[B], _powers: &[J]) -> Result<Self, SynthesisError> where CS: ConstraintSystemAbstract<ConstraintF>, I: Borrow<[Boolean]>, J: Borrow<[I]>, B: Borrow<[GroupVec<G>]> {
        unimplemented!()
    }

    fn fixed_base_msm_with_precomputed_base_powers<'a, CS, T, I, B>(_cs: CS, _bases: &[B], _scalars: I) -> Result<Self, SynthesisError> where CS: ConstraintSystemAbstract<ConstraintF>, T: 'a + ToBitsGadget<ConstraintF> + ?Sized, I: Iterator<Item=&'a T>, B: Borrow<[GroupVec<G>]> {
        unimplemented!()
    }

    fn fixed_base_msm<'a, CS, T, IS, IB>(_cs: CS, _bases: IB, _scalars: IS) -> Result<Self, SynthesisError> where CS: ConstraintSystemAbstract<ConstraintF>, T: 'a + ToBitsGadget<ConstraintF> + ?Sized, IS: Iterator<Item=&'a T>, IB: Iterator<Item=&'a GroupVec<G>> {
        unimplemented!()
    }
}