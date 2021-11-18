//! Definition of NonNativeFieldGadget and implementation of
//!     - certain low-level arithmetic operations (without reduction),
//!     - the FieldGadget trait,
//! as well as the following auxiliary traits:
//!     - ToBitsGadget, ConstantGadget, ToBitsGadget, ToBytesGadget,
//!     - CondSelectGadget, TwoBitLookup, ThreeBitCondNegLookupGadget,
//!     - AllocGadget, ToConstraintFieldGadget, CloneGadget
//! and the
//!     - EqGadget, which heaviliy uses reduction of non-natives from reduce.rs
use algebra::{BigInteger, FpParameters, PrimeField};

use crate::fields::nonnative::NonNativeFieldParams;
use crate::{
    fields::fp::FpGadget,
    fields::nonnative::{
        nonnative_field_mul_result_gadget::NonNativeFieldMulResultGadget,
        params::get_params,
        reduce::{bigint_to_constraint_field, limbs_to_bigint, Reducer},
    },
    fields::FieldGadget,
    overhead,
    prelude::*,
    to_field_gadget_vec::ToConstraintFieldGadget,
    Assignment,
};
use r1cs_core::{ConstraintSystem, SynthesisError};
use std::cmp::{max, min};
use std::marker::PhantomData;
use std::{borrow::Borrow, vec, vec::Vec};

#[derive(Debug, Eq, PartialEq)]
#[must_use]
pub struct NonNativeFieldGadget<SimulationF: PrimeField, ConstraintF: PrimeField> {
    /// The limbs as elements of ConstraintF, big endian ordered.
    /// Recall that in the course of arithmetic operations bits the bit length of
    /// a limb exceeds `NonNativeFieldParams::bits_per_limb`. Reduction transforms
    /// back to normal form, which again has at most `bits_per_limb` many bits (but
    /// is not necessarily below the non-native modulus).
    pub limbs: Vec<FpGadget<ConstraintF>>,
    /// Number of additions done over this gadget without transforming back to
    /// normal form. Used by gadgets to decide when to reduce.
    pub num_of_additions_over_normal_form: ConstraintF,
    /// Whether the limb representation is the normal form, i.e. has the same
    /// number of bits as the non-native modulus (?)
    pub is_in_the_normal_form: bool,
    #[doc(hidden)]
    pub simulation_phantom: PhantomData<SimulationF>,
}

/// Low-level functions that do not make use of normalization.
impl<SimulationF: PrimeField, ConstraintF: PrimeField>
    NonNativeFieldGadget<SimulationF, ConstraintF>
{
    /// Obtain the non-native value from a vector of not necessarily normalized
    /// limb elements.
    // TODO: Can we use the functions limbs_to_bigint and bigint_to_constraint_field ? Logic seems duplicated
    pub fn limbs_to_value(limbs: Vec<ConstraintF>) -> SimulationF {
        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());

        let mut base_repr: <SimulationF as PrimeField>::BigInt = SimulationF::one().into_repr();

        // Compute base = 2^{params.bits_per_limb} in SimulationF.
        // Note that in cases where non-natives are just single limb sized, 2^{(params.bits_per_limb)}
        // exceeds the modulus of SimulationF. Thus we compute as follows.
        base_repr.muln((params.bits_per_limb - 1) as u32);
        let mut base = SimulationF::from_repr(base_repr);
        base = base + &base;

        let mut result = SimulationF::zero();
        let mut power = SimulationF::one();

        for limb in limbs.iter().rev() {
            let mut val = SimulationF::zero();
            let mut cur = SimulationF::one();

            // Take all bits of the field element limb into account, even the ones
            // that exceed the bits_per_limb.
            for bit in limb.into_repr().to_bits().iter().rev() {
                if *bit {
                    val += &cur;
                }
                cur.double_in_place();
            }

            result += &(val * power);
            power *= &base;
        }

        result
    }

    /// Subtract a nonnative field element, without the final reduction step
    pub fn sub_without_reduce<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());

        // Step 1: reduce the `other` if needed
        let mut surfeit =
            overhead!(other.num_of_additions_over_normal_form + ConstraintF::one()) + 1;
        let mut other = other.clone();
        if (surfeit + params.bits_per_limb > ConstraintF::size_in_bits() - 1)
            || (surfeit
                + (SimulationF::size_in_bits() - params.bits_per_limb * (params.num_limbs - 1))
                > ConstraintF::size_in_bits() - 1)
        {
            Reducer::reduce(cs.ns(|| "reduce other"), &mut other)?;
            surfeit = overhead!(other.num_of_additions_over_normal_form + ConstraintF::one()) + 1;
        }

        // Step 2: construct the padding
        let mut pad_non_top_limb_repr: <ConstraintF as PrimeField>::BigInt =
            ConstraintF::one().into_repr();
        let mut pad_top_limb_repr: <ConstraintF as PrimeField>::BigInt = pad_non_top_limb_repr;

        pad_non_top_limb_repr.muln((surfeit + params.bits_per_limb) as u32);
        let pad_non_top_limb = ConstraintF::from_repr(pad_non_top_limb_repr);

        pad_top_limb_repr.muln(
            (surfeit
                + (SimulationF::size_in_bits() - params.bits_per_limb * (params.num_limbs - 1)))
                as u32,
        );
        let pad_top_limb = ConstraintF::from_repr(pad_top_limb_repr);

        let mut pad_limbs = Vec::new();
        pad_limbs.push(pad_top_limb);
        for _ in 0..self.limbs.len() - 1 {
            pad_limbs.push(pad_non_top_limb);
        }

        // Step 3: prepare to pad the padding to k * p for some k
        let pad_to_kp_gap = Self::limbs_to_value(pad_limbs).neg();
        let pad_to_kp_limbs = Self::get_limbs_representations(&pad_to_kp_gap)?;

        // Step 4: the result is self + pad + pad_to_kp - other
        let mut limbs = Vec::new();
        for (i, ((this_limb, other_limb), pad_to_kp_limb)) in self
            .limbs
            .iter()
            .zip(other.limbs.iter())
            .zip(pad_to_kp_limbs.iter())
            .enumerate()
        {
            if i != 0 {
                let new_limb = this_limb
                    .add_constant(
                        cs.ns(|| format!("this_limb + pad_non_top_limb + *pad_to_kp_limb {}", i)),
                        &(pad_non_top_limb + pad_to_kp_limb),
                    )?
                    .sub(
                        cs.ns(|| {
                            format!(
                                "this_limb + pad_non_top_limb + pad_to_kp_limb - other_limb {}",
                                i
                            )
                        }),
                        other_limb,
                    )?;
                limbs.push(new_limb);
            } else {
                let new_limb = this_limb
                    .add_constant(
                        cs.ns(|| format!("this_limb + pad_top_limb + *pad_to_kp_limb {}", i)),
                        &(pad_top_limb + pad_to_kp_limb),
                    )?
                    .sub(
                        cs.ns(|| {
                            format!(
                                "this_limb + pad_top_limb + pad_to_kp_limb - other_limb {}",
                                i
                            )
                        }),
                        other_limb,
                    )?;
                limbs.push(new_limb);
            }
        }

        let result = NonNativeFieldGadget::<SimulationF, ConstraintF> {
            limbs,
            num_of_additions_over_normal_form: self.num_of_additions_over_normal_form
                + (other.num_of_additions_over_normal_form + ConstraintF::one())
                + (other.num_of_additions_over_normal_form + ConstraintF::one()),
            is_in_the_normal_form: false,
            simulation_phantom: PhantomData,
        };

        Ok(result)
    }

    /// Convert a `SimulationF` element into limbs (not constraints)
    /// This is an internal function that would be reused by a number of other functions
    pub fn get_limbs_representations(
        elem: &SimulationF,
    ) -> Result<Vec<ConstraintF>, SynthesisError> {
        Self::get_limbs_representations_from_big_integer(&elem.into_repr())
    }

    /// Obtain the limbs directly from a big int
    pub fn get_limbs_representations_from_big_integer_with_params(
        params: NonNativeFieldParams,
        elem: &<SimulationF as PrimeField>::BigInt,
    ) -> Result<Vec<ConstraintF>, SynthesisError> {
        // push the lower limbs first
        let mut limbs: Vec<ConstraintF> = Vec::new();
        let mut cur = *elem;
        for _ in 0..params.num_limbs {
            let cur_bits = cur.to_bits(); // `to_bits` is big endian
            let cur_mod_r = <ConstraintF as PrimeField>::BigInt::from_bits(
                &cur_bits[cur_bits.len() - params.bits_per_limb..],
            ); // therefore, the lowest `bits_per_non_top_limb` bits is what we want.
            limbs.push(ConstraintF::from_repr(cur_mod_r));
            cur.divn(params.bits_per_limb as u32);
        }

        // then we reserve, so that the limbs are ``big limb first''
        limbs.reverse();

        Ok(limbs)
    }

    /// Obtain the limbs directly from a big int
    pub fn get_limbs_representations_from_big_integer(
        elem: &<SimulationF as PrimeField>::BigInt,
    ) -> Result<Vec<ConstraintF>, SynthesisError> {
        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());
        Self::get_limbs_representations_from_big_integer_with_params(params, elem)
    }

    /// for advanced use, multiply and output the intermediate representations (without reduction)
    /// This intermediate representations can be added with each other, and they can later be
    /// reduced back to the `NonNativeFieldGadget`.
    pub fn mul_without_reduce<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<NonNativeFieldMulResultGadget<SimulationF, ConstraintF>, SynthesisError> {
        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());

        // Step 1: reduce `self` and `other` if necessary
        let mut self_reduced = self.clone();
        let mut other_reduced = other.clone();
        Reducer::<SimulationF, ConstraintF>::pre_mul_reduce(
            cs.ns(|| "pre mul reduce"),
            &mut self_reduced,
            &mut other_reduced,
        )?;

        let mut prod_limbs = Vec::new();
        if cfg!(feature = "density-optimized") {
            let zero = FpGadget::<ConstraintF>::zero(cs.ns(|| "zero"))?;

            for _ in 0..2 * params.num_limbs - 1 {
                prod_limbs.push(zero.clone());
            }

            for i in 0..params.num_limbs {
                for j in 0..params.num_limbs {
                    prod_limbs[i + j] = {
                        let mul = self_reduced.limbs[i].mul(
                            cs.ns(|| {
                                format!("self_reduced.limbs[{}] * other_reduced.limbs[{}]", i, j)
                            }),
                            &other_reduced.limbs[j],
                        )?;
                        prod_limbs[i + j]
                            .add(cs.ns(|| format!("prod_limbs[{},{}] + mul", i, j)), &mul)
                    }?;
                }
            }
        } else {
            for z_index in 0..2 * params.num_limbs - 1 {
                prod_limbs.push(FpGadget::<ConstraintF>::alloc(
                    cs.ns(|| format!("limb product {}", z_index)),
                    || {
                        let mut z_i = ConstraintF::zero();
                        for i in 0..=min(params.num_limbs - 1, z_index) {
                            let j = z_index - i;
                            if j < params.num_limbs {
                                z_i += &self_reduced.limbs[i]
                                    .get_value()
                                    .get()?
                                    .mul(&other_reduced.limbs[j].get_value().get()?);
                            }
                        }
                        Ok(z_i)
                    },
                )?);
            }

            for c in 0..(2 * params.num_limbs - 1) {
                let c_pows: Vec<_> = (0..(2 * params.num_limbs - 1))
                    .map(|i| ConstraintF::from((c + 1) as u128).pow(&vec![i as u64]))
                    .collect();

                let mut x = FpGadget::<ConstraintF>::zero(cs.ns(|| format!("alloc x {}", c)))?;
                for (i, (var, c_pow)) in self_reduced.limbs.iter().zip(c_pows.iter()).enumerate() {
                    let mul_result = var.mul_by_constant(
                        cs.ns(|| format!("self var * c_pow[{}]{}", i, c)),
                        &c_pow,
                    )?;
                    x.add_in_place(cs.ns(|| format!("x + mul result {},{}", c, i)), &mul_result)?;
                }

                let mut y = FpGadget::<ConstraintF>::zero(cs.ns(|| format!("alloc y {}", c)))?;
                for (i, (var, c_pow)) in other_reduced.limbs.iter().zip(c_pows.iter()).enumerate() {
                    let mul_result = var.mul_by_constant(
                        cs.ns(|| format!("other var * c_pow[{}]{}", i, c)),
                        &c_pow,
                    )?;
                    y.add_in_place(cs.ns(|| format!("y + mul result {},{}", c, i)), &mul_result)?;
                }

                let mut z = FpGadget::<ConstraintF>::zero(cs.ns(|| format!("alloc z {}", c)))?;
                for (i, (var, c_pow)) in prod_limbs.iter().zip(c_pows.iter()).enumerate() {
                    let mul_result = var.mul_by_constant(
                        cs.ns(|| format!("prod var * c_pow[{}]{}", i, c)),
                        &c_pow,
                    )?;
                    z.add_in_place(cs.ns(|| format!("z + mul result {},{}", c, i)), &mul_result)?;
                }

                x.mul_equals(cs.ns(|| format!("x * y = z {}", c)), &y, &z)?;
            }
        }

        Ok(NonNativeFieldMulResultGadget {
            limbs: prod_limbs,
            prod_of_num_of_additions: (self_reduced.num_of_additions_over_normal_form
                + ConstraintF::one())
                * (other_reduced.num_of_additions_over_normal_form + ConstraintF::one()),
            simulation_phantom: PhantomData,
        })
    }

    #[inline]
    pub fn is_odd<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<Boolean, SynthesisError> {
        let bits = self.to_bits_strict(cs.ns(|| "to bits strict"))?;
        Ok(bits[bits.len() - 1])
    }

    // Packs a big endian bit sequence (which does not exceed the length of a normal form)
    // into a NonNativeFieldGadget
    pub fn from_bits_with_params<CS: ConstraintSystem<ConstraintF>>(
        mut cs: CS,
        bits: &[Boolean],
        params: NonNativeFieldParams,
    ) -> Result<Self, SynthesisError> {
        let len_normal_form = params.num_limbs * params.bits_per_limb;
        assert!(bits.len() <= len_normal_form);

        // Pad big endian representation to length of normal form
        let mut per_nonnative_bits = vec![Boolean::Constant(false); len_normal_form - bits.len()];
        per_nonnative_bits.extend_from_slice(bits);

        // Pack each chunk of `bits_per_limb` many Booleans into a limb,
        // big endian ordered.
        let limbs = per_nonnative_bits
            .chunks_exact(params.bits_per_limb)
            .enumerate()
            .map(|(i, chunk)| {
                // from_bits() assumes big endian vector of bits
                let limb = FpGadget::<ConstraintF>::from_bits(
                    cs.ns(|| format!("packing bits to limb {}", i)),
                    &chunk.to_vec(),
                )?;

                Ok(limb)
            })
            .collect::<Result<Vec<FpGadget<ConstraintF>>, SynthesisError>>()?;

        Ok(NonNativeFieldGadget::<SimulationF, ConstraintF> {
            limbs,
            num_of_additions_over_normal_form: ConstraintF::zero(),
            is_in_the_normal_form: true,
            simulation_phantom: PhantomData,
        })
    }
}

impl<SimulationF: PrimeField, ConstraintF: PrimeField> FieldGadget<SimulationF, ConstraintF>
    for NonNativeFieldGadget<SimulationF, ConstraintF>
{
    type Variable = ();

    fn get_value(&self) -> Option<SimulationF> {
        let mut limbs = Vec::new();
        for limb in self.limbs.iter() {
            if let Some(limb) = limb.value {
                limbs.push(limb);
            } else {
                return None;
            }
        }

        Some(Self::limbs_to_value(limbs))
    }

    fn get_variable(&self) -> Self::Variable {
        unimplemented!()
    }

    fn zero<CS: ConstraintSystem<ConstraintF>>(cs: CS) -> Result<Self, SynthesisError> {
        Ok(Self::from_value(cs, &SimulationF::zero()))
    }

    fn one<CS: ConstraintSystem<ConstraintF>>(cs: CS) -> Result<Self, SynthesisError> {
        Ok(Self::from_value(cs, &SimulationF::one()))
    }

    fn conditionally_add_constant<CS: ConstraintSystem<ConstraintF>>(
        &self,
        _cs: CS,
        _cond: &Boolean,
        _other: SimulationF,
    ) -> Result<Self, SynthesisError> {
        unimplemented!();
    }

    /// Addition of non-natives without reduction
    fn add<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        let mut limbs = Vec::new();
        for (i, (this_limb, other_limb)) in self.limbs.iter().zip(other.limbs.iter()).enumerate() {
            let sum = this_limb.add(cs.ns(|| format!("add limbs {}", i)), other_limb)?;
            limbs.push(sum);
        }

        let mut res = Self {
            limbs,
            // the excess of the sum of two non-natives is the sum of their excesses, plus one.
            num_of_additions_over_normal_form: self
                .num_of_additions_over_normal_form
                .add(&other.num_of_additions_over_normal_form)
                .add(&ConstraintF::one()),
            is_in_the_normal_form: false,
            simulation_phantom: PhantomData,
        };

        Reducer::<SimulationF, ConstraintF>::post_add_reduce(
            cs.ns(|| "post add reduce"),
            &mut res,
        )?;

        Ok(res)
    }

    /// Substraction of non-natives without reduction
    fn sub<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        let mut result = self.sub_without_reduce(cs.ns(|| "sub without reduce"), other)?;
        Reducer::<SimulationF, ConstraintF>::post_add_reduce(
            cs.ns(|| "post sub reduce"),
            &mut result,
        )?;
        Ok(result)
    }

    fn negate<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<Self, SynthesisError> {
        Self::zero(cs.ns(|| "hardcode zero"))?.sub(cs.ns(|| "0 - self"), self)
    }

    fn mul<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        let res = self.mul_without_reduce(cs.ns(|| "mul"), &other)?;
        let res_reduced = res.reduce(cs.ns(|| "reduce result"))?;
        Ok(res_reduced)
    }

    fn add_constant<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &SimulationF,
    ) -> Result<Self, SynthesisError> {
        let other_g = Self::from_value(cs.ns(|| "hardcode add constant"), other);
        self.add(cs.ns(|| "add constant"), &other_g)
    }

    fn sub_constant<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        fe: &SimulationF,
    ) -> Result<Self, SynthesisError> {
        let other_g = Self::from_value(cs.ns(|| "hardcode sub constant"), fe);
        self.sub(cs.ns(|| "subtract constant"), &other_g)
    }

    // TODO: Can be optimized by implementing a mul_by_constant_without_reduce()
    fn mul_by_constant<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        fe: &SimulationF,
    ) -> Result<Self, SynthesisError> {
        let other_g = Self::from_value(cs.ns(|| "hardcode mul constant"), fe);
        self.mul(cs.ns(|| "mul constant"), &other_g)
    }

    fn inverse<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<Self, SynthesisError> {
        let inverse = Self::alloc(cs.ns(|| "inverse"), || {
            Ok(self
                .get_value()
                .get()?
                .inverse()
                .unwrap_or_else(SimulationF::zero))
        })?;
        let one = Self::one(cs.ns(|| "alloc one"))?;

        let actual_result = self.clone().mul(cs.ns(|| "self * inverse"), &inverse)?;
        actual_result.enforce_equal(cs.ns(|| "self * inverse == 1"), &one)?;
        Ok(inverse)
    }

    // The non-native field is a prime field, hence the Frobenious map is trivial
    fn frobenius_map<CS: ConstraintSystem<ConstraintF>>(
        &self,
        _: CS,
        _power: usize,
    ) -> Result<Self, SynthesisError> {
        Ok(self.clone())
    }

    fn cost_of_mul() -> usize {
        unimplemented!()
    }

    fn cost_of_mul_equals() -> usize {
        unimplemented!()
    }

    fn cost_of_inv() -> usize {
        unimplemented!()
    }
}

impl<SimulationF: PrimeField, ConstraintF: PrimeField> ConstantGadget<SimulationF, ConstraintF>
    for NonNativeFieldGadget<SimulationF, ConstraintF>
{
    fn from_value<CS: ConstraintSystem<ConstraintF>>(mut cs: CS, value: &SimulationF) -> Self {
        let limbs_value = Self::get_limbs_representations(value).unwrap();

        let mut limbs = Vec::new();

        for (i, limb_value) in limbs_value.iter().enumerate() {
            limbs.push(FpGadget::<ConstraintF>::from_value(
                cs.ns(|| format!("limb {}", i)),
                limb_value,
            ));
        }

        Self {
            limbs,
            num_of_additions_over_normal_form: ConstraintF::zero(),
            is_in_the_normal_form: true,
            simulation_phantom: PhantomData,
        }
    }

    fn get_constant(&self) -> SimulationF {
        self.get_value().unwrap()
    }
}

impl<SimulationF: PrimeField, ConstraintF: PrimeField> ToBitsGadget<ConstraintF>
    for NonNativeFieldGadget<SimulationF, ConstraintF>
{
    fn to_bits<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());

        // Reduce to the normal form
        // Though, a malicious prover can make it slightly larger than p
        let mut self_normal = self.clone();
        Reducer::<SimulationF, ConstraintF>::pre_eq_reduce(
            cs.ns(|| "pre eq reduce"),
            &mut self_normal,
        )?;

        // Therefore, we convert it to bits and enforce that it is in the field
        let mut bits = Vec::<Boolean>::new();

        // Separate treatment of the first limb, as we want to return
        // exactly SimulationF::size_in_bits() bits
        bits.extend_from_slice(&Reducer::<SimulationF, ConstraintF>::limb_to_bits(
            cs.ns(|| "limb 0 to bits"),
            &self_normal.limbs[0],
            SimulationF::size_in_bits() % params.bits_per_limb,
        )?);

        for (i, limb) in self_normal.limbs.iter().skip(1).enumerate() {
            bits.extend_from_slice(&Reducer::<SimulationF, ConstraintF>::limb_to_bits(
                cs.ns(|| format!("limb {} to bits", i + 1)),
                &limb,
                params.bits_per_limb,
            )?);
        }

        Ok(bits)
    }

    fn to_bits_strict<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        let bits = self.to_bits(cs.ns(|| "to bits"))?;
        Boolean::enforce_in_field::<_, _, SimulationF>(&mut cs, bits.as_slice())?;

        Ok(bits)
    }
}

impl<SimulationF: PrimeField, ConstraintF: PrimeField> FromBitsGadget<ConstraintF>
    for NonNativeFieldGadget<SimulationF, ConstraintF>
{
    // Packs a bit sequence (which does not exceed the length of a normal form) into a NonNativeFieldGadget
    fn from_bits<CS: ConstraintSystem<ConstraintF>>(
        cs: CS,
        bits: &[Boolean],
    ) -> Result<Self, SynthesisError> {
        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());
        Self::from_bits_with_params(cs, bits, params)
    }
}

impl<SimulationF: PrimeField, ConstraintF: PrimeField> ToBytesGadget<ConstraintF>
    for NonNativeFieldGadget<SimulationF, ConstraintF>
{
    fn to_bytes<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        let mut bits = self.to_bits(cs.ns(|| "self to bits"))?;
        bits.reverse();

        let mut bytes = Vec::<UInt8>::new();
        bits.chunks(8).for_each(|bits_per_byte| {
            let mut bits_per_byte: Vec<Boolean> = bits_per_byte.to_vec();
            if bits_per_byte.len() < 8 {
                bits_per_byte.resize_with(8, || Boolean::constant(false));
            }

            bytes.push(UInt8::from_bits_le(&bits_per_byte));
        });

        Ok(bytes)
    }

    fn to_bytes_strict<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        let mut bits = self.to_bits_strict(cs.ns(|| "self to bits strict"))?;
        bits.reverse();

        let mut bytes = Vec::<UInt8>::new();
        bits.chunks(8).for_each(|bits_per_byte| {
            let mut bits_per_byte: Vec<Boolean> = bits_per_byte.to_vec();
            if bits_per_byte.len() < 8 {
                bits_per_byte.resize_with(8, || Boolean::constant(false));
            }

            bytes.push(UInt8::from_bits_le(&bits_per_byte));
        });

        Ok(bytes)
    }
}

impl<SimulationF: PrimeField, ConstraintF: PrimeField> CondSelectGadget<ConstraintF>
    for NonNativeFieldGadget<SimulationF, ConstraintF>
{
    fn conditionally_select<CS: ConstraintSystem<ConstraintF>>(
        mut cs: CS,
        cond: &Boolean,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        let mut limbs_sel = Vec::with_capacity(true_value.limbs.len());

        for (i, (x, y)) in true_value.limbs.iter().zip(&false_value.limbs).enumerate() {
            limbs_sel.push(FpGadget::<ConstraintF>::conditionally_select(
                cs.ns(|| format!("select limb {}", i)),
                cond,
                x,
                y,
            )?);
        }

        Ok(Self {
            limbs: limbs_sel,
            num_of_additions_over_normal_form: max(
                true_value.num_of_additions_over_normal_form,
                false_value.num_of_additions_over_normal_form,
            ),
            is_in_the_normal_form: true_value.is_in_the_normal_form
                && false_value.is_in_the_normal_form,
            simulation_phantom: PhantomData,
        })
    }

    fn cost() -> usize {
        let num_limbs =
            get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits()).num_limbs;
        num_limbs * <FpGadget<ConstraintF> as CondSelectGadget<ConstraintF>>::cost()
    }
}

impl<SimulationF: PrimeField, ConstraintF: PrimeField> TwoBitLookupGadget<ConstraintF>
    for NonNativeFieldGadget<SimulationF, ConstraintF>
{
    type TableConstant = SimulationF;

    fn two_bit_lookup<CS: ConstraintSystem<ConstraintF>>(
        mut cs: CS,
        bits: &[Boolean],
        constants: &[Self::TableConstant],
    ) -> Result<Self, SynthesisError> {
        debug_assert!(bits.len() == 2);
        debug_assert!(constants.len() == 4);

        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());
        let mut limbs_constants = Vec::new();
        for _ in 0..params.num_limbs {
            limbs_constants.push(Vec::new());
        }

        for constant in constants.iter() {
            let representations =
                NonNativeFieldGadget::<SimulationF, ConstraintF>::get_limbs_representations(
                    constant,
                )?;

            for (i, representation) in representations.iter().enumerate() {
                limbs_constants[i].push(*representation);
            }
        }

        let mut limbs = Vec::new();
        for (i, limbs_constant) in limbs_constants.iter().enumerate() {
            limbs.push(FpGadget::<ConstraintF>::two_bit_lookup(
                cs.ns(|| format!("two bit lookup limb {}", i)),
                bits,
                limbs_constant,
            )?);
        }

        Ok(NonNativeFieldGadget::<SimulationF, ConstraintF> {
            limbs,
            num_of_additions_over_normal_form: ConstraintF::zero(),
            is_in_the_normal_form: true,
            simulation_phantom: PhantomData,
        })
    }

    fn two_bit_lookup_lc<CS: ConstraintSystem<ConstraintF>>(
        mut cs: CS,
        precomp: &Boolean,
        bits: &[Boolean],
        constants: &[Self::TableConstant],
    ) -> Result<Self, SynthesisError> {
        debug_assert!(bits.len() == 2);
        debug_assert!(constants.len() == 4);

        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());
        let mut limbs_constants = Vec::new();
        for _ in 0..params.num_limbs {
            limbs_constants.push(Vec::new());
        }

        for constant in constants.iter() {
            let representations =
                NonNativeFieldGadget::<SimulationF, ConstraintF>::get_limbs_representations(
                    constant,
                )?;

            for (i, representation) in representations.iter().enumerate() {
                limbs_constants[i].push(*representation);
            }
        }

        let mut limbs = Vec::new();
        for (i, limbs_constant) in limbs_constants.iter().enumerate() {
            limbs.push(FpGadget::<ConstraintF>::two_bit_lookup_lc(
                cs.ns(|| format!("two bit lookup lc limb {}", i)),
                precomp,
                bits,
                limbs_constant,
            )?);
        }

        Ok(NonNativeFieldGadget::<SimulationF, ConstraintF> {
            limbs,
            num_of_additions_over_normal_form: ConstraintF::zero(),
            is_in_the_normal_form: true,
            simulation_phantom: PhantomData,
        })
    }

    fn cost() -> usize {
        let num_limbs =
            get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits()).num_limbs;
        num_limbs * <FpGadget<ConstraintF> as TwoBitLookupGadget<ConstraintF>>::cost()
    }
}

impl<SimulationF: PrimeField, ConstraintF: PrimeField> ThreeBitCondNegLookupGadget<ConstraintF>
    for NonNativeFieldGadget<SimulationF, ConstraintF>
{
    type TableConstant = SimulationF;

    fn three_bit_cond_neg_lookup<CS: ConstraintSystem<ConstraintF>>(
        mut cs: CS,
        bits: &[Boolean],
        b0b1: &Boolean,
        constants: &[Self::TableConstant],
    ) -> Result<Self, SynthesisError> {
        debug_assert!(bits.len() == 3);
        debug_assert!(constants.len() == 4);

        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());

        let mut limbs_constants = Vec::new();
        for _ in 0..params.num_limbs {
            limbs_constants.push(Vec::new());
        }

        for constant in constants.iter() {
            let representations =
                NonNativeFieldGadget::<SimulationF, ConstraintF>::get_limbs_representations(
                    constant,
                )?;

            for (i, representation) in representations.iter().enumerate() {
                limbs_constants[i].push(*representation);
            }
        }

        let mut limbs = Vec::new();
        for (i, limbs_constant) in limbs_constants.iter().enumerate() {
            limbs.push(FpGadget::<ConstraintF>::three_bit_cond_neg_lookup(
                cs.ns(|| format!("three_bit_cond_neg_lookup limb {}", i)),
                bits,
                b0b1,
                limbs_constant,
            )?);
        }

        Ok(NonNativeFieldGadget::<SimulationF, ConstraintF> {
            limbs,
            num_of_additions_over_normal_form: ConstraintF::zero(),
            is_in_the_normal_form: true,
            simulation_phantom: PhantomData,
        })
    }

    fn cost() -> usize {
        let num_limbs =
            get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits()).num_limbs;
        num_limbs * <FpGadget<ConstraintF> as ThreeBitCondNegLookupGadget<ConstraintF>>::cost()
    }
}

impl<SimulationF: PrimeField, ConstraintF: PrimeField> AllocGadget<SimulationF, ConstraintF>
    for NonNativeFieldGadget<SimulationF, ConstraintF>
{
    /// Allocates a non-native field element and enforces normal form, which consumes at most `bits_per_limb` many bits per limb, and
    /// and altogether at most (non-native) modulus many bits.
    // TODO:  Check why `num_of_additions_over_normal_form` is set to `1` and `is_over_normal_form` is set `false`.
    fn alloc<F, T, CS: ConstraintSystem<ConstraintF>>(
        mut cs: CS,
        f: F,
    ) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<SimulationF>,
    {
        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());
        let zero = SimulationF::zero();

        let elem = match f() {
            Ok(t) => *(t.borrow()),
            Err(_) => zero,
        };
        let elem_representations = Self::get_limbs_representations(&elem)?;
        let mut limbs = Vec::new();

        for (i, limb) in elem_representations.iter().enumerate() {
            limbs.push(FpGadget::<ConstraintF>::alloc(
                cs.ns(|| format!("alloc limb {}", i)),
                || Ok(limb),
            )?);
        }

        let num_of_additions_over_normal_form = ConstraintF::one();

        // We constrain all limbs to use at most `bits_per_limb` many bits
        for (i, limb) in limbs.iter().rev().take(params.num_limbs - 1).enumerate() {
            Reducer::<SimulationF, ConstraintF>::limb_to_bits(
                cs.ns(|| format!("limb {} to bits", i)),
                limb,
                params.bits_per_limb,
            )?;
        }
        // The most significant limb is treated differently, to enforce that
        // over all at most modulus many bits are used.
        Reducer::<SimulationF, ConstraintF>::limb_to_bits(
            cs.ns(|| "initial limb to bits"),
            &limbs[0],
            SimulationF::size_in_bits() - (params.num_limbs - 1) * params.bits_per_limb,
        )?;

        Ok(Self {
            limbs,
            num_of_additions_over_normal_form,
            is_in_the_normal_form: false,
            simulation_phantom: PhantomData,
        })
    }

    fn alloc_input<F, T, CS: ConstraintSystem<ConstraintF>>(
        mut cs: CS,
        f: F,
    ) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<SimulationF>,
    {
        let zero = SimulationF::zero();

        let elem = match f() {
            Ok(t) => *(t.borrow()),
            Err(_) => zero,
        };
        let elem_representations = Self::get_limbs_representations(&elem)?;
        let mut limbs = Vec::new();

        for (i, limb) in elem_representations.iter().enumerate() {
            limbs.push(FpGadget::<ConstraintF>::alloc_input(
                cs.ns(|| format!("alloc input limb {}", i)),
                || Ok(limb),
            )?);
        }

        let num_of_additions_over_normal_form = ConstraintF::zero();

        Ok(Self {
            limbs,
            num_of_additions_over_normal_form,
            is_in_the_normal_form: true,
            simulation_phantom: PhantomData,
        })
    }
}

impl<SimulationF: PrimeField, ConstraintF: PrimeField> ToConstraintFieldGadget<ConstraintF>
    for NonNativeFieldGadget<SimulationF, ConstraintF>
{
    type FieldGadget = FpGadget<ConstraintF>;

    fn to_field_gadget_elements<CS: ConstraintSystem<ConstraintF>>(
        &self,
        _cs: CS,
    ) -> Result<Vec<Self::FieldGadget>, SynthesisError> {
        Ok(self.limbs.to_vec())
    }
}

impl<SimulationF: PrimeField, ConstraintF: PrimeField> EqGadget<ConstraintF>
    for NonNativeFieldGadget<SimulationF, ConstraintF>
{
    // Naive implementation
    fn is_eq<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Boolean, SynthesisError> {
        // Let the prover choose the value of this boolean variable
        let should_enforce_equal = Boolean::alloc(cs.ns(|| "alloc result"), || {
            Ok(self.get_value().get()? == other.get_value().get()?)
        })?;

        // Enforce the prover chose the correct value
        self.conditional_enforce_equal(
            cs.ns(|| " conditional self == other"),
            other,
            &should_enforce_equal,
        )?;
        self.conditional_enforce_not_equal(
            cs.ns(|| "conditional self != other"),
            other,
            &should_enforce_equal.not(),
        )?;

        Ok(should_enforce_equal)
    }

    fn conditional_enforce_equal<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
        should_enforce: &Boolean,
    ) -> Result<(), SynthesisError> {
        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());

        // Get p
        let p_representations =
            NonNativeFieldGadget::<SimulationF, ConstraintF>::get_limbs_representations_from_big_integer(
                &<SimulationF as PrimeField>::Params::MODULUS,
            )?;
        // TODO: check if the recomputation of MODULUS is the best way we can do.
        let p_bigint = limbs_to_bigint(params.bits_per_limb, &p_representations);

        let mut p_gadget_limbs = Vec::new();
        for (i, limb) in p_representations.iter().enumerate() {
            p_gadget_limbs.push(FpGadget::<ConstraintF>::from_value(
                cs.ns(|| format!("hardcode limb {}", i)),
                limb,
            ));
        }
        let p_gadget = NonNativeFieldGadget::<SimulationF, ConstraintF> {
            limbs: p_gadget_limbs,
            num_of_additions_over_normal_form: ConstraintF::one(),
            // TODO: p_gadget as defined by the limbs has normal form.
            // Find out if there is a particular reason why `is_normal_form` is set `false`.
            is_in_the_normal_form: false,
            simulation_phantom: PhantomData,
        };

        // Get delta = self - other
        let zero = Self::zero(cs.ns(|| "hardcode zero"))?;
        let mut delta = self.sub_without_reduce(cs.ns(|| "delta = self - other"), other)?;
        delta = Self::conditionally_select(
            cs.ns(|| "select delta or zero"),
            should_enforce,
            &delta,
            &zero,
        )?;

        // Allocate k = delta / p
        let k_gadget = FpGadget::<ConstraintF>::alloc(cs.ns(|| "alloc k"), || {
            let mut delta_limbs_values = Vec::<ConstraintF>::new();
            for limb in delta.limbs.iter() {
                delta_limbs_values.push(limb.get_value().get()?);
            }

            let delta_bigint = limbs_to_bigint(params.bits_per_limb, &delta_limbs_values);

            Ok(bigint_to_constraint_field::<ConstraintF>(
                &(delta_bigint / p_bigint),
            ))
        })?;

        let surfeit = overhead!(delta.num_of_additions_over_normal_form + ConstraintF::one()) + 1;
        Reducer::<SimulationF, ConstraintF>::limb_to_bits(
            cs.ns(|| "k limb to bits"),
            &k_gadget,
            surfeit,
        )?;

        // Compute k * p
        let mut kp_gadget_limbs = Vec::new();
        for (i, limb) in p_gadget.limbs.iter().enumerate() {
            let mul = limb.mul(cs.ns(|| format!("limb_{} * k_gadget", i)), &k_gadget)?;
            kp_gadget_limbs.push(mul);
        }

        // Enforce delta = kp
        Reducer::<SimulationF, ConstraintF>::group_and_check_equality(
            cs.ns(|| "group and check equality"),
            surfeit,
            params.bits_per_limb,
            params.bits_per_limb,
            &delta.limbs,
            &kp_gadget_limbs,
        )?;

        Ok(())
    }

    fn conditional_enforce_not_equal<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
        should_enforce: &Boolean,
    ) -> Result<(), SynthesisError> {
        let one = Self::one(cs.ns(|| "hardcode one"))?;
        let sub = self.sub(cs.ns(|| "self - other"), &other)?;
        let _ = Self::conditionally_select(
            cs.ns(|| "SELECT self - other OR one"),
            should_enforce,
            &sub,
            &one,
        )?
        .inverse(cs.ns(|| "invert cond select result"))?;

        Ok(())
    }
}

/*
 * Implementation of a few traits
 */

impl<SimulationF: PrimeField, ConstraintF: PrimeField> Clone
    for NonNativeFieldGadget<SimulationF, ConstraintF>
{
    fn clone(&self) -> Self {
        NonNativeFieldGadget {
            limbs: self.limbs.clone(),
            num_of_additions_over_normal_form: self.num_of_additions_over_normal_form,
            is_in_the_normal_form: self.is_in_the_normal_form,
            simulation_phantom: PhantomData,
        }
    }
}
