//! Definition of NonNativeFieldGadget and implementation of
//!     - certain low-level arithmetic operations (without reduction),
//!     - the FieldGadget trait,
//! as well as the following auxiliary traits:
//!     - ToBitsGadget, FromBitsGadget, ConstantGadget, ToBytesGadget,
//!     - CondSelectGadget, TwoBitLookup, ThreeBitCondNegLookupGadget,
//!     - AllocGadget, ToConstraintFieldGadget, CloneGadget
//! and the
//!     - EqGadget, which heaviliy uses reduction from reduce.rs
use algebra::{BigInteger, FpParameters, PrimeField};
use num_bigint::BigUint;
use num_traits::{One, Zero};

use crate::fields::nonnative::NonNativeFieldParams;
use crate::{fields::fp::FpGadget, fields::nonnative::{
    nonnative_field_mul_result_gadget::NonNativeFieldMulResultGadget,
    params::get_params,
    reduce::Reducer,
}, fields::FieldGadget, ceil_log_2, prelude::*, to_field_gadget_vec::ToConstraintFieldGadget, Assignment, FromGadget};
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use std::cmp::max;
use std::marker::PhantomData;
use std::{borrow::Borrow, vec, vec::Vec};
use std::convert::TryInto;

#[derive(Debug, Eq, PartialEq)]
#[must_use]
pub struct NonNativeFieldGadget<SimulationF: PrimeField, ConstraintF: PrimeField> {
    /// The limbs as elements of ConstraintF, big endian ordered.
    /// Recall that in the course of arithmetic operations bits the bit length of
    /// a limb exceeds the limb length of normal form, which is
    /// ``
    ///     bits_per_limb[i] = NonNativeFieldParams::bits_per_limb
    /// `` 
    /// for all limbs except the most significant one, i.e. i>=1, and
    /// ``
    ///     bits_per_limb[0] = SimulationF::size_in_bits()
    ///     - (NonNativeFieldParams::numlimbs - 1) * NonNativeFieldParams::bits_per_limb.
    /// ``
    /// Reduction transforms back to normal form, which again has at as many bits as
    /// normal form (but is not necessarily the mod p remainder).
    pub limbs: Vec<FpGadget<ConstraintF>>,
    /// A measure for the limb size in the course of arithmetic operations, which is 
    /// used to decide when reduction is needed. 
    /// `num_of_additions_over_normal_form` keeps track of a witness independent 
    /// limb bound
    /// ``
    ///    limb[i] <= (num_of_additions_over_normal_form + 1) * 2^bits_per_limb[i].
    /// `` 
    /// In particular 
    /// ``
    ///     len(limb[i]) <= surfeit + len_normal_form[i].
    /// ``
    /// where 
    /// ``
    ///     surfeit = len(num_of_additions_over_normal_form + 1).
    /// ``
    /// 
    // Note: an alternative choice would be <ConstraintF as PrimeField>BigInt
    // but this would make computations on it more difficult, as they might 
    // exceed the max value of BigInt.
    pub num_of_additions_over_normal_form: BigUint,
    /// Whether the limb representation is the normal form, i.e. has the same
    /// number of bits as the non-native modulus.
    #[doc(hidden)]
    pub simulation_phantom: PhantomData<SimulationF>,
}



/// Converts an unsigned big integer `bigint` into an element from the constraint field F_p by
/// computing (bigint mod p).
pub fn bigint_to_constraint_field<ConstraintF: PrimeField>(bigint: &BigUint) -> ConstraintF {
    let mut val = ConstraintF::zero();
    let mut cur = ConstraintF::one();
    let bytes = bigint.to_bytes_be();

    let basefield_256 = ConstraintF::from_repr(<ConstraintF as PrimeField>::BigInt::from(256));

    for byte in bytes.iter().rev() {
        let bytes_basefield = ConstraintF::from(*byte as u128);
        val += cur * bytes_basefield;

        cur *= &basefield_256;
    }

    val
}

/// Recombines the large integer value from a vector of (not necessarily normalized) limbs.
pub fn limbs_to_bigint<ConstraintF: PrimeField>(
    bits_per_limb: usize,
    limbs: &[ConstraintF],
) -> BigUint {
    let mut val = BigUint::zero();
    let mut big_cur = BigUint::one();
    let two = BigUint::from(2u32);
    for limb in limbs.iter().rev() {
        let mut limb_repr = limb.into_repr().to_bits();
        limb_repr.reverse(); //We need them in little endian
        let mut small_cur = big_cur.clone();
        for limb_bit in limb_repr.iter() {
            if *limb_bit {
                val += &small_cur;
            }
            small_cur *= 2u32;
        }
        big_cur *= two.pow(bits_per_limb as u32);
    }

    val
}

/*******************************************************************************
 * 
 *  Low-level functions that do not make use of normalization
 * 
 * *****************************************************************************/
impl<SimulationF: PrimeField, ConstraintF: PrimeField>
    NonNativeFieldGadget<SimulationF, ConstraintF>
{
    /// A function for test purposes. Returns `true` if `&self.num_add` respects 
    /// the capacity bound, and bounds all the limbs correctly.
    pub(crate) fn check(&self) -> bool {
        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());

        let valid_num_limbs = self.limbs.len() == params.num_limbs;

        let normal_form_bound = BigUint::from(2usize).pow(params.bits_per_limb as u32);
        let normal_form_bound_ms = BigUint::from(2usize).pow(
            (SimulationF::size_in_bits() - (params.num_limbs - 1) * params.bits_per_limb) as u32
        );
        let num_add_plus_one = self.num_of_additions_over_normal_form.clone() + BigUint::one();
        let limb_bound = normal_form_bound * &num_add_plus_one;
        let limb_bound_ms = normal_form_bound_ms * &num_add_plus_one;

        let valid_num_adds = params.bits_per_limb + ceil_log_2!(num_add_plus_one)
             < ConstraintF::size_in_bits() - 1;

        // k-ary and of the limb checks.
        let valid_limbs = self.limbs.iter().enumerate().all(|(i,limb)|{
            if let Some(val_limb) = limb.get_value() {
                let val_limb: BigUint = val_limb.into();

                if i == 0 {
                    val_limb < limb_bound_ms
                } else {
                    val_limb < limb_bound
                } 
            } else {
                true
            }
        });

        valid_num_limbs && valid_num_adds && valid_limbs
    }

    /// A function for test puroposes. Allocates a random non-native with oversized 
    /// limbs, having a surfeit s.t. 
    /// `surfeit + bits_per_limbs <= ConstraintF::size_in_bits() - 1`.
    #[cfg(test)]
    pub(crate) fn alloc_random<R, CS>(mut cs: CS, rng: &mut R, surfeit: usize) 
    -> Result<Self, SynthesisError>
    where 
        R: rand::RngCore,
        CS: ConstraintSystemAbstract<ConstraintF>,
    {
        use rand::Rng;
        
        // We sample random limbs of `limb_size[i] = surfeit + bits_per_limbs[i]`. As
        // ``
        //      limb[i] < 2^{surfeit + bits_per_limb[i]} = 2^surfeit * 2^bits_per_limb[i],
        // ``
        // we may choose `num_adds +  1 = 2^surfeit`.
        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());
        
        assert!(params.bits_per_limb + surfeit <= ConstraintF::size_in_bits()-1);

        // compute 2^surfeit as bigint
        let num_add_plus_one = BigUint::one() << surfeit;

        let mut limbs = Vec::new();

        for i in 0..params.num_limbs {
            // compute target limb size 
            let num_bits:usize = if i == 0 {
                // most significant limb 
                surfeit + SimulationF::size_in_bits() - (params.num_limbs - 1) * params.bits_per_limb
            } else {
                // the other limbs
                surfeit + params.bits_per_limb
            };

            let bits = (0..num_bits).map(|_|
                rng.gen()
            )
            .collect::<Vec<bool>>(); 
            
            let limb_val = ConstraintF::read_bits(bits).unwrap();
            let limb = FpGadget::<ConstraintF>::alloc(
                cs.ns(|| format!("alloc limb {}", i)),
                || Ok(limb_val),
            )?;
            limbs.push(limb);
        };

        Ok(Self{
            limbs: limbs,
            num_of_additions_over_normal_form: num_add_plus_one - BigUint::one(),
            simulation_phantom: PhantomData
        })
    }

    /* 
        conversion functions on vectors of limbs
    */
    
    /// Obtain the non-native value from a vector of not necessarily normalized
    /// limb elements.
    // TODO: Can we use the functions limbs_to_bigint and bigint_to_constraint_field? 
    // Logic seems duplicated
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
    /// Convert a `SimulationF` element into limbs having normal form.
    /// This is an internal function that would be reused by a number of other functions
    pub(crate) fn get_limbs_representations(
        elem: &SimulationF,
    ) -> Result<Vec<ConstraintF>, SynthesisError> {
        Self::get_limbs_representations_from_big_integer(&elem.into_repr())
    }

    /// Obtain the limbs directly from a big int
    pub(crate) fn get_limbs_representations_from_big_integer_with_params(
        params: NonNativeFieldParams,
        elem: &SimulationF::BigInt,
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
    pub(crate) fn get_limbs_representations_from_big_integer(
        elem: &SimulationF::BigInt,
    ) -> Result<Vec<ConstraintF>, SynthesisError> {
        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());
        Self::get_limbs_representations_from_big_integer_with_params(params, elem)
    }

    // Packs a big endian slice of Boolean gadgets (which does not exceed the length 
    // of a normal form) into a NonNativeFieldGadget
    pub fn from_bits_with_params<CS: ConstraintSystemAbstract<ConstraintF>>(
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
            num_of_additions_over_normal_form: BigUint::zero(),
            simulation_phantom: PhantomData,
        })
    }

    pub fn to_bits_for_normal_form<CS: ConstraintSystemAbstract<ConstraintF>>(&self, mut cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());
        let mut bits = Vec::with_capacity(SimulationF::size_in_bits());
        for (i, limb) in self.limbs.iter().enumerate() {
            let bits_per_limb = if i == 0 {
                SimulationF::size_in_bits() - (params.num_limbs-1)*params.bits_per_limb
            } else {
                params.bits_per_limb
            };
            let limb_bits = Reducer::<SimulationF, ConstraintF>::limb_to_bits(cs.ns(|| format!("limb {} to bits", i)), limb, bits_per_limb)?;
            bits.extend_from_slice(limb_bits.as_slice());
        }

        Ok(bits)
    }

    /// checks if a NonNativeFieldGadget is odd, i.e. that its mod `p` reduced 
    /// representation has the least significant bit set to `1`. 
    #[inline]
    pub fn is_odd<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<Boolean, SynthesisError> {
        let bits = self.to_bits_strict(cs.ns(|| "to bits strict"))?;
        Ok(bits[bits.len() - 1])
    }


    /* 
        arithemtic functions without pre-reduction steps
    */

    /// Low level function for addition of non-natives. In order to guarantee
    /// a reducible output, this function assumes that  
    /// ``
    ///     bits_per_limb + log(num_add(L) + num_add(R) + 4) <= CAPACITY - 3,
    /// `` 
    /// and panics if not.
    pub(crate) fn add_without_prereduce<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        debug_assert!(
            self.check() && other.check(),
            "add_without_prereduce(): check() failed on input gadgets" 
        );

        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());
        let surfeit = ceil_log_2!(BigUint::from(4usize) + &self.num_of_additions_over_normal_form + &other.num_of_additions_over_normal_form);
        
        if params.bits_per_limb + surfeit > ConstraintF::Params::CAPACITY as usize - 3 {
            return Err(SynthesisError::Other(
                format!("Security bound exceeded for add_without_prereduce. Max: {}, Actual: {}", 
                ConstraintF::Params::CAPACITY as usize - 3, 
                params.bits_per_limb + surfeit))
            );
        }

        let mut limbs = Vec::new();
        for (i, (this_limb, other_limb)) in self.limbs.iter().zip(other.limbs.iter()).enumerate() {
            let sum = this_limb.add(cs.ns(|| format!("add limbs {}", i)), other_limb)?;
            limbs.push(sum);
        }

        let result = Self {
            limbs,
            // Since 
            // ``
            //    T[i] = L[i] + R[i] < (num_add(L) + 1) * 2^bits_per_limb
            //                  + (num_add(R) + 1) * 2^bits_per_limb
            // ``
            // we set `num_add(T) = num_add(L) + num_add(R) + 1`.
            num_of_additions_over_normal_form: BigUint::one()
                + &self.num_of_additions_over_normal_form
                + &other.num_of_additions_over_normal_form,
            simulation_phantom: PhantomData,
        };

        debug_assert!(
            result.check(),
            "add_without_prereduce(): result failed on check()"
        );

        Ok(result)
    }

    /// Low-level function for subtract a nonnative field element `other` from `self` modulo `p`. 
    /// Outputs non-normal form which allows a secure reduction.
    /// Assumes that 
    /// ``
    ///     bits_per_limb + log(num_add(L) + num_add(R) + 5) <= CAPACITY - 3,
    /// `` 
    /// to assure a secure and reducible sub result.
    // Costs no constraints.
    // Note on the security assumption:  To output a difference which does not exceed the 
    // capacity bound, we need to demand that
    // ``
    //     bits_per_limb + log(num_add(D) + 1) <= CAPACITY,
    // `` 
    // where `num_add(D) = num_add(L) + num_add(R) + 2`, see below. To allow a subsequent reduction 
    // we need to assure the stricter condition
    // ``
    //     bits_per_limb + log(num_add(D) + 3) <= CAPACITY - 3.
    // `` 
    pub(crate) fn sub_without_prereduce<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        debug_assert!(
            self.check() && other.check(),
            "sub_without_prereduce(): check() failed on input gadgets" 
        );

        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());
        let surfeit = ceil_log_2!(BigUint::from(5usize) + &self.num_of_additions_over_normal_form + &other.num_of_additions_over_normal_form);
        
        if params.bits_per_limb + surfeit > ConstraintF::Params::CAPACITY as usize - 3 {
            return Err(
                SynthesisError::Other(
                    format!("Security bound exceeded for sub_without_prereduce. Max: {}, Actual: {}", 
                    ConstraintF::Params::CAPACITY as usize - 3, params.bits_per_limb + surfeit)
                )
            );
        }

        // To prove that a limb representation [D[0],D[1],...] corresponds to the difference of 
        // the two non-natives
        // 
        //   Sum_{i=0..} L[i] * A^i - Sum_{i=0..} R[i] * A^i, 
        //
        // with `A = 2^bits_per_limb`, we apply shift_constants `[shift_constant[0], shift_constant[1],..]
        // to avoid underflows in the limb-wise differences, making the `shift_constant[i] - R[i]` 
        // positive in a length-preserving manner. To correct the change in value modulo p, 
        // we add to 
        // ``
        //      shift = Sum_{i=0..} shift_constant[i] * A^i
        // ``
        // the difference
        // ``
        //      delta = Sum_{i=0..} delta[i] * A^i,
        // ``
        // to the next multiple of p, i.e. `delta = - shift mod p`. Overall we enforce
        // ``
        //   (L[i] + delta[i]) + (shift_constant[i] - R[i])  == D[i].
        // ``
        // In order that this sum does not exceed the CAPACITY, 
        // ``
        //  D[i] < (num_add(L) + 2) * 2^bits_per_limb[i] + 
        //              (num_add(R) + 1) * 2^bits_per_limb[i] <= 2^CAPACITY,
        // ``
        // which holds if 
        // ``
        //      bits_per_limb + log(num_add(L) + num_add(R) + 3) <= CAPACITY.
        // ``

        // For all limbs we choose 
        // ``
        //   shift_constant[i] = (num_add(R) + 1) * 2^bits_per_limb[i] - 1
        // ``
        // With this choice 
        // ``
        //      0 <= shift_constant[i] - R[i] < (num_add(R) + 1) * 2^bits_per_limb[i].
        // ``
        let mut pad_non_top_limb_repr =  BigUint::one();
        let mut pad_top_limb_repr = pad_non_top_limb_repr.clone();

        pad_non_top_limb_repr <<= params.bits_per_limb;
        let pad_non_top_limb: ConstraintF = (
            (BigUint::one() + &other.num_of_additions_over_normal_form) * BigUint::from(pad_non_top_limb_repr) 
                - BigUint::one()
            ).into();

        pad_top_limb_repr <<= SimulationF::size_in_bits() - (params.num_limbs - 1) * params.bits_per_limb;
        
        let pad_top_limb: ConstraintF = (
            (BigUint::one() + &other.num_of_additions_over_normal_form) * BigUint::from(pad_top_limb_repr)
                - BigUint::one()
            ).into();

        // The shift constants, for most significant limb down to the least significant limb.
        // Overall this is the limb representation of
        // ``
        //      shift = Sum_{i=0..} shift_constant[i] * A^i.
        // `` 
        // Note that by our choice of the shift constants, 
        // ``
        //      shift - R = Sum_{i=0..} (shift_constant[i]- R[i]) * A^i 
        //          < (num_add(R) + 1) * 2^len(p).
        // ``
        let mut pad_limbs = Vec::new();
        pad_limbs.push(pad_top_limb);
        for _ in 0..self.limbs.len() - 1 {
            pad_limbs.push(pad_non_top_limb);
        }

        // `` 
        //      pad_to_kp_gap = delta = - shift mod p 
        // ``
        let pad_to_kp_gap = Self::limbs_to_value(pad_limbs).neg();
        let pad_to_kp_limbs = Self::get_limbs_representations(&pad_to_kp_gap)?;

        // Set D[i] = self[i] + pad_to_kp[i] + pad[i] - other[i] for all i.
        let mut limbs = Vec::new();
        for (i, ((this_limb, other_limb), pad_to_kp_limb)) in self
            .limbs
            .iter()
            .zip(other.limbs.iter())
            .zip(pad_to_kp_limbs.iter())
            .enumerate()
        {
            // TODO: this piece of code can be optimized by integrating pad_limbs in the iterator,
            // and use it in the add_constant.
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

        // From the above comment, 
        // ``
        //   D[i] < [(num_add(L) + 2) + (num_add(R) + 1)] * 2^bits_per_limb[i], 
        // ``
        // for all limbs. Therefore we may set 
        // ``
        //      num_add(D)  = num_add(L) +  num_add(R) + 2.
        // ``
        let result = NonNativeFieldGadget::<SimulationF, ConstraintF> {
            limbs,
            num_of_additions_over_normal_form: BigUint::from(2usize)
                + &self.num_of_additions_over_normal_form
                + &other.num_of_additions_over_normal_form,
            simulation_phantom: PhantomData,
        };

        debug_assert!(
            result.check(),
            "sub(): result fails on check()"
        );

        Ok(result)
    }

    /// For advanced use, multiply and output the intermediate representations (without reduction)
    /// This intermediate representations can be added with each other, and they can later be
    /// reduced back to the `NonNativeFieldGadget`.
    /// Assumes that
    /// ``
    ///     2 * bits_per_limb + surfeit' <= CAPACITY - 2,
    /// ``
    /// where
    /// ``
    ///      surfeit' = log(num_limbs + num_adds(prod) + 1) =
    ///             = log(num_limbs + num_limbs * (num_add(L) + 1) * (num_add(R) + 1)) 
    ///             = log(num_limbs * (1 + (num_add(L) + 1) * (num_add(R) + 1))) =
    /// ``
    //  Costs `num_limbs^2` constraints.
    pub fn mul_without_prereduce<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<NonNativeFieldMulResultGadget<SimulationF, ConstraintF>, SynthesisError> {

        debug_assert!(
            self.check() && other.check(),
            "mul_without_prereduce(): check() failed on input gadgets" 
        );

        // To assure that the limbs of the product representation do not exceed the capacity
        // bound, we demand
        // ``
        //      2 * bits_per_limb + surfeit(product) <= CAPACITY,
        // ``
        // where 
        // ``
        //      surfeit(product) = log(num_limbs * (num_add(L)+1) * (num_add(R) + 1)).
        // ``
        // To allow for a subsequent reduction we need to assure the stricter condition 
        // that 
        // ``
        //     2 * bits_per_limb + surfeit' <= CAPACITY - 2,
        // ``
        // with `surfeit' = log(num_limbs * (num_add(L) + 1) * (num_add(R) + 1) + num_limbs)`.
        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());
        let num_add_bound =  BigUint::from(params.num_limbs) 
            * (BigUint::one() + &self.num_of_additions_over_normal_form)
            * (BigUint::one() + &other.num_of_additions_over_normal_form);

        let surfeit_prime = ceil_log_2!(
            &num_add_bound + BigUint::from(params.num_limbs) 
        );

        if 2 * params.bits_per_limb + surfeit_prime > ConstraintF::Params::CAPACITY as usize - 2 {
            return Err(SynthesisError::Other(format!("Security bound exceeded for mul_without_prereduce. Max: {}, Actual: {}", 
                ConstraintF::Params::CAPACITY as usize - 2, 
                2 * params.bits_per_limb + surfeit_prime 
                ))
            );
        }

        let mut prod_limbs = Vec::new();

        // The naive gathering of the limb representation for the product:
        // ``
        //      prod_limb[k] = Sum_{i+j=k} L[i] * R[j]. 
        // ``
        // Consumes `num_limbs^2` constraints, and `2 * num_limbs^2` 
        // non-zero entries in each of the R1CS matrices (considering the sums 
        // finalized in a new variable).
        
        // TODO: Let us investigate if Karatsuba helps here. 
        let zero = FpGadget::<ConstraintF>::zero(cs.ns(|| "zero"))?;

        for _ in 0..2 * params.num_limbs - 1 {
            prod_limbs.push(zero.clone());
        }

        for i in 0..params.num_limbs {
            for j in 0..params.num_limbs {
                prod_limbs[i + j] = {
                    let mul = self.limbs[i].mul(
                        cs.ns(|| {
                            format!("self.limbs[{}] * other.limbs[{}]", i, j)
                        }),
                        &other.limbs[j],
                    )?;
                    prod_limbs[i + j]
                        .add(cs.ns(|| format!("prod_limbs[{},{}] + mul", i, j)), &mul)
                }?;
            }
        }

        // By the length bound `bits_per_limb +  1 + log(num_add + 1) `, each limb-wise product
        // is bounded by
        // ``
        //      0 <= L[i]*R[i]  < (num_add(L) + 1) * (num_add(R) + 1) * 2^{2 * bits_per_limb[i]}, 
        // ``
        // and hence 
        // ``
        //     0 <= prod_limb[j] < 
        //          num_limbs * (num_add(L) + 1) * (num_add(R) + 1) * 2^bits_per_prod_limb[j],
        // ``
        // where `bits_per_prod_limb[j] = 2 * bits_per_limb` for all except the most significant
        // limb, and `bits_per_prod_limb[0] = 2 * bits_per_limb[0]`.
        // Hence we may set 
        // ``
        //      num_add(product) =  num_limbs * (num_add(L) + 1) * (num_add(R) + 1) - 1. 
        // ``
        let result = NonNativeFieldMulResultGadget {
            limbs: prod_limbs,
            num_add_over_normal_form: &num_add_bound - &BigUint::one(),
            simulation_phantom: PhantomData,
        };

        debug_assert!(
            result.check(),
            "mul_without_prereduce(): result failed on check()"
        );

        Ok(result)
    }

    /// For advanced use, multiply and output the intermediate representations (without reduction)
    /// This intermediate representations can be added with each other, and they can later be
    /// reduced back to the `NonNativeFieldGadget`.
    /// Assumes that
    /// ``
    ///     2 * bits_per_limb + surfeit' <= CAPACITY - 2,
    /// ``
    /// where
    /// ``
    ///      surfeit' = log(num_limbs^2 * (num_add(L)+1) + 1).
    /// ``
    pub fn mul_by_constant_without_prereduce<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &SimulationF,
    ) -> Result<NonNativeFieldMulResultGadget<SimulationF, ConstraintF>, SynthesisError> {
        // To assure that the limbs of the product representation do not exceed the capacity
        // bound, we demand
        // ``
        //      2 * bits_per_limb + surfeit(product) <= CAPACITY,
        // ``
        // where 
        // ``
        //      surfeit(product) = log(num_limbs * (num_add(L)+1)).
        // ``
        // To allow for a subsequent reduction we need to assure the stricter condition 
        // that 
        // ``
        //     2 * bits_per_limb + surfeit' <= CAPACITY - 2,
        // ``
        // with `surfeit' = log(num_limbs * (num_add(L) + 1)  + num_limbs)`.
        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());
        let num_add_bound =  BigUint::from(params.num_limbs) 
            * (BigUint::one() + &self.num_of_additions_over_normal_form);

        let surfeit_prime = ceil_log_2!(
            &num_add_bound + BigUint::from(params.num_limbs) 
        );

        if 2 * params.bits_per_limb + surfeit_prime > ConstraintF::Params::CAPACITY as usize - 2 {
            return Err(SynthesisError::Other(format!("Security bound exceeded for mul_by_constant_without_prereduce. Max: {}, Actual: {}", 
                ConstraintF::Params::CAPACITY as usize - 2, 
                2 * params.bits_per_limb + surfeit_prime )));
        }

        let mut prod_limbs = Vec::new();
        let other_limbs = Self::get_limbs_representations(other)?;

        // The naive gathering of the limb representation for the product:
        // ``
        //      prod_limb[k] = Sum_{i+j=k} L[i] * R[j]. 
        // ``
        // Consumes `num_limbs^2` constraints, and `2 * num_limbs^2` 
        // non-zero entries in each of the R1CS matrices (considering the sums 
        // finalized in a new variable).
        
        // TODO: Let us investigate if Karatsuba helps here. 
        let zero = FpGadget::<ConstraintF>::zero(cs.ns(|| "zero"))?;

        for _ in 0..2 * params.num_limbs - 1 {
            prod_limbs.push(zero.clone());
        }

        for i in 0..params.num_limbs {
            for j in 0..params.num_limbs {
                prod_limbs[i + j] = {
                    let mul = self.limbs[i].mul_by_constant(
                        cs.ns(|| {
                            format!("self.limbs[{}] * other.limbs[{}]", i, j)
                        }),
                        &other_limbs[j],
                    )?;
                    prod_limbs[i + j]
                        .add(cs.ns(|| format!("prod_limbs[{},{}] + mul", i, j)), &mul)
                }?;
            }
        }

        // By the length bound `bits_per_limb +  1 + log(num_add + 1) `, each limb-wise product
        // is bounded by
        // ``
        //      0 <= L[i]*R[i]  < (num_add(L) + 1) * (num_add(R) + 1) * 2^{2 * bits_per_limb[i]}, 
        // ``
        // and hence 
        // ``
        //     0 <= prod_limb[j] < 
        //          num_limbs * (num_add(L) + 1) * (num_add(R) + 1) * 2^bits_per_prod_limb[j],
        // ``
        // where `bits_per_prod_limb[j] = 2 * bits_per_limb` for all except the most significant
        // limb, and `bits_per_prod_limb[0] = 2 * bits_per_limb[0]`.
        // Hence we may set 
        // ``
        //      num_add(product) =  num_limbs * (num_add(L) + 1) * (num_add(R) + 1) - 1. 
        // ``
        Ok(NonNativeFieldMulResultGadget {
            limbs: prod_limbs,
            num_add_over_normal_form: num_add_bound - BigUint::one(),
            simulation_phantom: PhantomData,
        })
    }

    /// Enforces two non-native gadgets, not necessarily in normal form, to be equal mod the 
    /// non-native modulus `p`. Assumes that 
    /// ``
    ///    bits_per_limb + surfeit <= CAPACITY - 2,
    /// ``
    /// where 
    /// ``
    ///    surfeit = 1 + log(3 + num_add(L) + num_add(R)).
    /// ``
    // Costs 
    // ``
    //     C = 3 * S + surfeit + num_limbs(p) + 1,
    // ``
    // where 
    // ``
    //      S =  2 + Floor[
    //          (ConstraintF::CAPACITY - 2 - surfeit) / bits_per_limb
    //          ].   
    // ``
    pub(crate) fn conditional_enforce_equal_without_prereduce<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
        should_enforce: &Boolean,
    ) -> Result<(), SynthesisError> {
        debug_assert!(
            self.check() && other.check(),
            "conditional_enforce_equal_without_prereduce(): check() failed on input gadgets" 
        );
        
        // The sub_without_prereduce() applied below assumes that 
        // ``
        //     bits_per_limb + log(num_add(L) + num_add(R) + 5) <= CAPACITY - 2,
        // `` 
        // which is weaker than 
        // ``
        //     bits_per_limb + 1 + log(num_add(L) + num_add(R) + 3) <= CAPACITY - 2,
        // `` 
        // as demanded by the group_and_check_equality().
        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());
        let surfeit = 1 + ceil_log_2!(&self.num_of_additions_over_normal_form 
            + &other.num_of_additions_over_normal_form
            + BigUint::from(3usize)
        );
        if params.bits_per_limb + surfeit > ConstraintF::Params::CAPACITY as usize - 2 {
            return Err(
                SynthesisError::Other(
                    format!("Security bound exceeded for conditional_enforce_equality_without_prereduce. Max: {}, Actual: {}", 
                    ConstraintF::Params::CAPACITY as usize - 2, params.bits_per_limb + surfeit)
                )
            );
        }

        // Equality mod p is proven by the integer equation
        // ``
        //       Sum_{i=0}^{num_limbs -1} D[i] * A^i   = k * p,
        // ``
        // where the `D[i]` are the limbs of the sub_without_prereduce of `L` and `R`,
        // and `A = 2^bits_per_limb`.
        // As the left hand side is bounded by
        // ``
        //      Sum_{i=0}^{num_limbs -1} D[i] * A^i < (num_add(D) + 1) * 2^len(p),
        // ``   
        // the factor `k` is length bounded by
        // ``
        //      len(k) <= 1 + log(num_add(D) + 1),
        // ``
        // hence a single field element is good enough.
        
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
            num_of_additions_over_normal_form: BigUint::zero(),
            simulation_phantom: PhantomData,
        };

        // Compute `delta = self - other`, costs no constraints. 
        let zero = Self::zero(cs.ns(|| "hardcode zero"))?;
        let mut delta = self.sub_without_prereduce(cs.ns(|| "delta = self - other"), other)?;
        
        debug_assert!(
            1 + ceil_log_2!(BigUint::one() + &delta.num_of_additions_over_normal_form) == surfeit 
        );

        delta = Self::conditionally_select(
            cs.ns(|| "select delta or zero"),
            should_enforce,
            &delta,
            &zero,
        )?;

        // We have
        // ``
        //      k = D / p <= (1 + num_add(D)) * 2^len(p) / p 
        //                <= (1 + num_add(D)) * 2,
        // ``
        // where `1 + num_add(D)` is assured to be smaller than `p` by the 
        // sub_without_prereduce(). Hence `k` can be allocated as a single 
        // field element, the bit length of which is bounded by the condition
        // ``
        //      len(k) <= 1 + log(1 + num_add(D)).
        // ``
        // Costs `surfeit = 1 + log(3 + num_add(L) + num_add(R))` constraints.
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

        //let surfeit = 1 + ceil_log_2!(delta.num_of_additions_over_normal_form + BigUint::one());
        Reducer::<SimulationF, ConstraintF>::limb_to_bits(
            cs.ns(|| "k limb to bits"),
            &k_gadget,
            surfeit,
        )?;

        // Compute k * p limbwise. Each limb is bounded by
        // ``
        //      limb[i] < 2^surfeit * 2^bits_per_limb,
        // ``
        // and similarly for the most significant limb.
        // Costs `num_limbs` many constraints.
        let mut kp_gadget_limbs = Vec::new();
        for (i, limb) in p_gadget.limbs.iter().enumerate() {
            let mul = limb.mul(cs.ns(|| format!("limb_{} * k_gadget", i)), &k_gadget)?;
            kp_gadget_limbs.push(mul);
        }

        // Enforce `delta = k*p` as big integers. Note that the surfeit of `k*p` is 
        // `1 + log(1 + num_adds(D))`, which is larger than the surfeit of `delta`.
        // Costs
        // ``
        //  (S-1) * (1 + limb_size + 2 - shift_per_limb) + 1 =
        //      (S-1) * (3 + surfeit) + 1
        // ``             
        // constraints, where
        // `` 
        // S - 1 = Floor[
        //          (ConstraintF::CAPACITY - 2 - (bits_per_limb + surfeit)) / bits_per_limb
        //      ] 
        //      =  1 + Floor[
        //          (ConstraintF::CAPACITY - 2 - surfeit) / bits_per_limb
        //      ],
        // ``
        // and `surfeit = len(3 + num_add(L) + num_add(R))`.
        // Succeeds iff 
        // ``
        //      bits_per_limb + surfeit  <= ConstraintF::CAPACITY - 2.
        // `` 
        Reducer::<SimulationF, ConstraintF>::group_and_check_equality(
            cs.ns(|| "group and check equality"),
            surfeit,
            params.bits_per_limb,
            params.bits_per_limb,
            &delta.limbs,
            &kp_gadget_limbs,
        )
    }

    pub(crate) fn enforce_equal_without_prereduce<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
        other: &Self,
    ) -> Result<(), SynthesisError> {
        self.conditional_enforce_equal_without_prereduce(cs, other, &Boolean::constant(true))
    }
}


/*******************************************************************************
 * 
 *  The high-level functions for arithmetic mod p: Implementation of FieldGadget
 * 
 * *****************************************************************************/
impl<SimulationF: PrimeField, ConstraintF: PrimeField> TryInto<Boolean> for NonNativeFieldGadget<SimulationF, ConstraintF> {
    type Error = SynthesisError;

    fn try_into(self) -> Result<Boolean, Self::Error> {
        unimplemented!()
    }
}

impl<SimulationF: PrimeField, ConstraintF: PrimeField> FromGadget<Boolean, ConstraintF> for NonNativeFieldGadget<SimulationF, ConstraintF> {
    fn from<CS: ConstraintSystemAbstract<ConstraintF>>(_other: Boolean, _cs: CS) -> Result<Self, SynthesisError> {
        unimplemented!()
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

    fn zero<CS: ConstraintSystemAbstract<ConstraintF>>(cs: CS) -> Result<Self, SynthesisError> {
        Ok(Self::from_value(cs, &SimulationF::zero()))
    }

    fn one<CS: ConstraintSystemAbstract<ConstraintF>>(cs: CS) -> Result<Self, SynthesisError> {
        Ok(Self::from_value(cs, &SimulationF::one()))
    }

    fn conditionally_add_constant<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        _cs: CS,
        _cond: &Boolean,
        _other: SimulationF,
    ) -> Result<Self, SynthesisError> {
        unimplemented!();
    }

    fn conditionally_add<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        cond: &Boolean,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        let added_values_g = self.add(cs.ns(|| "added values"),&other)?;
        Self::conditionally_select(
            cs.ns(|| "select added_values or original value"),
            cond,
            &added_values_g,
            &self
        )
    }

    /// Addition of non-natives, outputs non-normal form.
    fn add<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        let mut elem_self = self.clone();
        let mut elem_other = other.clone();

        // pre reduction step
        Reducer::<SimulationF, ConstraintF>::pre_add_reduce(
            cs.ns(|| "pre add reduce"),
            &mut elem_self,
            &mut elem_other
        )?;
        
        // add
        elem_self.add_without_prereduce(
            cs.ns(|| "add without prereduce"),
            &elem_other
        )
    }

    /// Subtract a nonnative field element `other` from `self` modulo `p`. Outputs 
    /// non-normal form.
    // NOTE: Costs no constraints, if pre-reduction is not applied, and only slightly 
    // increases the additions over normal form.
    fn sub<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {

        // pre-reduction step
        let mut elem_self = self.clone();
        let mut elem_other = other.clone();
        Reducer::pre_sub_reduce(
            cs.ns(|| "pre sub reduce"),
            &mut elem_self,
            &mut elem_other,
        )?;
        
        // sub
        elem_self.sub_without_prereduce(
         cs.ns(|| "sub_without_prereduce"),
            &elem_other
        )
    }

    fn negate<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<Self, SynthesisError> {
        Self::zero(cs.ns(|| "hardcode zero"))?.sub(cs.ns(|| "0 - self"), self)
    }

    /// Multiplication of two non-natives, reduced back to normal form. 
    // If no prereduction step is performed, costs
    // ``
    //     C =  2 *(len(p) + num_limbs^2) + surfeit' 
    //          +  (num_groups - 1) * (3 + bits_per_limb + surfeit') + 1
    // ``
    // constraints, where 
    // ``
    //      surfeit' =  log(num_limbs + 2 * (num_adds(prod) + 1))
    //              = log(num_limbs +  2 * num_limbs * (num_add(L)+1) * (num_add(R) + 1)),
    //      num_groups = Ceil[(2 * num_limbs - 1)/ S],
    // ``
    // and
    // ``
    //    S - 1 = Floor[
    //          (ConstraintF::CAPACITY - 2 - surfeit') / bits_per_limb
    //          ] - 2.
    // ``
    fn mul<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        // Step 1: reduce `self` and `other` if necessary
        let mut self_reduced = self.clone();
        let mut other_reduced = other.clone();

        Reducer::<SimulationF, ConstraintF>::pre_mul_reduce(
            cs.ns(|| "pre mul reduce"),
            &mut self_reduced,
            &mut other_reduced,
        )?;

        // Step 2: mul without pre reduce
        let res = self_reduced.mul_without_prereduce(
            cs.ns(|| "mul"),
            &other_reduced
        )?;

        // Step 3: reduction of the product to normal form
        let res_reduced = res.reduce(cs.ns(|| "reduce result"))?;

        Ok(res_reduced)
    }

    fn add_constant<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &SimulationF,
    ) -> Result<Self, SynthesisError> {
        let other_g = Self::from_value(cs.ns(|| "hardcode add constant"), other);
        self.add(cs.ns(|| "add constant"), &other_g)
    }

    fn sub_constant<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        fe: &SimulationF,
    ) -> Result<Self, SynthesisError> {
        // TODO: an add with fe.neg() is slightly more efficient in terms
        // of the limb bounds.
        let other_g = Self::from_value(cs.ns(|| "hardcode sub constant"), fe);
        self.sub(cs.ns(|| "subtract constant"), &other_g)
    }

    fn mul_by_constant<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        fe: &SimulationF,
    ) -> Result<Self, SynthesisError> {
        
        // Step 1: reduce `self` if necessary. As a workaround
        // we alloc a separate Nonnative, which never undergoes
        // a reduction.
        // TODO: let us improve this.
        let mut self_reduced = self.clone();
        let mut other = NonNativeFieldGadget::from_value(
            cs.ns(|| "hardcode other"),
            fe
        );
        Reducer::<SimulationF, ConstraintF>::pre_mul_reduce(
            cs.ns(|| "pre mul reduce"),
            &mut self_reduced,
            &mut other,
        )?;

        assert!(self.check(),
            "self after pre-reduction failed on check()"
        );

        // Step 2: mul without pre reduce
        let res = self_reduced.mul_by_constant_without_prereduce(
            cs.ns(|| "mul"),
            fe
        )?;

        // Step 3: reduction of the product to normal form
        let res_reduced = res.reduce(cs.ns(|| "reduce result"))?;
        Ok(res_reduced)
    }

    // TODO: This is as the default implementation. I have put it here
    // as we can implement an improved variant, which does not reduce
    // twice. 
    fn mul_equals<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
        result: &Self,
    ) -> Result<(), SynthesisError> {
        debug_assert!(
            self.check() && other.check(),
            "mul_equals(): check() failed on input gadgets " 
        );
        let actual_result = self.mul(cs.ns(|| "calc_actual_result"), other)?;
        debug_assert!(
            actual_result.check(),
            "mul_equals(): check() failed on actual_result." 
        );

        result.enforce_equal(&mut cs.ns(|| "test_equals"), &actual_result)
    }

    fn inverse<CS: ConstraintSystemAbstract<ConstraintF>>(
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
    fn frobenius_map<CS: ConstraintSystemAbstract<ConstraintF>>(
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


/*******************************************************************************
 * 
 *  Various other gadgets for NonNativeFieldGadgets
 * 
 * *****************************************************************************/

impl<SimulationF: PrimeField, ConstraintF: PrimeField> AllocGadget<SimulationF, ConstraintF>
for NonNativeFieldGadget<SimulationF, ConstraintF>
{
    /// Allocates a non-native field element and enforces normal form, which consumes at most 
    /// `bits_per_limb` many bits per limb, and and altogether at most (non-native) modulus 
    /// many bits.
    fn alloc<F, T, CS: ConstraintSystemAbstract<ConstraintF>>(
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
            num_of_additions_over_normal_form: BigUint::zero(),
            simulation_phantom: PhantomData,
        })
    }

    fn alloc_input<F, T, CS: ConstraintSystemAbstract<ConstraintF>>(
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

        Ok(Self {
            limbs,
            num_of_additions_over_normal_form: BigUint::zero(),
            simulation_phantom: PhantomData,
        })
    }
}

impl<SimulationF: PrimeField, ConstraintF: PrimeField> Clone
 for NonNativeFieldGadget<SimulationF, ConstraintF>
{
 fn clone(&self) -> Self {
     NonNativeFieldGadget {
         limbs: self.limbs.clone(),
         num_of_additions_over_normal_form: self.num_of_additions_over_normal_form.clone(),
         simulation_phantom: PhantomData,
     }
 }
}

impl<SimulationF: PrimeField, ConstraintF: PrimeField> ConstantGadget<SimulationF, ConstraintF>
    for NonNativeFieldGadget<SimulationF, ConstraintF>
{
    fn from_value<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        value: &SimulationF,
    ) -> Self {
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
            num_of_additions_over_normal_form: BigUint::zero(),
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
    // Returns the big endian bit representation of `self mod p`. 
    fn to_bits<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        self.to_bits_strict(cs)
    }

    // Returns the big endian bit representation of `self mod p`. 
    fn to_bits_strict<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> 
    {
        // alloc a vector of SimulationF many Booleans, representing the bits of 'self'.
        // big endian order
        let bits = Vec::<Boolean>::alloc(
            cs.ns(|| "alloc self bits"),
            || Ok(self.get_value().unwrap_or_default().write_bits())
        )?;

        // enforce the bits being strictly smaller than the modulus
        Boolean::enforce_in_field::<_, _, SimulationF>(&mut cs, bits.as_slice())?;

        // construct another NonNativeFieldGadget out of the 'self' bits
        let other_self = Self::from_bits(
            cs.ns(|| "construct other self from self bits"),
            bits.as_slice()
        )?;

        // enforce the equality with 'self'
        self.enforce_equal(
            cs.ns(|| "self == from_bits(self_bits)"),
            &other_self
        )?;

        // Return bits
        Ok(bits)
    }
}

impl<SimulationF: PrimeField, ConstraintF: PrimeField> FromBitsGadget<ConstraintF>
    for NonNativeFieldGadget<SimulationF, ConstraintF>
{
    // Packs a big endian bit sequence (which does not exceed the length of a normal form) 
    // into a NonNativeFieldGadget
    fn from_bits<CS: ConstraintSystemAbstract<ConstraintF>>(
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
    // Returns the big endian bit representation of `self mod p`. 
    fn to_bytes<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        // big endian bits of `&self`
        let mut bits = self.to_bits(cs.ns(|| "self to bits"))?;

        let mut bytes = Vec::<UInt8>::new();

        // convert to little endian, split into chunks of 8 bits,
        // and define a `UInt8` from them.
        bits.reverse();
        bits.chunks(8).for_each(
            |bits_per_byte| {
                let mut bits_per_byte: Vec<Boolean> = bits_per_byte.to_vec();
                if bits_per_byte.len() < 8 {
                    bits_per_byte.resize_with(8, || Boolean::constant(false));
                }

                bytes.push(UInt8::from_bits_le(&bits_per_byte));
            }
        );

        Ok(bytes)
    }

    fn to_bytes_strict<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        // 
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
    fn conditionally_select<CS: ConstraintSystemAbstract<ConstraintF>>(
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
                true_value.num_of_additions_over_normal_form.clone(),
                false_value.num_of_additions_over_normal_form.clone(),
            ),
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

    fn two_bit_lookup<CS: ConstraintSystemAbstract<ConstraintF>>(
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
            num_of_additions_over_normal_form: BigUint::zero(),
            simulation_phantom: PhantomData,
        })
    }

    fn two_bit_lookup_lc<CS: ConstraintSystemAbstract<ConstraintF>>(
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
            num_of_additions_over_normal_form: BigUint::zero(),
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

    fn three_bit_cond_neg_lookup<CS: ConstraintSystemAbstract<ConstraintF>>(
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
            num_of_additions_over_normal_form: BigUint::zero(),
            simulation_phantom: PhantomData,
        })
    }

    fn cost() -> usize {
        let num_limbs =
            get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits()).num_limbs;
        num_limbs * <FpGadget<ConstraintF> as ThreeBitCondNegLookupGadget<ConstraintF>>::cost()
    }
}

impl<'a, SimulationF: PrimeField, ConstraintF: PrimeField> ToConstraintFieldGadget<ConstraintF>
for &'a [NonNativeFieldGadget<SimulationF, ConstraintF>]
{
    type FieldGadget = FpGadget<ConstraintF>;

    fn to_field_gadget_elements<CS: ConstraintSystemAbstract<ConstraintF>>(&self, mut cs: CS) -> Result<Vec<Self::FieldGadget>, SynthesisError> {

        // Range proof
        let mut bits = Vec::new();
        for (i, elem) in self.iter().enumerate() {
            let mut elem_bits = elem.to_bits_strict(
                cs.ns(|| format!("to bits strict elem {}", i))
            )?;
            bits.append(&mut elem_bits);
        }

        // Efficient packing
        bits
            .chunks(ConstraintF::Params::CAPACITY as usize)
            .into_iter()
            .enumerate()
            .map(|(i, bits)| FpGadget::<ConstraintF>::from_bits(
                cs.ns(|| format!("bit chunk {} to field", i)),
                bits
            )).collect::<Result<Vec<_>, _>>()
    }
}

impl<SimulationF: PrimeField, ConstraintF: PrimeField> EqGadget<ConstraintF>
    for NonNativeFieldGadget<SimulationF, ConstraintF>
{
    // Naive implementation
    fn is_eq<CS: ConstraintSystemAbstract<ConstraintF>>(
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

    // Enforces two non-native gadgets, not necessarily in normal form, to be equal mod the 
    // non-native modulus `p`. 
    fn conditional_enforce_equal<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
        should_enforce: &Boolean,
    ) -> Result<(), SynthesisError> {
        debug_assert!(
            self.check() && other.check(),
            "conditional_enforce_equal(): check() failed on input gadgets" 
        );
        // pre-reduction step
        let mut elem_self = self.clone();
        let mut elem_other = other.clone();
        Reducer::pre_enforce_equal_reduce(
            cs.ns(|| "pre sub reduce"),
            &mut elem_self,
            &mut elem_other,
        )?;
        
        elem_self.conditional_enforce_equal_without_prereduce(cs.ns(|| "elem_self == elem_other"), 
            &elem_other,
            &should_enforce
        )?;

        Ok(())
    }

    fn conditional_enforce_not_equal<CS: ConstraintSystemAbstract<ConstraintF>>(
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
