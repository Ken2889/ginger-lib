//! A submodule of low-level functions for modular reduction/normalization of non-native field gadgets.
use algebra::{
    biginteger::BigInteger,
    fields::{FpParameters, PrimeField},
};

use crate::{
    fields::{
        fp::FpGadget,
        nonnative::{
            nonnative_field_gadget::{
                NonNativeFieldGadget,
                bigint_to_constraint_field, limbs_to_bigint
            }, 
            params::get_params, 
        },
    },
    ceil_log_2,
    prelude::*,
};
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use std::{cmp::min, marker::PhantomData, vec::Vec};

use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{One, Zero};

use crate::fields::FieldGadget;

/// The collections of methods for reducing the presentations of NonNativeFieldGadgets
pub struct Reducer<SimulationF: PrimeField, ConstraintF: PrimeField> {
    pub simulation_phantom: PhantomData<SimulationF>,
    pub constraint_phantom: PhantomData<ConstraintF>,
}

impl<SimulationF: PrimeField, ConstraintF: PrimeField> Reducer<SimulationF, ConstraintF> {
    /// Convert a limb of `num_bits` into a vector of Boolean gadgets.
    /// Allowing `num_bits` to be at most `ConstraintF::size_in_bits() - 1` for efficient 'unpacking'.
    // Consumes `num_bits` + 1 constraints.
    pub fn limb_to_bits<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        limb: &FpGadget<ConstraintF>,
        num_bits: usize,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        let num_bits = min(num_bits, ConstraintF::Params::CAPACITY as usize);

        // we extract the bits from the `num_bits` least significant bits
        let to_skip = ConstraintF::size_in_bits() - num_bits;
        assert!(to_skip <= ConstraintF::size_in_bits());

        limb.to_bits_with_length_restriction(cs.ns(|| "limb to bits"), to_skip)
    }

    /// Reduction to normal form, which again has no excess in its limbs.
    /// Assumes that 
    /// ``
    ///     bits_per_limb + 1 + log(num_add(elem) + 3) <= CAPACITY - 2.
    /// ``
    // Costs`
    //    ``
    //     C = len(p) + 3 * S + surfeit + num_limbs(p) + 1
    // ``
    // constraints, where 
    // ``
    //      S =  2 + Floor[
    //          (ConstraintF::CAPACITY - 2 - surfeit) / bits_per_limb
    //          ],   
    // ``
    // and `surfeit = log(3 + num_add(elem))`.
    pub fn reduce<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        elem: &mut NonNativeFieldGadget<SimulationF, ConstraintF>,
    ) -> Result<(), SynthesisError> {
        // Alloc of a non-native in normal form (not necessarily below the
        // non-native modulus)
        let new_elem = NonNativeFieldGadget::alloc(cs.ns(|| "alloc normal form"), || {
            Ok(elem.get_value().unwrap_or_default())
        })?;

        // We do not need to panic if the aforementioned assumption is not met,
        // as enforce_equal_without_prereduce() will do.
        elem.enforce_equal_without_prereduce(cs.ns(|| "elem == new_elem"), &new_elem)?;
        *elem = new_elem;
        Ok(())
    }

    fn reduce_until_cond_is_satisfied<F, CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        elem: &mut NonNativeFieldGadget<SimulationF, ConstraintF>,
        elem_other: &mut NonNativeFieldGadget<SimulationF, ConstraintF>,
        exit_cond: F
    ) -> Result<(), SynthesisError>
    where
        F: Fn(&NonNativeFieldGadget<SimulationF, ConstraintF>, &NonNativeFieldGadget<SimulationF, ConstraintF>) -> bool
    {
        let mut i = 0;
        while !exit_cond(elem, elem_other) {
            if elem.num_of_additions_over_normal_form >= elem_other.num_of_additions_over_normal_form
            {
                Self::reduce(cs.ns(|| format!("reduce elem {}", i)), elem)?;
            } else {
                Self::reduce(cs.ns(|| format!("reduce elem other {}", i)), elem_other)?;
            }
            i += 1;
        }
        Ok(())
    }

    /// Optional reduction which assures that the resulting operands produce a "reducible" sum. 
    pub(crate) fn pre_add_reduce<CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        elem: &mut NonNativeFieldGadget<SimulationF, ConstraintF>,
        elem_other: &mut NonNativeFieldGadget<SimulationF, ConstraintF>,
    ) -> Result<(), SynthesisError> {
        debug_assert!(
            elem.check() && elem_other.check(),
            "pre_add_reduce(): check() failed on input gadgets"
        );

        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());
        // To output a sum which does not exceed the capacity bound, we need to demand that
        // ``
        //     bits_per_limb + log(num_add(sum) + 1) <= CAPACITY,
        // `` 
        // where `num_add(sum) = num_add(L) + num_add(R) + 1`. To allow a subsequent reduction 
        // we need to assure the stricter condition
        // ``
        //     bits_per_limb + log(num_add(sum) + 3) <= CAPACITY - 3.
        // `` 
        Self::reduce_until_cond_is_satisfied(
            cs,
            elem,
            elem_other,
            |elem, elem_other| {
                let sum_add = &elem.num_of_additions_over_normal_form + &elem_other.num_of_additions_over_normal_form;
                let surfeit = ceil_log_2!(sum_add + BigUint::from(3usize));
                surfeit + params.bits_per_limb <= ConstraintF::Params::CAPACITY as usize - 3
            }
        )
    }

    /// Optional reduction which assures that the resulting operands produce a "reducible" sub result. 
    pub(crate) fn pre_sub_reduce<CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        elem: &mut NonNativeFieldGadget<SimulationF, ConstraintF>,
        elem_other: &mut NonNativeFieldGadget<SimulationF, ConstraintF>,
    ) -> Result<(), SynthesisError> {
        debug_assert!(
            elem.check() && elem_other.check(),
            "pre_sub_reduce(): check() failed on input gadgets"
        );

        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());
        // The sub_without_prereduce() assumes that 
        // ``
        //     bits_per_limb + len(num_add(L) + num_add(R) + 5) <= CAPACITY - 3,
        // `` 
        // to assure a secure substraction together with an optional reduce.
        Self::reduce_until_cond_is_satisfied(
            cs,
            elem,
            elem_other,
            |elem, elem_other| {
                let sum_add = &elem.num_of_additions_over_normal_form + &elem_other.num_of_additions_over_normal_form;
                let surfeit = ceil_log_2!(sum_add + BigUint::from(5usize));
                surfeit + params.bits_per_limb <= ConstraintF::Params::CAPACITY as usize - 3
            }
        )
    }

    /// Reduction used before multiplication to assure that the limbs of the product of the
    /// the two non-natives `elem` and `elem_other` are length bounded by CAPACITY - 1. 
    /// Optionally reduces one or both of the operands to normal form.
    pub(crate) fn pre_mul_reduce<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        elem: &mut NonNativeFieldGadget<SimulationF, ConstraintF>,
        elem_other: &mut NonNativeFieldGadget<SimulationF, ConstraintF>,
    ) -> Result<(), SynthesisError> {
        debug_assert!(
            elem.check() && elem_other.check(),
            "pre_mul_reduce(): check() failed on input gadgets"
        );

        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());

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
        // where
        // ``
        //      surfeit' =log(num_limbs * (1 + (num_add(L) + 1) * (num_add(R) + 1))).
        // ``
        Self::reduce_until_cond_is_satisfied(
            cs.ns(|| "pre mul reduce"),
            elem,
            elem_other,
            |elem, elem_other| {
                let term = (BigUint::one() + &elem.num_of_additions_over_normal_form)
                    * (BigUint::one() + &elem_other.num_of_additions_over_normal_form)
                    + BigUint::one();
                let surfeit_prime = ceil_log_2!(
                    BigUint::from(params.num_limbs) * term
                );
    
                2 * params.bits_per_limb + surfeit_prime <= ConstraintF::Params::CAPACITY as usize - 2
            }
        )?;

        Ok(())
    }

     /// Optional reduction which assures that the resulting operands produce do not exceed
     /// the capacity bound for a enforce_equal_without_prereduce(). 
     pub(crate) fn pre_enforce_equal_reduce<CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        elem: &mut NonNativeFieldGadget<SimulationF, ConstraintF>,
        elem_other: &mut NonNativeFieldGadget<SimulationF, ConstraintF>,
    ) -> Result<(), SynthesisError> {
        debug_assert!(
            elem.check() && elem_other.check(),
            "pre_sub_reduce(): check() failed on input gadgets"
        );

        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());
        // The enforce_equal_without_prereduce() assumes that
        // ``
        //    bits_per_limb + surfeit <= CAPACITY - 2,
        // ``
        // where 
        // ``
        //    surfeit = 1 + log(3 + num_add(L) + num_add(R)).
        // ``
        Self::reduce_until_cond_is_satisfied(
            cs,
            elem,
            elem_other,
            |elem, elem_other| {
                let sum_add = &elem.num_of_additions_over_normal_form + &elem_other.num_of_additions_over_normal_form;
                let surfeit = 1 + ceil_log_2!(sum_add + BigUint::from(3usize));
                surfeit + params.bits_per_limb <= ConstraintF::Params::CAPACITY as usize - 2
            }
        )
    }

    /// The core piece for comparing two big integers in non-normal form. 
    /// Checks the equality of 
    /// ``
    ///     left = Sum_{i=0..} left[i] * A^i, 
    ///     right= Sum_{i=0..} right[i] * A^i,
    /// `` 
    /// given as equally long slices of limbs 
    /// ``
    ///     [left[0], left[1], ...], 
    ///     [right[0], right[1], ...],
    /// `` 
    /// with each limb being length bounded by 
    /// ``
    ///     limb_size = bits_per_limb + surfeit.
    /// `` 
    /// Implements the grouping technique from [[Kosba et al]] to reduce the number of 
    /// constraints for the carries. 
    /// Assumes that
    /// ``
    ///     bits_per_limb + surfeit + 2 <= ConstraintF::CAPACITY,
    /// ``
    /// and `shift_per_limb >= 2`. 
    /// 
    /// [Kosba et al]: https://ieeexplore.ieee.org/document/8418647
    /// 
    // Costs
    // ``
    //      (num_groups - 1) * (1 + bits_per_limb + surfeit + 2 - shift_per_limb) + 2
    // ``
    // constraints, where `1 <= num_groups <= num_limbs` is the number of groups, determined
    // by `num_groups = Ceil[num_limbs / S]` with 
    // ``
    //  S - 1 = Floor[
    //          (ConstraintF::CAPACITY - 2 - (bits_per_limb + surfeit)) / shift_per_limb
    //      ].
    // ``
    // TODO: can be slightly optimized by using the number of additions over normal
    // form instead of `surfeit`.
    pub fn group_and_check_equality<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        // The additional number of bits beyond `bits_per_limb`. Hence the current
        // limbsize is `bits_per_limb + surfeit`.
        surfeit: usize,
        // The number of bits  
        bits_per_limb: usize,
        // defines arity of the limb representation, i.e. `A= 2^shift_per_limb`.
        // MUST be >= 2.
        shift_per_limb: usize,
        left: &[FpGadget<ConstraintF>],
        right: &[FpGadget<ConstraintF>],
    ) -> Result<(), SynthesisError> {
        
        let zero = FpGadget::<ConstraintF>::zero(cs.ns(|| "hardcode zero"))?;

        let mut limb_pairs = Vec::<(FpGadget<ConstraintF>, FpGadget<ConstraintF>)>::new();
        // We group the limbs so that we can handle their sum
        // ``
        //      group_total = limb[0] * 1 + limb[1] * A + ... + limb[S-1] * A^{S-1},
        // ``
        // within a single constraint field element. Assuming that `A >= 2` we have 
        // `2 * A^i <= A^{i+1}` and therefore
        // `` 
        //   limb[0] + limb[1] * A < 2 * A * 2^limb_size
        //   limb[0] + limb[1] * A + limb[2] * A^2 < 2 * A^2 * 2^limb_size
        //   ...
        //   limb[0] + limb[1] * A + ... + limb[S-1] * A^{S-1} <
        //                       < 2 * A^{S-1} * 2^limb_size.
        // ``
        // Hence `len(group_total) <= bits_per_group`, with 
        // ``
        //     bits_per_group = limb_size + 1 + (S - 1) * shift_per_limb.
        // ``
        // To assure that the following operations on the totals do not exceed the capacity, 
        // it is sufficient to demand 
        // ``
        //      bits_per_group + 1 <= ConstraintF::CAPACITY,
        // ``
        // as described in detail below. This yields the security condition
        // ``
        //      bits_per_limb + surfeit + (S - 1) * shift_per_limb + 2 <= ConstraintF::CAPACITY,
        // ``
        // where
        // ``
        //      S - 1 = Floor[
        //          (ConstraintF::CAPACITY - 2 - (bits_per_limb + surfeit)) / shift_per_limb
        //      ].
        // ``

        if shift_per_limb < 2 {
            return Err(SynthesisError::Other(format!("shift_per_limb must be smaller than 2. Found: {}", shift_per_limb)));
        }
        
        if ConstraintF::Params::CAPACITY as usize - 2 < surfeit + bits_per_limb 
        {
            return Err(SynthesisError::Other(format!("Security bound exceeded for group_and_check_equality. Max: {}, Actual: {}", ConstraintF::Params::CAPACITY as usize - 2, surfeit + bits_per_limb)));
        }

        // TODO: remove the following assert. Don't know why I put it there.
        assert!(bits_per_limb >= shift_per_limb);  
        
        let num_limb_in_a_group = (ConstraintF::Params::CAPACITY as usize
            - 2
            - surfeit
            - bits_per_limb)
            / shift_per_limb
            + 1;

        assert!(num_limb_in_a_group > 0);

        // Compute the powers of the arity for a group of limbs, i.e.
        // `shift_array = [1, A, A^2, ..., A^(num_limbs_per_group-1)}]`.
        let shift_array = {
            let mut array = Vec::new();
            let mut cur = ConstraintF::one().into_repr();
            for _ in 0..num_limb_in_a_group {
                array.push(ConstraintF::from_repr(cur));
                cur.muln(shift_per_limb as u32);
            }

            array
        };

        // zip the limbs of `left` and `right` and reverse to little endian order.
        for (left_limb, right_limb) in left.iter().zip(right.iter()).rev() {
            limb_pairs.push((left_limb.clone(), right_limb.clone()));
        }

        let mut groupped_limb_pairs =
            Vec::<(FpGadget<ConstraintF>, FpGadget<ConstraintF>, usize)>::new();

        for (i, limb_pairs_in_a_group) in limb_pairs.chunks(num_limb_in_a_group).enumerate() {
            let mut left_total_limb = zero.clone();
            let mut right_total_limb = zero.clone();

            // For each group `[limb[0],...limb[S-1]]`, where `S = num_limbs_per_group`, 
            // we compute the linear combination
            // ``
            //   group_total = limb[0] * 1 + limb[1] * A + ... limb[S-1] * A^{S-1}`.
            // ``
            // This is done for both left and right operands. 
            // Costs no constraint.
            for (j, ((left_limb, right_limb), shift)) in limb_pairs_in_a_group
                .iter()
                .zip(shift_array.iter())
                .enumerate()
            {
                let left_mul = left_limb
                    .mul_by_constant(cs.ns(|| format!("left_limb * shift {},{}", i, j)), shift)?;
                left_total_limb.add_in_place(
                    cs.ns(|| format!("left_total_limb += left_mul {},{}", i, j)),
                    &left_mul,
                )?;

                let right_mul = right_limb
                    .mul_by_constant(cs.ns(|| format!("right_limb * shift {},{}", i, j)), shift)?;
                right_total_limb.add_in_place(
                    cs.ns(|| format!("right_total_limb += right_mul {},{}", i, j)),
                    &right_mul,
                )?;
            }

            groupped_limb_pairs.push((
                left_total_limb,
                right_total_limb,
                limb_pairs_in_a_group.len(),
            ));
        }

        // The equality of two `A`-ary representations `[L[0],L[1],..]` and `[R[0],R[1],..]` with 
        // oversized limbs is proven by enforcing their *shifted* differences 
        // ``
        //      [L[0] + (- R[0] + shift_constant) , 
        //          L[1] + (- R[1] + shift_constant), 
        //              ..],
        // `` 
        // to represent 
        // ``
        //      Sum_{i>=0} shift_constant * A^i.
        // ``
        // The constant `shift_constant = 2^bits_per_group  - 1` is to circumvent underflows in a
        // length-preserving manner. With this choice  
        // ``
        //     0 <=  shift_constant - R[i] < 2^bits_per_group,
        // `` 
        // and hence
        // ``
        //      L[i] + (shift_constant - R[i]) < 2^{bits_per_group + 1},
        // ``
        // Since the length of the carries are throughout `<= bits_per_limb + surfeit`, 
        // we also have `carry[i-1] + L[i] < 2^bits_per_group`, and the overall sum 
        // ``
        //      carry[i-1] + L[i] + (shift_constant - R[i]) 
        // `` 
        // is still of length `<= bits_per_group + 1`.
        
        // Why carries don't effect the length bound: 
        // Assuming `len(carry) <= bits_per_limb + surfeit`, which is shown in detail below, 
        // `` 
        //   carry + limb[0] + limb[1] * A < 2 * A * 2^limb_size
        // ``
        // and therefore 
        // ``
        //   carry + limb[0] + limb[1] * A + limb[2] * A^2 < 2 * A^2 * 2^limb_size  
        //   ...
        //   carry + limb[0] + limb[1] * A + ... + limb[S-1] * A^{S-1} <
        //                       < 2 * A^{S-1} * 2^limb_size.
        // ``
        // Thus
        // ``
        //   len(carry + L[i]) <= 
        //              limb_size + 1 + (S-1) * len(A) = bits_per_group.
        // `` 

        // The following code is ported from [[Bellman]].
        // [Bellman]: https://github.com/alex-ozdemir/bellman-bignat/blob/master/src/mp/bignat.rs#L567
        let mut carry_in = zero;
        let mut carry_in_value = ConstraintF::zero();
        let mut accumulated_extra = BigUint::zero();
        // The group totals have arity `A^S = 2^{S*shift_per_limb}`.
        for (group_id, (left_total_limb, right_total_limb, num_limb_in_this_group)) in
            groupped_limb_pairs.iter().enumerate()
        {
            // Carry and remainder are subject to the following constraints: 
            // The quotient-remainder constraint
            // ``
            //    carry_in + group_total_left + shift_constant - group_total_right 
            //          == carry * A^S + 0 + (shift_constant % A^S),
            // ``
            // and the length restrictions for the carry
            // ``
            //        len(carry) <= bits_per_limb + surfeit + 2 - shift_per_limb       
            // ``
            // The length bound assures that no modular reduction takes place on both 
            // sides of the quotient-remainder constraint.


            // Why the carries are length bounded by `bits_per_limb + surfeit`: 
            // By the length bound on the group totals, we have 
            // ``
            //      len(carry[i]) <= bits_per_group + 1 - shift_per_limb * S 
            //          =  bits_per_limb + surfeit + 2 - shift_per_limb.
            // `` 
            
            // Computing the shift constant `pad_limb`:
            // ``
            //   shift_constant = 2^bits_per_group - 1
            //      = 2^{bits_per_limb + surfeit + 1 + (S-1) * shift_per_limb} - 1. 
            // ``
            let mut pad_limb_repr: <ConstraintF as PrimeField>::BigInt =
                ConstraintF::one().into_repr();

            pad_limb_repr.muln(
                (bits_per_limb + surfeit
                + (num_limb_in_this_group - 1) * shift_per_limb
                + 1) as u32
                );
            let pad_limb = ConstraintF::from_repr(pad_limb_repr) - ConstraintF::one();

            let left_total_limb_value = left_total_limb.get_value().unwrap_or_default();
            let right_total_limb_value = right_total_limb.get_value().unwrap_or_default();

            let mut carry_value =
                left_total_limb_value + carry_in_value + pad_limb - right_total_limb_value;

            let mut carry_repr = carry_value.into_repr();
            carry_repr.divn((shift_per_limb * num_limb_in_this_group) as u32);

            carry_value = ConstraintF::from_repr(carry_repr);

            // The length restriction of the carry is proven below.
            let carry = FpGadget::<ConstraintF>::alloc(
                cs.ns(|| format!("alloc carry {}", group_id)),
                || Ok(carry_value),
            )?;

            // We add the shift_constant to the accumulator
            accumulated_extra += limbs_to_bigint(bits_per_limb, &[pad_limb]);

            // accumulated_extra = A^S * new_accumulated_extra + remainder, 
            // with remainder < A^S, or equivalently
            let (new_accumulated_extra, remainder) = accumulated_extra.div_rem(
                &BigUint::from(2u64).pow((shift_per_limb * num_limb_in_this_group) as u32),
            );
            let remainder_limb = bigint_to_constraint_field::<ConstraintF>(&remainder);

            // Now we enforce the quotient remainder constraint.
            // ``
            //   left_total_limb + pad_limb + carry_in - right_total_limb
            //      ==  carry * A^S + remainder
            // ``
            let eqn_left = left_total_limb
                .add_constant(
                    cs.ns(|| format!("left_total_limb + pad_limb {}", group_id)),
                    &pad_limb,
                )?
                .add(
                    cs.ns(|| format!("left_total_limb + pad_limb + carry_in {}", group_id)),
                    &carry_in,
                )?
                .sub(
                    cs.ns(|| {
                        format!(
                            "left_total_limb + pad_limb + carry_in - right_total_limb {}",
                            group_id
                        )
                    }),
                    right_total_limb,
                )?;

            let eqn_right = carry
                    .mul_by_constant(
                        cs.ns(|| format!("carry * 2^(shift_per_limb * num_limb_in_this_group) {}", group_id)),
                        &ConstraintF::from(2u64).pow(&[(shift_per_limb * num_limb_in_this_group) as u64])
                    )?
                    .add_constant(
                        cs.ns(|| format!("carry * 2^(shift_per_limb * num_limb_in_this_group) + remainder_limb {}", group_id)),
                        &remainder_limb
                    )?;

            // The constraint
            eqn_left.enforce_equal(
                cs.ns(|| format!("eqn_left == eqn_right {}", group_id)),
                &eqn_right,
            )?;

            accumulated_extra = new_accumulated_extra;
            carry_in = carry.clone();
            carry_in_value = carry_value;

            if group_id == groupped_limb_pairs.len() - 1 {
                // The highest significant group is treated differently:
                // the carry must be equal the accumulated shifts.
                // Costs 1 constraint.
                let accumulated_extra_g = FpGadget::<ConstraintF>::from_value(
                    cs.ns(|| format!("hardcode accumulated_extra {}", group_id)),
                    &bigint_to_constraint_field(&accumulated_extra),
                );
                carry.enforce_equal(
                    cs.ns(|| format!("carry == accumulated_extra {}", group_id)),
                    &accumulated_extra_g,
                )?;
            } else {
                // The length restriction for the carry
                // Costs `bits_per_limb + surfeit + 2 - shift_per_limb` many constraints.
                Reducer::<SimulationF, ConstraintF>::limb_to_bits(
                    cs.ns(|| format!("carry_to_bits_{}", group_id)),
                    &carry,
                    bits_per_limb + surfeit + 2 - shift_per_limb,
                )?;
            }
        }

        Ok(())
    }
}
