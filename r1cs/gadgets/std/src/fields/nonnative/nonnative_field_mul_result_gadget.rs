use crate::{
    ceil_log_2,
    fields::{
        fp::FpGadget,
        nonnative::{
            nonnative_field_gadget::{
                bigint_to_constraint_field, limbs_to_bigint, NonNativeFieldGadget,
            },
            params::{get_params, get_params_for_generic_field, get_params_for_pseudomersenne},
            reduce::Reducer,
        },
    },
    prelude::*,
    FromGadget,
};
use algebra::fields::{FpParameters, PrimeField};
use num_bigint::BigUint;
use num_traits::{One, Pow};
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use std::{marker::PhantomData, vec::Vec};

#[derive(Debug)]
#[must_use]
/// The gadget for the non-reduced products of `NonNativeFieldGadget`s.
pub struct NonNativeFieldMulResultGadget<SimulationF: PrimeField, ConstraintF: PrimeField> {
    /// Limbs of the product representation, starting with the most significant limb.
    /// Normal form corresponds to the limb sizes
    /// ``
    ///     bits_per_limb[i] = 2 * NonNativeFieldParams::bits_per_limb,
    /// ``
    /// for all except the most significant limb, for which
    /// ``
    ///     bits_per_limb[0] = 2 * (SimulationF::size_in_bits()
    ///      - (NonNativeFieldParams::numlimbs - 1) * NonNativeFieldParams::bits_per_limb)
    /// ``
    pub limbs: Vec<FpGadget<ConstraintF>>,
    /// As `num_add_over_normal_form` for `NonNativeGadget`s, keeps track of the limb
    /// size bound
    /// ``
    ///     limbs[i] < (prod_of_num_additions + 1) * 2^bits_per_limb[i].
    /// ``
    pub num_add_over_normal_form: BigUint,
    #[doc(hidden)]
    pub simulation_phantom: PhantomData<SimulationF>,
}

impl<SimulationF: PrimeField, ConstraintF: PrimeField>
    FromGadget<&NonNativeFieldGadget<SimulationF, ConstraintF>, ConstraintF>
    for NonNativeFieldMulResultGadget<SimulationF, ConstraintF>
{
    fn from<CS: ConstraintSystemAbstract<ConstraintF>>(
        other: &NonNativeFieldGadget<SimulationF, ConstraintF>,
        cs: CS,
    ) -> Result<Self, SynthesisError> {
        debug_assert!(
            other.check(),
            "mul result gagdet from non native gadget: check() failed on input gadget"
        );

        let params = get_params::<SimulationF, ConstraintF>();

        let mut limbs = other.limbs.clone();
        limbs.reverse();
        limbs.resize(2 * params.num_limbs - 1, FpGadget::<ConstraintF>::zero(cs)?);
        limbs.reverse();

        // set num_add to ceil((input_gadget.num_add+1)/2^bits_per_limb)-1 as a limb of
        // NonNativeFieldMulResultGadget has 2*bits_per_limb for each limb
        let num_add_over_normal_form = (&other.num_of_additions_over_normal_form
            + BigUint::from(2usize).pow(params.bits_per_limb as u32))
            / BigUint::from(2usize).pow(params.bits_per_limb as u32)
            - BigUint::one();

        let result = Self {
            limbs,
            num_add_over_normal_form,
            simulation_phantom: PhantomData,
        };

        debug_assert!(
            result.check(),
            "mul result gagdet from non native gadget: check() failed on result"
        );

        Ok(result)
    }
}

impl<SimulationF: PrimeField, ConstraintF: PrimeField>
    NonNativeFieldMulResultGadget<SimulationF, ConstraintF>
{
    /// A function for test purposes. Returns `true` if `&self.num_add` respects
    /// the capacity bound, and bounds all the limbs correctly.
    pub(crate) fn check(&self) -> bool {
        let params = get_params::<SimulationF, ConstraintF>();

        let valid_num_limbs = self.limbs.len() == 2 * params.num_limbs - 1;

        let normal_form_bound = Pow::pow(BigUint::from(2usize), &(2 * params.bits_per_limb));
        let normal_form_bound_ms = Pow::pow(
            BigUint::from(2u64),
            &(2 * (SimulationF::size_in_bits() - (params.num_limbs - 1) * params.bits_per_limb)),
        );
        let num_add_plus_one = BigUint::one() + &self.num_add_over_normal_form;
        let limb_bound = normal_form_bound * &num_add_plus_one;
        let limb_bound_ms = normal_form_bound_ms * &num_add_plus_one;

        let valid_num_adds = 2 * params.bits_per_limb + ceil_log_2!(num_add_plus_one)
            <= ConstraintF::size_in_bits() - 1;

        // k-ary and of the limb checks.
        let valid_limbs = self.limbs.iter().enumerate().all(|(i, limb)| {
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

    /// Get the value of the multiplication result
    pub fn value(&self) -> Result<SimulationF, SynthesisError> {
        let params = get_params::<SimulationF, ConstraintF>();

        let p_representations =
            NonNativeFieldGadget::<SimulationF, ConstraintF>::get_limbs_representations_from_big_integer(
                &<SimulationF as PrimeField>::Params::MODULUS
            )?;
        let p_bigint = limbs_to_bigint(params.bits_per_limb, &p_representations);

        let mut limbs_values = Vec::<ConstraintF>::new();
        for limb in self.limbs.iter() {
            limbs_values.push(limb.get_value().unwrap_or_default());
        }
        let value_bigint = limbs_to_bigint(params.bits_per_limb, &limbs_values);

        let res = bigint_to_constraint_field::<SimulationF>(&(value_bigint % p_bigint));
        Ok(res)
    }

    /// Reducing a NonNativeMulResultGadget back to a non-native field gadget
    /// in normal form for a non pseudo-mersenne field.
    /// Assumes that
    /// ``
    ///     2 * bits_per_limb + surfeit' <= CAPACITY - 2.
    /// ``
    /// where
    /// ``
    ///     bits_per_limb = NonNativeFieldParams::bits_per_limb,
    ///     surfeit' =  log(num_limbs + 2*(num_adds + 1)),
    ///     num_limbs = NonNativeFieldParams::num_limbs,
    /// ``
    /// and `num_adds` is as in the NonNativeMulResultGadget.
    // Costs
    // ``
    //     C =  len(p) + surfeit'
    //          + len(p) + num_limbs^2
    //          +  (num_groups - 1) * (3 + bits_per_limb + surfeit') + 1
    // ``
    // constraints, with `num_groups = Ceil(len(p) / S)` and
    // ``
    //  S - 1 = Floor[
    //          (ConstraintF::CAPACITY - 2 - (2 * bits_per_limb + surfeit') / bits_per_limb
    //      ]
    //        = Floor[
    //          (ConstraintF::CAPACITY - 2 - surfeit') / bits_per_limb
    //      ] - 2.
    // ``
    pub(crate) fn reduce_for_generic_field<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<NonNativeFieldGadget<SimulationF, ConstraintF>, SynthesisError> {
        debug_assert!(
            self.check(),
            "reduce(): check() failed on input mul result gadget"
        );
        let params =
            get_params_for_generic_field(SimulationF::size_in_bits(), ConstraintF::size_in_bits());
        // This is just paraphrasing the reduction of non-natives. We enforce the large integer
        // equality
        // ``
        //    Sum_{i=0..} limb[i] * A^i = k * p + r,
        // ``
        // where `0 <= r < 2^len(p)` and `k >= 0`, by means of `group_and_check_equality()`.
        // As the left hand side is length bounded by
        // ``
        //   Sum_{i=0..} limb[i] * A^i < (num_adds + 1) * 2^{2*len(p)}
        // ``
        // the quotient `k` is length bounded by
        // ``
        //      len(k) <= len(p) + log(num_adds + 1) + 1.
        // ``

        // Note: To assure that the limb-wise computation of the `k * p + r` does not
        // exceed the capacity bound, we demand
        // ``
        //     2 * bits_per_limb + surfeit'  <= CAPACITY,
        // ``
        // with `surfeit' = log(num_limbs + 2*(num_adds + 1))`.
        // However, as the final `group_and_check_equality()` panics iff
        // ``
        //     2 * bits_per_limb + surfeit' > CAPACITY - 2.
        // ``
        // there is no need to throw an error here.

        // Step 1: get p
        let p_representations =
            NonNativeFieldGadget::<SimulationF, ConstraintF>::get_limbs_representations_from_big_integer(
                &<SimulationF as PrimeField>::Params::MODULUS,
            )?;
        let p_bigint = limbs_to_bigint(params.bits_per_limb, &p_representations);

        // Step 2: compute surfeit
        let surfeit = ceil_log_2!(BigUint::one() + &self.num_add_over_normal_form);

        // Step 3: allocate k,
        // Costs `C = len(p) + surfeit + 1` constraints.
        let k_bits = {
            let mut res = Vec::new();

            let mut limbs_values = Vec::<ConstraintF>::new();
            for limb in self.limbs.iter() {
                limbs_values.push(limb.get_value().unwrap_or_default());
            }

            let value_bigint = limbs_to_bigint(params.bits_per_limb, &limbs_values);
            let mut k_cur = value_bigint / p_bigint; // drops the remainder

            // The total length of k
            let total_len = SimulationF::size_in_bits() + surfeit + 1;

            for i in 0..total_len {
                res.push(Boolean::alloc(
                    cs.ns(|| format!("alloc k bit {}", i)),
                    || Ok(&k_cur % 2u64 == BigUint::from(1u64)),
                )?);
                k_cur /= 2u64; // drops the remainder
            }
            res
        };

        // We define the non-native gadget of `k` by using exactly `num_limbs`
        // limbs, having all limbs except the most significant one in normal form.
        let k_limbs = {
            let zero = FpGadget::zero(cs.ns(|| "hardcode zero for k_limbs"))?;
            let mut limbs = Vec::new();

            let mut k_bits_cur = k_bits.clone();

            for i in 0..params.num_limbs {
                let this_limb_size = if i != params.num_limbs - 1 {
                    params.bits_per_limb
                } else {
                    // The most significant limb is oversized by
                    // `surfeit = log(num_adds + 1) + 1`
                    k_bits.len() - (params.num_limbs - 1) * params.bits_per_limb
                };

                let this_limb_bits = k_bits_cur[0..this_limb_size].to_vec();
                k_bits_cur = k_bits_cur[this_limb_size..].to_vec();

                let mut limb = zero.clone();
                let mut cur = ConstraintF::one();

                for (j, bit) in this_limb_bits.iter().enumerate() {
                    limb = limb.conditionally_add_constant(
                        cs.ns(|| format!("add bit {} for limb {}", j, i)),
                        bit,
                        cur,
                    )?;
                    cur.double_in_place();
                }
                limbs.push(limb);
            }

            limbs.reverse();
            limbs
        };

        // TODO: let us remove the declaration of `num_adds` as it is not used
        // anyway.
        // ``
        //      k <= x/p < (num_adds + 1)*2^{2len(p)} / p
        //               <= 2*(num_adds + 1)*2^len(p).
        // ``
        // Hence we may set `num_adds(k) = 2 * num_adds + 1`
        let k_gadget = NonNativeFieldGadget::<SimulationF, ConstraintF> {
            limbs: k_limbs,
            num_of_additions_over_normal_form: BigUint::from(2u32)
                * self.num_add_over_normal_form.clone()
                + BigUint::one(),
            simulation_phantom: PhantomData,
        };

        // alloc r in normal form.
        // Costs `C = len(p) + num_limbs` constraints.
        let r_gadget =
            NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(cs.ns(|| "alloc r"), || {
                self.value()
            })?;

        // Compute the product representation for `k*p`
        // Costs no constraints.
        let mut prod_limbs = Vec::new();
        let zero = FpGadget::<ConstraintF>::zero(cs.ns(|| "hardcode zero for step 1"))?;

        for _ in 0..2 * params.num_limbs - 1 {
            prod_limbs.push(zero.clone());
        }

        for i in 0..params.num_limbs {
            for j in 0..params.num_limbs {
                let mul_result = k_gadget.limbs[j].mul_by_constant(
                    cs.ns(|| format!("mul_result = p_limbs[{}] * k_gadget.limbs[{}]", i, j)),
                    &p_representations[i],
                )?;
                prod_limbs[i + j] = prod_limbs[i + j].add(
                    cs.ns(|| {
                        format!(
                            "prod_limbs[{},{}] = prod_limbs[{},{}] + mul_result",
                            i, j, i, j
                        )
                    }),
                    &mul_result,
                )?;
            }
        }

        // Compute the limbs of `k * p + r`. Does not cost any constraint.
        // TODO: Let us remove the `num_adds` declaration, as it is not used anyway.
        // The `k*p + r` limbs are bounded by
        // ``
        //      (k * p + r)[i] <= (num_limbs - 1 + 2*(num_add + 1))* 2^{2*bits_per_limb[i]}
        //                      + 2^bits_per_limb[i]
        //                      <= (num_limbs + 2*(num_add + 1)) * 2^{2*bits_per_limb[i]}.
        // ``
        // Hence we may set num_adds and surfeit for the limbs of `k*p + r` according
        // to
        // ``
        //      num_adds(kp + r) = num_limbs + 2*num_adds + 1,
        //      surfeit(kp + r) = log(num_limbs + 2*(num_adds + 1)).
        // ``
        let mut kp_plus_r_gadget = Self {
            limbs: prod_limbs,
            num_add_over_normal_form: BigUint::from(params.num_limbs)
                + k_gadget.num_of_additions_over_normal_form,
            simulation_phantom: PhantomData,
        };
        let surfeit_kp_plus_r =
            ceil_log_2!(kp_plus_r_gadget.num_add_over_normal_form + BigUint::one());

        let kp_plus_r_limbs_len = kp_plus_r_gadget.limbs.len();
        for (i, limb) in r_gadget.limbs.iter().rev().enumerate() {
            kp_plus_r_gadget.limbs[kp_plus_r_limbs_len - 1 - i].add_in_place(
                cs.ns(|| {
                    format!(
                        "kp_plus_r_gadget.limbs[{}] + r_gadget.limbs_rev[{}]",
                        kp_plus_r_limbs_len - 1 - i,
                        i
                    )
                }),
                limb,
            )?;
        }

        // Assumes that
        // ``
        //     2 * bits_per_limb + surfeit' <= CAPACITY - 2,
        // ``
        // where `surfeit' = surfeit(kp + r) = log(num_limbs + 2*num_adds + 2)`.
        // Costs
        // ``
        //      (num_groups - 1) * (1 + 2*bits_per_limb + surfeit' + 2 - bits_per_limb) + 2
        // ``
        // constraints, where `num_groups = Ceil[num_limbs / S]`, and
        // ``
        //  S - 1 = Floor[
        //          (ConstraintF::CAPACITY - 2 - (2 * bits_per_limb + surfeit') / bits_per_limb
        //      ]
        //        = Floor[
        //          (ConstraintF::CAPACITY - 2 - surfeit') / bits_per_limb
        //      ] - 2.
        // ``
        Reducer::<SimulationF, ConstraintF>::group_and_check_equality(
            cs.ns(|| "group and check equality"),
            surfeit_kp_plus_r,
            // bits_per_limb
            2 * params.bits_per_limb,
            // shift_per_limb
            params.bits_per_limb,
            &self.limbs,
            &kp_plus_r_gadget.limbs,
        )?;

        Ok(r_gadget)
    }

    /// Reducing a NonNativeMulResultGadget back to a non-native field gadget
    /// in normal form.
    pub fn reduce<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<NonNativeFieldGadget<SimulationF, ConstraintF>, SynthesisError> {
        if super::is_pseudo_mersenne::<SimulationF>() {
            let params = get_params_for_pseudomersenne(
                SimulationF::size_in_bits(),
                ConstraintF::size_in_bits(),
                SimulationF::Params::DIFFERENCE_WITH_HIGHER_POWER_OF_TWO.unwrap(),
            );
            // in this case the first num_limbs-1 limbs should be the constant zero
            for i in 0..params.num_limbs - 1 {
                assert_eq!(self.limbs[i].get_value().unwrap(), ConstraintF::zero())
            }
            // So we can safely convert the `num_limbs` least significant limbs to a NonNativeFieldGadget
            // and then employ the more efficient reduce operation
            let limbs = self.limbs[params.num_limbs - 1..].iter().cloned().collect();
            // num_add of the NonNativeFieldGadget is 2^bits_per_limb times higher than the num_add of
            // NonNativeFieldMulResultGadget, as the limbs in normal form are bits_per_limb smaller
            let num_of_additions_over_normal_form = (&self.num_add_over_normal_form
                + BigUint::one())
                * BigUint::from(2usize).pow(params.bits_per_limb as u32)
                - BigUint::one();
            let mut result = NonNativeFieldGadget {
                limbs,
                num_of_additions_over_normal_form,
                simulation_phantom: PhantomData,
            };
            Reducer::reduce(&mut cs, &mut result)?;
            return Ok(result);
        } else {
            return self.reduce_for_generic_field(&mut cs);
        }
    }

    /// Add unreduced elements.
    pub fn add<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        debug_assert!(
            self.check() && other.check(),
            "add():: check() failed on input mul result gadgets"
        );

        let mut new_limbs = Vec::new();

        for (i, (l1, l2)) in self.limbs.iter().zip(other.limbs.iter()).enumerate() {
            let new_limb = l1.add(cs.ns(|| format!("l1_{} + l2_{}", i, i)), l2)?;
            new_limbs.push(new_limb);
        }

        Ok(Self {
            limbs: new_limbs,
            num_add_over_normal_form: &self.num_add_over_normal_form
                + &other.num_add_over_normal_form,
            simulation_phantom: PhantomData,
        })
    }

    /// Add native constant elem
    pub fn add_constant<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &SimulationF,
    ) -> Result<Self, SynthesisError> {
        debug_assert!(
            self.check(),
            "add_constant(): check() failed on input mul result gadgets"
        );

        let mut other_limbs =
            NonNativeFieldGadget::<SimulationF, ConstraintF>::get_limbs_representations(other)?;
        other_limbs.reverse();

        let mut new_limbs = Vec::new();

        for (i, limb) in self.limbs.iter().rev().enumerate() {
            if i < other_limbs.len() {
                let new_limb = limb.add_constant(
                    cs.ns(|| format!("limb_{} + other_limb_{}", i, i)),
                    &other_limbs[i],
                )?;
                new_limbs.push(new_limb);
            } else {
                new_limbs.push((*limb).clone());
            }
        }

        new_limbs.reverse();

        Ok(Self {
            limbs: new_limbs,
            num_add_over_normal_form: BigUint::one() + &self.num_add_over_normal_form,
            simulation_phantom: PhantomData,
        })
    }
}
