use crate::{
    boolean::Boolean,
    fields::fp::FpGadget,
    prelude::*,
    ToBitsGadget,
};
use algebra::PrimeField;
use r1cs_core::{ConstraintSystem, SynthesisError};
use core::cmp::Ordering;

impl<F: PrimeField> FpGadget<F> {
    /// This function enforces the ordering between `self` and `other`. The
    /// constraint system will not be satisfied otherwise. If `self` should
    /// also be checked for equality, e.g. `self <= other` instead of `self <
    /// other`, set `should_also_check_quality` to `true`. This variant
    /// verifies `self` and `other` are `<= (p-1)/2`.
    pub fn enforce_cmp<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        other: &FpGadget<F>,
        ordering: Ordering,
        should_also_check_equality: bool,
    ) -> Result<(), SynthesisError> {
        let (left, right) = self.process_cmp_inputs(cs.ns(|| "process cmp inputs"), other, ordering, should_also_check_equality)?;
        left.enforce_smaller_than(cs.ns(|| "enforce smaller"), &right)
    }

    /// This function enforces the ordering between `self` and `other`. The
    /// constraint system will not be satisfied otherwise. If `self` should
    /// also be checked for equality, e.g. `self <= other` instead of `self <
    /// other`, set `should_also_check_quality` to `true`. This variant
    /// assumes `self` and `other` are `<= (p-1)/2` and does not generate
    /// constraints to verify that.
    pub fn enforce_cmp_unchecked<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        other: &FpGadget<F>,
        ordering: Ordering,
        should_also_check_equality: bool,
    ) -> Result<(), SynthesisError> {
        let (left, right) = self.process_cmp_inputs(cs.ns(|| "process cmp inputs"), other, ordering, should_also_check_equality)?;
        left.enforce_smaller_than_unchecked(cs.ns(|| "enforce smaller"), &right)
    }

    /// This function checks the ordering between `self` and `other`. It outputs
    /// self `Boolean` that contains the result - `1` if true, `0`
    /// otherwise. The constraint system will be satisfied in any case. If
    /// `self` should also be checked for equality, e.g. `self <= other`
    /// instead of `self < other`, set `should_also_check_quality` to
    /// `true`. This variant verifies `self` and `other` are `<= (p-1)/2`.
    pub fn is_cmp<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        other: &FpGadget<F>,
        ordering: Ordering,
        should_also_check_equality: bool,
    ) -> Result<Boolean, SynthesisError> {
        let (left, right) = self.process_cmp_inputs(cs.ns(|| "process cmp inputs"), other, ordering, should_also_check_equality)?;
        left.is_smaller_than(cs.ns(|| "is smaller"), &right)
    }

    /// This function checks the ordering between `self` and `other`. It outputs
    /// a `Boolean` that contains the result - `1` if true, `0` otherwise.
    /// The constraint system will be satisfied in any case. If `self`
    /// should also be checked for equality, e.g. `self <= other` instead of
    /// `self < other`, set `should_also_check_quality` to `true`. This
    /// variant assumes `self` and `other` are `<= (p-1)/2` and does not
    /// generate constraints to verify that.
    pub fn is_cmp_unchecked<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        other: &FpGadget<F>,
        ordering: Ordering,
        should_also_check_equality: bool,
    ) -> Result<Boolean, SynthesisError> {
        let (left, right) = self.process_cmp_inputs(cs.ns(|| "process cmp inputs"), other, ordering, should_also_check_equality)?;
        left.is_smaller_than_unchecked(cs.ns(|| "is smaller"), &right)
    }

    fn process_cmp_inputs<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        other: &Self,
        ordering: Ordering,
        should_also_check_equality: bool,
    ) -> Result<(Self, Self), SynthesisError> {
        let (left, right) = match ordering {
            Ordering::Less => (self, other),
            Ordering::Greater => (other, self),
            Ordering::Equal => return Err(SynthesisError::Unsatisfiable),
        };
        let one = FpGadget::<F>::from_value(cs.ns(|| "from value"), &F::one());
        let right_for_check = if should_also_check_equality {
            right.add(cs.ns(|| "add"),&one)?
        } else {
            right.clone()
        };

        Ok((left.clone(), right_for_check))
    }

    /// Helper function to enforce that `self <= (p-1)/2`.
    pub fn enforce_smaller_or_equal_than_mod_minus_one_div_two<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
    ) -> Result<(), SynthesisError> {
        // It's okay to use `to_non_unique_bits` bits here because we're enforcing
        // self <= (p-1)/2, which implies self < p.
        let bits_be = self.to_bits(cs.ns(|| "to bits"))?;
        let bits_le = bits_be.into_iter().rev().collect::<Vec<_>>();
        let _ = Boolean::enforce_smaller_or_equal_than_le(
            cs.ns(|| "enforce smaller or equal"), 
            &bits_le,
            &F::modulus_minus_one_div_two(),
        )?;
        Ok(())
    }

    /// Helper function to check `self < other` and output a result bit. This
    /// function verifies `self` and `other` are `<= (p-1)/2`.
    fn is_smaller_than<CS: ConstraintSystem<F>>(&self, mut cs: CS, other: &FpGadget<F>) -> Result<Boolean, SynthesisError> {
        self.enforce_smaller_or_equal_than_mod_minus_one_div_two(cs.ns(|| "self smaller or equal mod"))?;
        other.enforce_smaller_or_equal_than_mod_minus_one_div_two(cs.ns(|| "other smaller or equal mod"))?;
        self.is_smaller_than_unchecked(cs.ns(|| "is smaller unchecked"), other)
    }

    /// Helper function to check `self < other` and output a result bit. This
    /// function assumes `self` and `other` are `<= (p-1)/2` and does not
    /// generate constraints to verify that.
    // Note that `len((p-1)/2) = len(p) - 1 = CAPACITY`.
    fn is_smaller_than_unchecked<CS: ConstraintSystem<F>>(&self, mut cs: CS, other: &FpGadget<F>) -> Result<Boolean, SynthesisError> {
        // Since `a = self` and `b = other` are from `[0, (p-1)/2]`, we know that 
        // ``
        //      self - other
        // ``
        // is from the range `[-(p-1)/2, (p-1)/2]`, where this range has no overlap
        // due to modular reduction.  Hence
        //
        // ``
        //      0 <= 2 * (self - other) <= (p-1),
        // ``
        // and the least significant bit of `2 * (self - other) mod p` is zero. 
        // Otherwise, if `self < other`, then 
        // ``
        //      2 * (self - other) mod p =  2 * (self - other) + p
        // ``
        // which is a positive odd number, having least significant bit equal to `1`.
        // To assure the right decision we need to return the least significant
        // bit of the NATIVE bit representation of `2 * (self - other)`. Hence we 
        // need to use `to_bits_strict()`.
        Ok(self.sub(cs.ns(|| "sub"), other)?
            .double(cs.ns(|| "double"))?
            .to_bits_strict(cs.ns(|| "to bits"))? // returns big endian
            .into_iter().rev().collect::<Vec<_>>() 
            .first() 
            .unwrap()
            .clone())
    }

    /// Helper function to enforce `self < other`. This function verifies `self`
    /// and `other` are `<= (p-1)/2`.
    fn enforce_smaller_than<CS: ConstraintSystem<F>>(&self, mut cs: CS, other: &FpGadget<F>) -> Result<(), SynthesisError> {
        self.enforce_smaller_or_equal_than_mod_minus_one_div_two(cs.ns(|| "self smaller or equal mod"))?;
        other.enforce_smaller_or_equal_than_mod_minus_one_div_two(cs.ns(|| "other smaller or equal mod"))?;
        self.enforce_smaller_than_unchecked(cs.ns(|| "enforce smaller unchecked"), other)
    }

    /// Helper function to enforce `self < other`. This function assumes `self`
    /// and `other` are `<= (p-1)/2` and does not generate constraints to
    /// verify that.
    fn enforce_smaller_than_unchecked<CS: ConstraintSystem<F>>(&self, mut cs: CS, other: &FpGadget<F>) -> Result<(), SynthesisError> {
        let is_smaller_than = self.is_smaller_than_unchecked(cs.ns(|| "is smaller"), other)?;
        //println!("{} Is smaller then {}: {}", self.get_value().unwrap(), other.get_value().unwrap(), is_smaller_than.get_value().unwrap());
        let lc_one = CS::one();
        cs.enforce(
            || "Enforce smaller then",
            |lc| lc + is_smaller_than.lc(CS::one(), F::one()),
            |lc| lc + lc_one.clone(),
            |lc| lc + lc_one
        );
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use std::cmp::Ordering;
    use rand::{Rng, thread_rng};

    use r1cs_core::ConstraintSystem;
    use crate::{algebra::{UniformRand, PrimeField, 
        fields::bls12_381::Fr,
    }, fields::fp::FpGadget, test_constraint_system::TestConstraintSystem};
    use crate::alloc::AllocGadget;

    #[test]
    fn test_cmp() {
        let mut rng = &mut thread_rng();
        fn rand_in_range<R: Rng>(rng: &mut R) -> Fr {
            let pminusonedivtwo: Fr = Fr::modulus_minus_one_div_two().into();
            let mut r;
            loop {
                r = Fr::rand(rng);
                if r <= pminusonedivtwo {
                    break;
                }
            }
            r
        }
        for i in 0..10 {
            let mut cs = TestConstraintSystem::<Fr>::new();

            let a = rand_in_range(&mut rng);
            let a_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_a"), || Ok(a)).unwrap();
            let b = rand_in_range(&mut rng);
            let b_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_b"), || Ok(b)).unwrap();

            match a.cmp(&b) {
                Ordering::Less => {
                    a_var.enforce_cmp(cs.ns(|| "enforce less"), &b_var, Ordering::Less, false).unwrap();
                    a_var.enforce_cmp(cs.ns(|| "enforce less equal"), &b_var, Ordering::Less, true).unwrap();
                }
                Ordering::Greater => {
                    a_var.enforce_cmp(cs.ns(|| "enforce greater"), &b_var, Ordering::Greater, false).unwrap();
                    a_var.enforce_cmp(cs.ns(|| "enforce greater equal"), &b_var, Ordering::Greater, true).unwrap();
                }
                _ => {}
            }

            if i == 0 {
                println!("number of constraints: {}", cs.num_constraints());
            }
            if !cs.is_satisfied(){
                println!("{:?}", cs.which_is_unsatisfied());
            }
            assert!(cs.is_satisfied());
        }
        println!("Finished with satisfaction tests");

        for _i in 0..10 {
            let mut cs = TestConstraintSystem::<Fr>::new();
            let a = rand_in_range(&mut rng);
            let a_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_a"), || Ok(a)).unwrap();
            let b = rand_in_range(&mut rng);
            let b_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_b"), || Ok(b)).unwrap();

            match b.cmp(&a) {
                Ordering::Less => {
                    a_var.enforce_cmp(cs.ns(|| "enforce less"), &b_var, Ordering::Less, false).unwrap();
                    a_var.enforce_cmp(cs.ns(|| "enforce less equal"),&b_var, Ordering::Less, true).unwrap();
                }
                Ordering::Greater => {
                    a_var.enforce_cmp(cs.ns(|| "enforce greater"),&b_var, Ordering::Greater, false).unwrap();
                    a_var.enforce_cmp(cs.ns(|| "enforce greater equal"),&b_var, Ordering::Greater, true).unwrap();
                }
                _ => {}
            }
            assert!(!cs.is_satisfied());
        }

        for _i in 0..10 {
            let mut cs = TestConstraintSystem::<Fr>::new();
            let a = rand_in_range(&mut rng);
            let a_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_a"), || Ok(a)).unwrap();
            a_var.enforce_cmp(cs.ns(|| "enforce less"),&a_var, Ordering::Less, false).unwrap();

            assert!(!cs.is_satisfied());
        }

        for _i in 0..10 {
            let mut cs = TestConstraintSystem::<Fr>::new();
            let a = rand_in_range(&mut rng);
            let a_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_a"), || Ok(a)).unwrap();
            a_var.enforce_cmp(cs.ns(|| "enforce less"),&a_var, Ordering::Less, true).unwrap();
            if !cs.is_satisfied(){
                println!("{:?}", cs.which_is_unsatisfied());
            }
            assert!(cs.is_satisfied());
        }
    }
}