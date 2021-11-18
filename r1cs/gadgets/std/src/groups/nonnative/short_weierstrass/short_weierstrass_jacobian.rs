//! The non-native group gadget (for short Weierstrass curves) and implementations of
//!     - the GroupGadget trait,
//! as well as the following auxiliary traits:
//!     - PartialEq, Eq, ToBitsGadget, ToBytesGagdet, EqGadget
//!     - CondSelectGadget, ConstantGadget, AllocGadget.
use algebra::{
    curves::short_weierstrass_jacobian::{
        GroupAffine as SWAffine, GroupProjective as SWProjective,
    },
    AffineCurve, BitIterator, EndoMulParameters, Field, PrimeField, ProjectiveCurve,
    SWModelParameters, SquareRootField,
};

use r1cs_core::{ConstraintSystem, SynthesisError};

use crate::{
    alloc::{AllocGadget, ConstantGadget},
    boolean::Boolean,
    fields::{nonnative::nonnative_field_gadget::NonNativeFieldGadget, FieldGadget},
    groups::{
        check_mul_bits_fixed_base_inputs, check_mul_bits_inputs, EndoMulCurveGadget, GroupGadget,
    },
    prelude::EqGadget,
    select::{CondSelectGadget, TwoBitLookupGadget},
    uint8::UInt8,
    Assignment, ToBitsGadget, ToBytesGadget,
};
use std::{
    borrow::Borrow,
    marker::PhantomData,
    ops::{Add, Mul, Neg},
};

#[derive(Derivative)]
#[derivative(Debug, Clone)]
pub struct GroupAffineNonNativeGadget<
    P: SWModelParameters<BaseField = SimulationF>,
    ConstraintF: PrimeField,
    SimulationF: PrimeField + SquareRootField,
> {
    pub x: NonNativeFieldGadget<SimulationF, ConstraintF>,
    pub y: NonNativeFieldGadget<SimulationF, ConstraintF>,
    pub infinity: Boolean,
    _params: PhantomData<P>,
}

impl<P, ConstraintF, SimulationF> GroupGadget<SWProjective<P>, ConstraintF>
    for GroupAffineNonNativeGadget<P, ConstraintF, SimulationF>
where
    P: SWModelParameters<BaseField = SimulationF>,
    ConstraintF: PrimeField,
    SimulationF: PrimeField + SquareRootField,
{
    type Value = SWProjective<P>;
    type Variable = ();

    fn add<CS: ConstraintSystem<ConstraintF>>(
        &self,
        cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        self.add_internal(cs, other, true)
    }

    #[inline]
    fn zero<CS: ConstraintSystem<ConstraintF>>(mut cs: CS) -> Result<Self, SynthesisError> {
        Ok(Self::new(
            NonNativeFieldGadget::zero(cs.ns(|| "zero"))?,
            NonNativeFieldGadget::one(cs.ns(|| "one"))?,
            Boolean::constant(true),
        ))
    }

    #[inline]
    fn is_zero<CS: ConstraintSystem<ConstraintF>>(&self, _: CS) -> Result<Boolean, SynthesisError> {
        Ok(self.infinity)
    }

    #[inline]
    fn double_in_place<CS: ConstraintSystem<ConstraintF>>(
        &mut self,
        mut cs: CS,
    ) -> Result<(), SynthesisError> {
        let x_squared = self.x.mul_without_reduce(cs.ns(|| "x^2"), &self.x)?;
        //TODO: Once mul_by_constant is implemented properly we can avoid all these adds
        let three_x_squared_plus_a = x_squared
            .add(cs.ns(|| "2x^2"), &x_squared)?
            .add(cs.ns(|| "3x^2"), &x_squared)?
            .add_constant(cs.ns(|| "3x^2 + a"), &P::COEFF_A)?
            .reduce(cs.ns(|| "reduce 3x^2 + a"))?;

        let two_y = self.y.double(cs.ns(|| "2y"))?;

        let lambda = NonNativeFieldGadget::alloc(cs.ns(|| "lambda"), || {
            let y_doubled_inv = NonNativeFieldGadget::get_value(&two_y)
                .get()?
                .inverse()
                .get()?;
            Ok(three_x_squared_plus_a.get_value().get()? * &y_doubled_inv)
        })?;

        // Check lambda
        lambda.mul_equals(cs.ns(|| "check lambda"), &two_y, &three_x_squared_plus_a)?;

        // Allocate fresh x and y as a temporary workaround to reduce the R1CS density.
        let x = NonNativeFieldGadget::alloc(cs.ns(|| "new x"), || {
            let lambda_val = lambda.get_value().get()?;
            let x_val = self.x.get_value().get()?;
            Ok((lambda_val * &lambda_val) - &x_val - &x_val)
        })?;

        // lambda * lambda = new_x + 2_old_x
        let new_x_plus_two_x = self
            .x
            .add(cs.ns(|| "2old_x"), &self.x)?
            .add(cs.ns(|| "new_x + 2old_x"), &x)?;
        lambda.mul_equals(cs.ns(|| "check new x"), &lambda, &new_x_plus_two_x)?;

        let y = NonNativeFieldGadget::alloc(cs.ns(|| "new y"), || {
            let lambda_val = lambda.get_value().get()?;
            let x_val = self.x.get_value().get()?;
            let y_val = self.y.get_value().get()?;
            let new_x_val = x.get_value().get()?;
            Ok(((x_val - &new_x_val) * &lambda_val) - &y_val)
        })?;

        //lambda * (old_x - new_x) = new_y + old_y
        let old_x_minus_new_x = self.x.sub(cs.ns(|| "old_x - new_x"), &x)?;
        let old_y_plus_new_y = self.y.add(cs.ns(|| "old_y + new_y"), &y)?;
        lambda.mul_equals(
            cs.ns(|| "check new y"),
            &old_x_minus_new_x,
            &old_y_plus_new_y,
        )?;

        *self = Self::new(x, y, Boolean::constant(false));
        Ok(())
    }

    fn negate<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<Self, SynthesisError> {
        Ok(Self::new(
            self.x.clone(),
            self.y.negate(cs.ns(|| "negate y"))?,
            self.infinity,
        ))
    }

    /// Incomplete addition: neither `self` nor `other` can be the neutral
    /// element.
    fn add_constant<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &SWProjective<P>,
    ) -> Result<Self, SynthesisError> {
        // lambda = (B.y - A.y)/(B.x - A.x)
        // C.x = lambda^2 - A.x - B.x
        // C.y = lambda(A.x - C.x) - A.y
        //
        // Special cases:
        //
        // doubling: if B.y = A.y and B.x = A.x then lambda is unbound and
        // C = (lambda^2, lambda^3)
        //
        // addition of negative point: if B.y = -A.y and B.x = A.x then no
        // lambda can satisfy the first equation unless B.y - A.y = 0. But
        // then this reduces to doubling.
        //
        // So we need to check that A.x - B.x != 0, which can be done by
        // enforcing I * (B.x - A.x) = 1
        if other.is_zero() {
            return Err(SynthesisError::AssignmentMissing);
        }
        let other = other.into_affine();
        let other_x = other.x;
        let other_y = other.y;

        let x2_minus_x1 = self
            .x
            .sub_constant(cs.ns(|| "x2 - x1"), &other_x)?
            .negate(cs.ns(|| "neg1"))?;
        let y2_minus_y1 = self
            .y
            .sub_constant(cs.ns(|| "y2 - y1"), &other_y)?
            .negate(cs.ns(|| "neg2"))?;

        let inv = x2_minus_x1.inverse(cs.ns(|| "compute inv"))?;

        let lambda = NonNativeFieldGadget::alloc(cs.ns(|| "lambda"), || {
            Ok(y2_minus_y1.get_value().get()? * &inv.get_value().get()?)
        })?;

        let x_3 = NonNativeFieldGadget::alloc(&mut cs.ns(|| "x_3"), || {
            let lambda_val = lambda.get_value().get()?;
            let x1 = self.x.get_value().get()?;
            let x2 = other_x;
            Ok((lambda_val.square() - &x1) - &x2)
        })?;

        let y_3 = NonNativeFieldGadget::alloc(&mut cs.ns(|| "y_3"), || {
            let lambda_val = lambda.get_value().get()?;
            let x_1 = self.x.get_value().get()?;
            let y_1 = self.y.get_value().get()?;
            let x_3 = x_3.get_value().get()?;
            Ok(lambda_val * &(x_1 - &x_3) - &y_1)
        })?;

        // Check lambda
        lambda.mul_equals(cs.ns(|| "check lambda"), &x2_minus_x1, &y2_minus_y1)?;

        // Check x3
        let x3_plus_x1_plus_x2 = x_3
            .add(cs.ns(|| "x3 + x1"), &self.x)?
            .add_constant(cs.ns(|| "x3 + x1 + x2"), &other_x)?;
        lambda.mul_equals(cs.ns(|| "check x3"), &lambda, &x3_plus_x1_plus_x2)?;

        // Check y3
        let y3_plus_y1 = y_3.add(cs.ns(|| "y3 + y1"), &self.y)?;
        let x1_minus_x3 = self.x.sub(cs.ns(|| "x1 - x3"), &x_3)?;

        lambda.mul_equals(cs.ns(|| ""), &x1_minus_x3, &y3_plus_y1)?;

        Ok(Self::new(x_3, y_3, Boolean::Constant(false)))
    }

    /// [Hopwood]'s optimized scalar multiplication, adapted to the general case of no
    /// leading-one assumption.
    /// For a detailed explanation, see the native implementation.
    ///
    /// [Hopwood] https://github.com/zcash/zcash/issues/3924
    fn mul_bits<'a, CS: ConstraintSystem<ConstraintF>>(
        // variable base point, must be non-trivial and in the prime order subgroup
        &self,
        mut cs: CS,
        // little endian, of length <= than the scalar field modulus.
        // Should not be equal to {0, p-2, p-1, p, p+1}.
        bits: impl Iterator<Item = &'a Boolean>,
    ) -> Result<Self, SynthesisError> {
        assert!(P::ScalarField::size_in_bits() >= 3);

        let double_and_add_step = |mut cs: r1cs_core::Namespace<_, _>,
                                   bit: &Boolean,
                                   acc: &mut Self,
                                   t: &Self,
                                   safe_arithmetics: bool|
         -> Result<(), SynthesisError> {
            // Q := k[i+1] ? T : −T
            let neg_y = t.y.negate(cs.ns(|| "neg y"))?;
            let selected_y = NonNativeFieldGadget::conditionally_select(
                cs.ns(|| "select y or -y"),
                bit,
                &t.y,
                &neg_y,
            )?;
            let q = Self::new(t.x.clone(), selected_y, t.infinity);

            // Acc := (Acc + Q) + Acc using double_and_add_internal at 5 constraints
            *acc = acc.double_and_add_internal(cs.ns(|| "double and add"), &q, safe_arithmetics)?;

            Ok(())
        };

        let mut bits = bits.cloned().collect::<Vec<Boolean>>();
        if self.get_value().is_some() && bits.iter().all(|b| b.get_value().is_some()) {
            check_mul_bits_inputs(
                &self.get_value().unwrap(),
                bits.iter().map(|b| b.get_value().unwrap()).collect(),
            )?;
        }

        // Length normalization by adding the scalar field modulus.
        // The result is alway n + 1 bits long, although the leading bit might be zero.
        // Costs ~ 1*n + O(1) many constraints.
        bits = crate::groups::scalar_bits_to_constant_length::<_, P::ScalarField, _>(
            cs.ns(|| "scalar bits to constant length"),
            bits,
        )?;

        let t = self.clone();

        // Acc := [3] T = [2]*T + T
        let init = {
            let mut t_copy = t.clone();
            t_copy.double_in_place(cs.ns(|| "[2] * T"))?;
            t_copy.add_unsafe(cs.ns(|| "[3] * T"), &t)
        }?;

        /* Separate treatment of the two leading bits.
         */

        // This processes the most significant bit for the case
        // bits[n]=1.
        let mut acc = init.clone();
        let leading_bit = bits.pop().unwrap();

        // Processing bits[n-1] for the case bits[n] = 1
        double_and_add_step(
            cs.ns(|| "Processing bits[n-1] for the case bits[n] == 1"),
            &bits.pop().unwrap(),
            &mut acc,
            &t,
            false,
        )?;

        // If leading_bit is one we reset acc to the case bits[n-1]==1
        acc = Self::conditionally_select(
            cs.ns(|| "reset acc if leading_bit == 1"),
            &leading_bit,
            &acc,
            &init,
        )?;

        /* The next bits bits[n-2],...,bits[3] (i.e. except the three least significant)
        are treated as in Hopwoods' algorithm.
        */

        for (i, bit) in bits
            .iter()
            .enumerate()
            // Skip the three least significant bits (we handle them after the loop)
            .skip(3)
            // Scan over the scalar bits in big-endian order
            .rev()
        {
            double_and_add_step(cs.ns(|| format!("bit {}", i + 2)), bit, &mut acc, &t, false)?;
        }

        /* The last three bits are treated using secure arithmetics
         */

        double_and_add_step(cs.ns(|| "bit 2"), &bits[2], &mut acc, &t, true)?;

        double_and_add_step(cs.ns(|| "bit 1"), &bits[1], &mut acc, &t, true)?;

        // See native implementation why add_unsafe is fine here
        // return (k[0] = 0) ? (Acc - T) : Acc
        let neg_t = t.negate(cs.ns(|| "neg T"))?;
        let acc_minus_t = acc.add_unsafe(cs.ns(|| "Acc - T"), &neg_t)?;

        let result = Self::conditionally_select(
            cs.ns(|| "select acc or acc - T"),
            &bits[0],
            &acc,
            &acc_minus_t,
        )?;

        Ok(result)
    }

    /// The non-native variant of Hopwoods fixed base scalar mul.
    /// CAUTION: Due to the use of incomplete arithemtics, there are few exceptions
    /// described in `fn check_mul_bits_fixed_base_inputs()`.
    #[inline]
    fn mul_bits_fixed_base<'a, CS: ConstraintSystem<ConstraintF>>(
        base: &'a SWProjective<P>,
        mut cs: CS,
        bits: &[Boolean],
    ) -> Result<Self, SynthesisError> {
        // bits must not exceed the length the scalar field modulus
        if bits.len() > P::ScalarField::size_in_bits() {
            return Err(SynthesisError::Other(format!(
                "Input bits size: {}, max allowed size: {}",
                bits.len(),
                P::ScalarField::size_in_bits()
            )));
        }

        // After padding to the next multiple of two we compute
        //
        //  acc = sum_{i=0}^{m-1} ((2*b_{2i+1} + b_i) - 3/2) * 4^i * T
        //      = sum_{i=0}^{m-1} (2*(2*b_{2i+1} + b_i) - 3) * 4^i * T',
        //
        // with T' = 1/2 T, and then correct the result by substracting
        //  - 3* sum_{i=0}^{m-1} * 4^i * T' = -3* (4^m -1) * T'.
        // This signed representation with digits from the symmetric
        // set {-3,-1,+1,+3} allows to use add_unsafe in a controlled
        // way.

        // Init
        let mut to_sub = SWProjective::<P>::zero();

        // T = 2^{-1} * base
        let mut t = {
            let two_inv = P::ScalarField::one().double().inverse().unwrap();
            (*base).mul(&two_inv)
        };

        // Init to 0 to avoid compilation errors ("usage of possibily uninitialized variable").
        // The 0 val will never be used and acc will be initialized to proper value in the first
        // iteration of the loop below.
        let mut acc = Self::zero(cs.ns(|| "initialize acc"))?;

        // Pad bits with 0s if not even
        let mut bits = bits.to_vec();
        if bits.len() % 2 != 0 {
            bits.push(Boolean::constant(false));
        }

        // Pre-checks
        if bits.iter().all(|b| b.get_value().is_some()) {
            check_mul_bits_fixed_base_inputs(
                base,
                bits.iter().rev().map(|b| b.get_value().unwrap()).collect(),
            )?;
        };

        let num_chunks = bits.len() / 2;

        for (i, bits) in bits.chunks(2).enumerate() {
            // Compute table for this chunk
            let ti = t;
            let three_ti = ti.double().add(&ti);
            let mut table = [three_ti.neg(), ti.neg(), ti, three_ti];

            //Compute constants
            SWProjective::batch_normalization(&mut table);
            let x_coords = [table[0].x, table[1].x, table[2].x, table[3].x];
            let y_coords = [table[0].y, table[1].y, table[2].y, table[3].y];
            let precomp = Boolean::and(cs.ns(|| format!("b0 AND b1_{}", i)), &bits[0], &bits[1])?;

            //Lookup x and y
            let x = NonNativeFieldGadget::two_bit_lookup_lc(
                cs.ns(|| format!("Lookup x_{}", i)),
                &precomp,
                &[bits[0], bits[1]],
                &x_coords,
            )?;
            let y = NonNativeFieldGadget::two_bit_lookup_lc(
                cs.ns(|| format!("Lookup y_{}", i)),
                &precomp,
                &[bits[0], bits[1]],
                &y_coords,
            )?;

            // Add the value computed in this chunk to the accumulator
            match i {
                // First chunk -> initialize acc
                chunk if chunk == 0 => {
                    acc = Self::new(x, y, Boolean::constant(false));
                }

                // We can use unsafe add, no exception occur
                chunk if chunk < num_chunks => {
                    let adder: Self = Self::new(x, y, Boolean::constant(false));
                    acc = acc.add_unsafe(cs.ns(|| format!("Add_{}", i)), &adder)?;
                }

                // Last chunk we must use safe add
                _ => {
                    let adder: Self = Self::new(x, y, Boolean::constant(false));
                    acc = acc.add(cs.ns(|| format!("Add_{}", i)), &adder)?;
                }
            }

            // Update values for next chunk
            t = t.double().double();
            to_sub += &table[0];
        }
        acc = acc.sub_constant(cs.ns(|| "acc - to_sub"), &to_sub)?;
        Ok(acc)
    }

    fn get_value(&self) -> Option<<Self as GroupGadget<SWProjective<P>, ConstraintF>>::Value> {
        match (
            self.x.get_value(),
            self.y.get_value(),
            self.infinity.get_value(),
        ) {
            (Some(x), Some(y), Some(infinity)) => {
                Some(SWAffine::<P>::new(x, y, infinity).into_projective())
            }
            (None, None, None) => None,
            _ => unreachable!(),
        }
    }

    fn get_variable(&self) -> Self::Variable {
        unimplemented!()
    }

    fn cost_of_add() -> usize {
        unimplemented!()
    }

    fn cost_of_double() -> usize {
        unimplemented!()
    }
}

impl<P, ConstraintF, SimulationF> EndoMulCurveGadget<SWProjective<P>, ConstraintF>
    for GroupAffineNonNativeGadget<P, ConstraintF, SimulationF>
where
    P: EndoMulParameters<BaseField = SimulationF>,
    ConstraintF: PrimeField,
    SimulationF: PrimeField + SquareRootField,
{
    /// Given an arbitrary curve element `&self`, applies the endomorphism
    /// defined by `ENDO_COEFF`.
    fn apply_endomorphism<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<Self, SynthesisError> {
        Ok(Self::new(
            self.x.mul_by_constant(cs.ns(|| "endo x"), &P::ENDO_COEFF)?,
            self.y.clone(),
            self.infinity,
        ))
    }

    /// The endomorphism-based scalar multiplication circuit from [Halo] in non-native
    /// arithmetics. Assumes that `ENDO_SCALAR` satisfies the minimal distance property as
    /// mentioned in `SWModelParameters`.
    /// Given any non-trivial point `P= &self` of the prime order r subgroup, and a slice
    /// of an even number of at most `lambda` Booleans `bits`, enforces that the result equals
    ///     `phi(bits) * P`,
    /// where `phi(bits)` is the equivalent scalar representation of `bits`.
    ///
    /// [Halo]: https://eprint.iacr.org/2019/1021
    fn endo_mul<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        bits: &[Boolean],
    ) -> Result<Self, SynthesisError> {
        let mut bits = bits.to_vec();
        if bits.len() % 2 == 1 {
            bits.push(Boolean::constant(false));
        }

        if bits.len() > P::LAMBDA {
            Err(SynthesisError::Other(
                "Endo mul bits length exceeds LAMBDA".to_owned(),
            ))?
        }

        let endo_self = self.apply_endomorphism(cs.ns(|| "endo self"))?;
        let self_y_neg = self.y.negate(cs.ns(|| "self y negate"))?;

        let mut acc = endo_self.clone();
        acc = acc.add(cs.ns(|| "add"), &self)?;
        acc.double_in_place(cs.ns(|| "double"))?;

        for i in (0..(bits.len() / 2)).rev() {
            // Conditional select between (-1)^b_0 * Phi^{b_1}(&self), according
            // to [b_1,b_0] = bits[2i+1, 2i].
            // Takes 2 constraints.
            let add = Self::new(
                NonNativeFieldGadget::conditionally_select(
                    cs.ns(|| format!("conditional bit1 select endo {}", i)),
                    &bits[i * 2 + 1],
                    &endo_self.x,
                    &self.x,
                )?,
                NonNativeFieldGadget::conditionally_select(
                    cs.ns(|| format!("conditional bit0 select negate {}", i)),
                    &bits[i * 2],
                    &self.y,
                    &self_y_neg,
                )?,
                self.infinity,
            );

            // The unsafe double and add, takes 5 constraints.
            acc = acc.double_and_add_unsafe(cs.ns(|| format!("double_and_add {}", i)), &add)?;
        }

        Ok(acc)
    }
}

impl<P, ConstraintF, SimulationF> PartialEq
    for GroupAffineNonNativeGadget<P, ConstraintF, SimulationF>
where
    P: SWModelParameters<BaseField = SimulationF>,
    ConstraintF: PrimeField,
    SimulationF: PrimeField + SquareRootField,
{
    fn eq(&self, other: &Self) -> bool {
        self.x == other.x && self.y == other.y
    }
}

impl<P, ConstraintF, SimulationF> Eq for GroupAffineNonNativeGadget<P, ConstraintF, SimulationF>
where
    P: SWModelParameters<BaseField = SimulationF>,
    ConstraintF: PrimeField,
    SimulationF: PrimeField + SquareRootField,
{
}

impl<P, ConstraintF, SimulationF> ToBitsGadget<ConstraintF>
    for GroupAffineNonNativeGadget<P, ConstraintF, SimulationF>
where
    P: SWModelParameters<BaseField = SimulationF>,
    ConstraintF: PrimeField,
    SimulationF: PrimeField + SquareRootField,
{
    fn to_bits<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        let mut x_bits = self.x.to_bits(&mut cs.ns(|| "X Coordinate To Bits"))?;
        let y_bits = self.y.to_bits(&mut cs.ns(|| "Y Coordinate To Bits"))?;
        x_bits.extend_from_slice(&y_bits);
        x_bits.push(self.infinity);
        Ok(x_bits)
    }

    fn to_bits_strict<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        let mut x_bits = self
            .x
            .to_bits_strict(&mut cs.ns(|| "X Coordinate To Bits"))?;
        let y_bits = self
            .y
            .to_bits_strict(&mut cs.ns(|| "Y Coordinate To Bits"))?;
        x_bits.extend_from_slice(&y_bits);
        x_bits.push(self.infinity);

        Ok(x_bits)
    }
}

impl<P, ConstraintF, SimulationF> ToBytesGadget<ConstraintF>
    for GroupAffineNonNativeGadget<P, ConstraintF, SimulationF>
where
    P: SWModelParameters<BaseField = SimulationF>,
    ConstraintF: PrimeField,
    SimulationF: PrimeField + SquareRootField,
{
    fn to_bytes<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        let mut x_bytes = self.x.to_bytes(&mut cs.ns(|| "X Coordinate To Bytes"))?;
        let y_bytes = self.y.to_bytes(&mut cs.ns(|| "Y Coordinate To Bytes"))?;
        let inf_bytes = self.infinity.to_bytes(&mut cs.ns(|| "Infinity to Bytes"))?;
        x_bytes.extend_from_slice(&y_bytes);
        x_bytes.extend_from_slice(&inf_bytes);
        Ok(x_bytes)
    }

    fn to_bytes_strict<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        let mut x_bytes = self
            .x
            .to_bytes_strict(&mut cs.ns(|| "X Coordinate To Bytes"))?;
        let y_bytes = self
            .y
            .to_bytes_strict(&mut cs.ns(|| "Y Coordinate To Bytes"))?;
        let inf_bytes = self.infinity.to_bytes(&mut cs.ns(|| "Infinity to Bytes"))?;
        x_bytes.extend_from_slice(&y_bytes);
        x_bytes.extend_from_slice(&inf_bytes);

        Ok(x_bytes)
    }
}

impl<P, ConstraintF, SimulationF> EqGadget<ConstraintF>
    for GroupAffineNonNativeGadget<P, ConstraintF, SimulationF>
where
    P: SWModelParameters<BaseField = SimulationF>,
    ConstraintF: PrimeField,
    SimulationF: PrimeField + SquareRootField,
{
    fn is_eq<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Boolean, SynthesisError> {
        let b0 = self.x.is_eq(cs.ns(|| "x"), &other.x)?;
        let b1 = self.y.is_eq(cs.ns(|| "y"), &other.y)?;
        let coordinates_equal = Boolean::and(cs.ns(|| "x AND y"), &b0, &b1)?;
        let both_are_zero = Boolean::and(
            cs.ns(|| "self.infinity AND other.infinity"),
            &self.infinity,
            &other.infinity,
        )?;
        Boolean::or(
            cs.ns(|| "coordinates_equal OR both_are_zero"),
            &coordinates_equal,
            &both_are_zero,
        )
    }

    #[inline]
    fn conditional_enforce_equal<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
        should_enforce: &Boolean,
    ) -> Result<(), SynthesisError> {
        self.is_eq(cs.ns(|| "is_eq(self, other)"), &other)?
            .conditional_enforce_equal(
                cs.ns(|| "enforce condition"),
                &Boolean::constant(true),
                &should_enforce,
            )?;
        Ok(())
    }

    #[inline]
    fn conditional_enforce_not_equal<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
        should_enforce: &Boolean,
    ) -> Result<(), SynthesisError> {
        let is_equal = self.is_eq(cs.ns(|| "is_eq(self, other)"), other)?;
        Boolean::and(
            cs.ns(|| "is_equal AND should_enforce"),
            &is_equal,
            should_enforce,
        )?
        .enforce_equal(
            cs.ns(|| "is_equal AND should_enforce == false"),
            &Boolean::Constant(false),
        )
    }
}

impl<P, ConstraintF, SimulationF> GroupAffineNonNativeGadget<P, ConstraintF, SimulationF>
where
    P: SWModelParameters<BaseField = SimulationF>,
    ConstraintF: PrimeField,
    SimulationF: PrimeField + SquareRootField,
{
    pub fn new(
        x: NonNativeFieldGadget<SimulationF, ConstraintF>,
        y: NonNativeFieldGadget<SimulationF, ConstraintF>,
        infinity: Boolean,
    ) -> Self {
        Self {
            x,
            y,
            infinity,
            _params: PhantomData,
        }
    }

    #[inline]
    /// Incomplete addition: neither `self` nor `other` can be the neutral
    /// element, and other != ±self.
    /// If `safe` is set, enforce in the circuit exceptional cases not occurring.
    fn add_internal<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
        safe: bool,
    ) -> Result<Self, SynthesisError> {
        // lambda = (B.y - A.y)/(B.x - A.x)
        // C.x = lambda^2 - A.x - B.x
        // C.y = lambda(A.x - C.x) - A.y
        //
        // Special cases:
        //
        // doubling: if B.y = A.y and B.x = A.x then lambda is unbound and
        // C = (lambda^2, lambda^3)
        //
        // addition of negative point: if B.y = -A.y and B.x = A.x then no
        // lambda can satisfy the first equation unless B.y - A.y = 0. But
        // then this reduces to doubling.
        let x2_minus_x1 = other.x.sub(cs.ns(|| "x2 - x1"), &self.x)?;
        let y2_minus_y1 = other.y.sub(cs.ns(|| "y2 - y1"), &self.y)?;

        let lambda = if safe {
            // Check that A.x - B.x != 0, which can be done by
            // enforcing I * (B.x - A.x) = 1
            // This is done below when we calculate inv (by NonNativeFieldGadget::inverse)
            let inv = x2_minus_x1.inverse(cs.ns(|| "compute inv"))?;
            NonNativeFieldGadget::alloc(cs.ns(|| "lambda"), || {
                Ok(y2_minus_y1.get_value().get()? * &inv.get_value().get()?)
            })
        } else {
            NonNativeFieldGadget::alloc(cs.ns(|| "lambda"), || {
                Ok(y2_minus_y1.get_value().get()?
                    * &x2_minus_x1.get_value().get()?.inverse().get()?)
            })
        }?;

        let x_3 = NonNativeFieldGadget::alloc(&mut cs.ns(|| "x_3"), || {
            let lambda_val = lambda.get_value().get()?;
            let x1 = self.x.get_value().get()?;
            let x2 = other.x.get_value().get()?;
            Ok((lambda_val.square() - &x1) - &x2)
        })?;

        let y_3 = NonNativeFieldGadget::alloc(&mut cs.ns(|| "y_3"), || {
            let lambda_val = lambda.get_value().get()?;
            let x_1 = self.x.get_value().get()?;
            let y_1 = self.y.get_value().get()?;
            let x_3 = x_3.get_value().get()?;
            Ok(lambda_val * &(x_1 - &x_3) - &y_1)
        })?;

        // Check lambda
        lambda.mul_equals(cs.ns(|| "check lambda"), &x2_minus_x1, &y2_minus_y1)?;

        // Check x3
        let x3_plus_x1_plus_x2 = x_3
            .add(cs.ns(|| "x3 + x1"), &self.x)?
            .add(cs.ns(|| "x3 + x1 + x2"), &other.x)?;
        lambda.mul_equals(cs.ns(|| "check x3"), &lambda, &x3_plus_x1_plus_x2)?;

        // Check y3
        let y3_plus_y1 = y_3.add(cs.ns(|| "y3 + y1"), &self.y)?;
        let x1_minus_x3 = self.x.sub(cs.ns(|| "x1 - x3"), &x_3)?;
        lambda.mul_equals(cs.ns(|| ""), &x1_minus_x3, &y3_plus_y1)?;

        Ok(Self::new(x_3, y_3, Boolean::Constant(false)))
    }

    #[inline]
    /// Incomplete, unsafe, addition: neither `self` nor `other` can be the neutral
    /// element, and other != ±self.
    pub fn add_unsafe<CS: ConstraintSystem<ConstraintF>>(
        &self,
        cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        self.add_internal(cs, other, false)
    }

    #[inline]
    /// Compute 2 * self + other as (self + other) + self: this requires less constraints
    /// than computing self.double().add(other).
    /// Incomplete add: neither `self` nor `other` can be the neutral element, and other != ±self;
    /// If `safe` is set, enforce in the circuit that exceptional cases not occurring.
    fn double_and_add_internal<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
        safe: bool,
    ) -> Result<Self, SynthesisError> {
        // Hopwood's optimized double-and-add sum P_4 = P_3 + P_1, where P_3 = P_1 + P_2.
        // Under the above presumptions on P_1 and P_2 can be enforced by just 5
        // constraints
        //      1. (x2 - x1) * lambda_1 = y2 - y1;
        //      2. lambda_1^2 = x1 +  x2 + x3;
        //      3. (x1 - x3) * (lambda1 + lambda_2) = 2·y1
        //      4. lambda_2^2 =   x1 + x3 + x4;
        //      5. lambda_2 * (x1 - x4) = y_1 + y_4;
        // Note that 3. is the result of adding the two equations
        //      3a. (x_1 - x_3) * lambda_1 = y_1 + y_3
        //      3b. (x_1 - x_3) * lambda_2 = y_1 - y_3.
        // This reduction is valid as x_2 - x_1 is non-zero and hence 1. uniquely
        // determines lambda_1, and thus x3 is determined by 2.
        // Again, since x_1-x_3 is non-zero equation 3. uniquely determines lambda_2
        // and hence being of the same unique value as enforced by 3a. and 3b.
        let x2_minus_x1 = other.x.sub(cs.ns(|| "x2 - x1"), &self.x)?;
        let y2_minus_y1 = other.y.sub(cs.ns(|| "y2 - y1"), &self.y)?;

        // Allocate lambda_1
        let lambda_1 = if safe {
            // Enforce the extra constraint for x_2 - x_1 != 0 by using the inverse gadget
            let inv_1 = x2_minus_x1.inverse(cs.ns(|| "enforce inv 1"))?;
            NonNativeFieldGadget::alloc(cs.ns(|| "lambda_1"), || {
                Ok(y2_minus_y1.get_value().get()? * &inv_1.get_value().get()?)
            })
        } else {
            // By our presumptions, x_2 - x_1 != 0
            NonNativeFieldGadget::alloc(cs.ns(|| "lambda_1"), || {
                Ok(y2_minus_y1.get_value().get()?
                    * &x2_minus_x1.get_value().get()?.inverse().get()?)
            })
        }?;

        // Constraint 1.
        lambda_1.mul_equals(cs.ns(|| "check lambda_1"), &x2_minus_x1, &y2_minus_y1)?;

        let x_3 = NonNativeFieldGadget::alloc(&mut cs.ns(|| "x_3"), || {
            let lambda_1_val = lambda_1.get_value().get()?;
            let x1 = self.x.get_value().get()?;
            let x2 = other.x.get_value().get()?;
            Ok((lambda_1_val.square() - &x1) - &x2)
        })?;

        // Constraint 2.
        let x3_plus_x1_plus_x2 = x_3
            .add(cs.ns(|| "x3 + x1"), &self.x)?
            .add(cs.ns(|| "x3 + x1 + x2"), &other.x)?;
        lambda_1.mul_equals(cs.ns(|| "check x3"), &lambda_1, &x3_plus_x1_plus_x2)?;

        // Allocate lambda_2.
        let x1_minus_x3 = &self.x.sub(cs.ns(|| "x1 - x3"), &x_3)?;
        let two_y1 = self.y.double(cs.ns(|| "2y1"))?;

        let lambda_2 = if safe {
            // Set the extra constraint for x_1 - x_3 != 0
            let inv_2 = x1_minus_x3.inverse(cs.ns(|| "enforce inv 2"))?;
            NonNativeFieldGadget::alloc(cs.ns(|| "lambda_2"), || {
                let lambda_val = lambda_1.get_value().get()?;
                let two_y1_val = two_y1.get_value().get()?;

                let two_y1_div_x1_minus_x3 = two_y1_val * &inv_2.get_value().get()?;
                Ok(two_y1_div_x1_minus_x3 - &lambda_val)
            })
        } else {
            NonNativeFieldGadget::alloc(cs.ns(|| "lambda_2"), || {
                let lambda_val = lambda_1.get_value().get()?;
                let two_y1_val = two_y1.get_value().get()?;

                let x1_minus_x3_inv = (x1_minus_x3.get_value().get()?).inverse().get()?;
                let two_y1_div_x1_minus_x3 = two_y1_val * &x1_minus_x3_inv;
                Ok(two_y1_div_x1_minus_x3 - &lambda_val)
            })
        }?;

        // Constraint 3.
        let lambda_2_plus_lambda_1 = lambda_2.add(cs.ns(|| "lambda_2 + lambda_1"), &lambda_1)?;

        lambda_2_plus_lambda_1.mul_equals(
            cs.ns(|| "(lambda_2 + lambda) * (x1 - x3) = 2y1"),
            &x1_minus_x3,
            &two_y1,
        )?;

        // Allocate the final x
        let x_4 = NonNativeFieldGadget::alloc(&mut cs.ns(|| "x_4"), || {
            let lambda_2_val = lambda_2.get_value().get()?;
            let x1_val = self.x.get_value().get()?;
            let x3_val = x_3.get_value().get()?;
            Ok((lambda_2_val.square() - &x1_val) - &x3_val)
        })?;

        // Constraint 4.
        let x4_plus_x1_plus_x3 = x_4
            .add(cs.ns(|| "x4 + x1"), &self.x)?
            .add(cs.ns(|| "x3 + x1 + x3"), &x_3)?;
        lambda_2.mul_equals(cs.ns(|| "check x4"), &lambda_2, &x4_plus_x1_plus_x3)?;

        // alloc the final y
        let y_4 = NonNativeFieldGadget::alloc(&mut cs.ns(|| "y_4"), || {
            let lambda_2_val = lambda_2.get_value().get()?;
            let x_1_val = self.x.get_value().get()?;
            let y_1_val = self.y.get_value().get()?;
            let x_4_val = x_4.get_value().get()?;
            Ok(lambda_2_val * &(x_1_val - &x_4_val) - &y_1_val)
        })?;

        // Constraint 5.
        let y4_plus_y1 = y_4.add(cs.ns(|| "y4 + y1"), &self.y)?;
        let x1_minus_x4 = self.x.sub(cs.ns(|| "x1 - x4"), &x_4)?;
        lambda_2.mul_equals(cs.ns(|| ""), &x1_minus_x4, &y4_plus_y1)?;

        Ok(Self::new(x_4, y_4, Boolean::Constant(false)))
    }

    #[inline]
    /// Compute 2 * self + other.
    /// Incomplete, safe, addition: neither `self` nor `other` can be the neutral
    /// element, and other != ±self.
    pub fn double_and_add<CS: ConstraintSystem<ConstraintF>>(
        &self,
        cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        self.double_and_add_internal(cs, other, true)
    }

    #[inline]
    /// Compute 2 * self + other.
    /// Incomplete, unsafe, addition: neither `self` nor `other` can be the neutral
    /// element, and other != ±self.
    pub fn double_and_add_unsafe<CS: ConstraintSystem<ConstraintF>>(
        &self,
        cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        self.double_and_add_internal(cs, other, false)
    }
}

impl<P, ConstraintF, SimulationF> CondSelectGadget<ConstraintF>
    for GroupAffineNonNativeGadget<P, ConstraintF, SimulationF>
where
    P: SWModelParameters<BaseField = SimulationF>,
    ConstraintF: PrimeField,
    SimulationF: PrimeField + SquareRootField,
{
    #[inline]
    fn conditionally_select<CS: ConstraintSystem<ConstraintF>>(
        mut cs: CS,
        cond: &Boolean,
        first: &Self,
        second: &Self,
    ) -> Result<Self, SynthesisError> {
        let x = NonNativeFieldGadget::conditionally_select(
            &mut cs.ns(|| "x"),
            cond,
            &first.x,
            &second.x,
        )?;
        let y = NonNativeFieldGadget::conditionally_select(
            &mut cs.ns(|| "y"),
            cond,
            &first.y,
            &second.y,
        )?;
        let infinity = Boolean::conditionally_select(
            &mut cs.ns(|| "infinity"),
            cond,
            &first.infinity,
            &second.infinity,
        )?;

        Ok(Self::new(x, y, infinity))
    }

    fn cost() -> usize {
        2 * <NonNativeFieldGadget<SimulationF, ConstraintF> as CondSelectGadget<ConstraintF>>::cost(
        ) + <Boolean as CondSelectGadget<ConstraintF>>::cost()
    }
}

impl<P, ConstraintF, SimulationF> ConstantGadget<SWProjective<P>, ConstraintF>
    for GroupAffineNonNativeGadget<P, ConstraintF, SimulationF>
where
    P: SWModelParameters<BaseField = SimulationF>,
    ConstraintF: PrimeField,
    SimulationF: PrimeField + SquareRootField,
{
    fn from_value<CS: ConstraintSystem<ConstraintF>>(mut cs: CS, value: &SWProjective<P>) -> Self {
        let value = value.into_affine();
        let x = NonNativeFieldGadget::from_value(cs.ns(|| "hardcode x"), &value.x);
        let y = NonNativeFieldGadget::from_value(cs.ns(|| "hardcode y"), &value.y);
        let infinity = Boolean::constant(value.infinity);

        Self::new(x, y, infinity)
    }

    fn get_constant(&self) -> SWProjective<P> {
        let value_proj = SWAffine::<P>::new(
            self.x.get_value().unwrap(),
            self.y.get_value().unwrap(),
            self.infinity.get_value().unwrap(),
        )
        .into_projective();
        let x = value_proj.x;
        let y = value_proj.y;
        let z = value_proj.z;
        SWProjective::<P>::new(x, y, z)
    }
}

impl<P, ConstraintF, SimulationF> AllocGadget<SWProjective<P>, ConstraintF>
    for GroupAffineNonNativeGadget<P, ConstraintF, SimulationF>
where
    P: SWModelParameters<BaseField = SimulationF>,
    ConstraintF: PrimeField,
    SimulationF: PrimeField + SquareRootField,
{
    #[inline]
    fn alloc<FN, T, CS: ConstraintSystem<ConstraintF>>(
        mut cs: CS,
        value_gen: FN,
    ) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<SWProjective<P>>,
    {
        let (x, y, infinity) = match value_gen() {
            Ok(ge) => {
                let ge = ge.borrow().into_affine();
                (Ok(ge.x), Ok(ge.y), Ok(ge.infinity))
            }
            _ => (
                Err(SynthesisError::AssignmentMissing),
                Err(SynthesisError::AssignmentMissing),
                Err(SynthesisError::AssignmentMissing),
            ),
        };

        // Perform on-curve check.
        let b = P::COEFF_B;
        let a = P::COEFF_A;

        let x = NonNativeFieldGadget::alloc(&mut cs.ns(|| "x"), || x)?;
        let y = NonNativeFieldGadget::alloc(&mut cs.ns(|| "y"), || y)?;
        let infinity = Boolean::alloc(&mut cs.ns(|| "infinity"), || infinity)?;

        // Check that y^2 = x^3 + ax +b
        // We do this by checking that y^2 - b = x * (x^2 +a)
        let x2 = x.mul_without_reduce(cs.ns(|| "x^2"), &x)?;
        let y2 = y.mul_without_reduce(cs.ns(|| "y^2"), &y)?;

        let x2_plus_a = x2
            .add_constant(cs.ns(|| "x^2 + a"), &a)?
            .reduce(cs.ns(|| "reduce(x^2 + a)"))?;
        let y2_minus_b = y2
            .add_constant(cs.ns(|| "y^2 - b"), &b.neg())?
            .reduce(cs.ns(|| "reduce(y^2 - b)"))?;

        let x2_plus_a_times_x = x2_plus_a.mul(cs.ns(|| "(x^2 + a)*x"), &x)?;

        x2_plus_a_times_x.conditional_enforce_equal(
            cs.ns(|| "on curve check"),
            &y2_minus_b,
            &infinity.not(),
        )?;

        Ok(Self::new(x, y, infinity))
    }

    #[inline]
    fn alloc_without_check<FN, T, CS: ConstraintSystem<ConstraintF>>(
        mut cs: CS,
        value_gen: FN,
    ) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<SWProjective<P>>,
    {
        let (x, y, infinity) = match value_gen() {
            Ok(ge) => {
                let ge = ge.borrow().into_affine();
                (Ok(ge.x), Ok(ge.y), Ok(ge.infinity))
            }
            _ => (
                Err(SynthesisError::AssignmentMissing),
                Err(SynthesisError::AssignmentMissing),
                Err(SynthesisError::AssignmentMissing),
            ),
        };

        let x = NonNativeFieldGadget::alloc(&mut cs.ns(|| "x"), || x)?;
        let y = NonNativeFieldGadget::alloc(&mut cs.ns(|| "y"), || y)?;
        let infinity = Boolean::alloc(&mut cs.ns(|| "infinity"), || infinity)?;

        Ok(Self::new(x, y, infinity))
    }

    #[inline]
    fn alloc_checked<FN, T, CS: ConstraintSystem<ConstraintF>>(
        mut cs: CS,
        value_gen: FN,
    ) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<SWProjective<P>>,
    {
        let alloc_and_prime_order_check =
            |mut cs: r1cs_core::Namespace<_, _>, value_gen: FN| -> Result<Self, SynthesisError> {
                let cofactor_weight = BitIterator::new(P::COFACTOR).filter(|b| *b).count();
                // If we multiply by r, we actually multiply by r - 2.
                let r_minus_1 = (-P::ScalarField::one()).into_repr();
                let r_weight = BitIterator::new(&r_minus_1).filter(|b| *b).count();

                // If the Hamming weight of th cofactor is less than the Hamming weight of
                // the scalar field modulus, then we enforce subgroup membership of `result` by
                // result = COFACTOR * ge of a suitable computed groupelement ge.
                // Otherwise we simply enforce that -result == (r-1) * result.
                if cofactor_weight < r_weight {
                    let ge = Self::alloc(cs.ns(|| "Alloc checked"), || {
                        value_gen().map(|ge| {
                            ge.borrow()
                                .into_affine()
                                .mul_by_cofactor_inv()
                                .into_projective()
                        })
                    })?;
                    let mut seen_one = false;
                    let mut result = Self::zero(cs.ns(|| "result"))?;
                    for (i, b) in BitIterator::new(P::COFACTOR).enumerate() {
                        let mut cs = cs.ns(|| format!("Iteration {}", i));
                        let old_seen_one = seen_one;
                        if seen_one {
                            result.double_in_place(cs.ns(|| "Double"))?;
                        } else {
                            seen_one = b;
                        }
                        if b {
                            result = if old_seen_one {
                                result.add(cs.ns(|| "Add"), &ge)?
                            } else {
                                ge.clone()
                            };
                        }
                    }
                    Ok(result)
                } else {
                    let ge = Self::alloc(cs.ns(|| "Alloc checked"), value_gen)?;
                    let mut seen_one = false;
                    let mut result = Self::zero(cs.ns(|| "result"))?;
                    // Returns bits in big-endian order
                    for (i, b) in BitIterator::new(r_minus_1).enumerate() {
                        let mut cs = cs.ns(|| format!("Iteration {}", i));
                        let old_seen_one = seen_one;
                        if seen_one {
                            result.double_in_place(cs.ns(|| "Double"))?;
                        } else {
                            seen_one = b;
                        }
                        if b {
                            result = if old_seen_one {
                                result.add(cs.ns(|| "Add"), &ge)?
                            } else {
                                ge.clone()
                            };
                        }
                    }
                    let neg_ge = ge.negate(cs.ns(|| "Negate ge"))?;
                    neg_ge.enforce_equal(cs.ns(|| "Check equals"), &result)?;
                    Ok(ge)
                }
            };
        let ge = alloc_and_prime_order_check(cs.ns(|| "alloc and prime order check"), value_gen)?;

        Ok(ge)
    }

    #[inline]
    fn alloc_input<FN, T, CS: ConstraintSystem<ConstraintF>>(
        mut cs: CS,
        value_gen: FN,
    ) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<SWProjective<P>>,
    {
        let (x, y, infinity) = match value_gen() {
            Ok(ge) => {
                let ge = ge.borrow().into_affine();
                (Ok(ge.x), Ok(ge.y), Ok(ge.infinity))
            }
            _ => (
                Err(SynthesisError::AssignmentMissing),
                Err(SynthesisError::AssignmentMissing),
                Err(SynthesisError::AssignmentMissing),
            ),
        };

        let x = NonNativeFieldGadget::alloc_input(&mut cs.ns(|| "x"), || x)?;
        let y = NonNativeFieldGadget::alloc_input(&mut cs.ns(|| "y"), || y)?;
        let infinity = Boolean::alloc_input(&mut cs.ns(|| "infinity"), || infinity)?;

        Ok(Self::new(x, y, infinity))
    }
}
