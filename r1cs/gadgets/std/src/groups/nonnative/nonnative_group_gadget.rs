//! The non-native group gadget (for short Weierstrass curves) and implementations of 
//!     - the GroupGadget trait,
//! as well as the following auxiliary traits:
//!     - PartialEq, Eq, ToBitsGadget, ToBytesGagdet, EqGadget
//!     - CondSelectGadget, ConstantGadget, AllocGadget.
use algebra::{
    AffineCurve, BitIterator, Field, PrimeField, ProjectiveCurve, SWModelParameters,
    SquareRootField, UniformRand,
    curves::short_weierstrass_jacobian::{GroupAffine as SWAffine, GroupProjective as SWProjective}};

use r1cs_core::{ConstraintSystem, SynthesisError};

use crate::{Assignment, ToBitsGadget, ToBytesGadget, alloc::{AllocGadget, ConstantGadget}, boolean::Boolean, fields::{FieldGadget, nonnative::nonnative_field_gadget::NonNativeFieldGadget}, groups::GroupGadget, prelude::EqGadget, select::{CondSelectGadget, TwoBitLookupGadget}, uint8::UInt8};
use std::{borrow::Borrow, marker::PhantomData};
use rand::rngs::OsRng;

#[derive(Derivative)]
#[derivative(Debug, Clone)]
pub struct GroupAffineNonNativeGadget<
    P: SWModelParameters<BaseField = SimulationF>,
    ConstraintF: PrimeField,
    SimulationF: PrimeField + SquareRootField
> {
    pub x:   NonNativeFieldGadget<SimulationF, ConstraintF>,
    pub y:   NonNativeFieldGadget<SimulationF, ConstraintF>,
    pub infinity:   Boolean,
    _params: PhantomData<P>,
}


impl<P, ConstraintF, SimulationF> GroupGadget<SWProjective<P>, ConstraintF>
for GroupAffineNonNativeGadget<P, ConstraintF, SimulationF>
    where
        P: SWModelParameters<BaseField = SimulationF>,
        ConstraintF: PrimeField,
        SimulationF: PrimeField + SquareRootField
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
    fn is_zero<CS: ConstraintSystem<ConstraintF>>(&self, _: CS) -> Result<Boolean, SynthesisError>{
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
            let y_doubled_inv = NonNativeFieldGadget::get_value(&two_y).get()?.inverse().get()?;
            Ok(three_x_squared_plus_a.get_value().get()? * &y_doubled_inv)
        })?;

        // Check lambda
        lambda.mul_equals(cs.ns(|| "check lambda"), &two_y, &three_x_squared_plus_a)?;

        // Allocate fresh x and y as a temporary workaround to reduce the R1CS density.
        // TODO: Let us check if the constraints from non-native arithmetics
        //       already stop the propagation of LCs
        let x = NonNativeFieldGadget::alloc(
            cs.ns(|| "new x"),
            || {
                let lambda_val = lambda.get_value().get()?;
                let x_val = self.x.get_value().get()?;
                Ok((lambda_val * &lambda_val) - &x_val - &x_val)
            }
        )?;

        // lambda * lambda = new_x + 2_old_x
        let new_x_plus_two_x = self.x
            .add(cs.ns(|| "2old_x"), &self.x)?
            .add(cs.ns(|| "new_x + 2old_x"), &x)?;
        lambda.mul_equals(cs.ns(|| "check new x"), &lambda, &new_x_plus_two_x)?;

        let y = NonNativeFieldGadget::alloc(
            cs.ns(|| "new y"),
            || {
                let lambda_val = lambda.get_value().get()?;
                let x_val = self.x.get_value().get()?;
                let y_val = self.y.get_value().get()?;
                let new_x_val = x.get_value().get()?;
                Ok(((x_val - &new_x_val) * &lambda_val) - &y_val)
            }
        )?;

        //lambda * (old_x - new_x) = new_y + old_y
        let old_x_minus_new_x = self.x
            .sub(cs.ns(|| "old_x - new_x"), &x)?;
        let old_y_plus_new_y = self.y
            .add(cs.ns(|| "old_y + new_y"), &y)?;
        lambda.mul_equals(cs.ns(|| "check new y"), &old_x_minus_new_x, &old_y_plus_new_y)?;

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
            self.infinity
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

    /// Variable base exponentiation, avoiding exceptional cases due to incomplete additions.
    /// Inputs must be specified in *little-endian* form.
    /// From https://github.com/zcash/zcash/issues/3924
    /// Implementation adapted from https://github.com/ebfull/halo/blob/master/src/gadgets/ecc.rs#L1762
    ///
    /// Goal: [bits] self = [2^n + k] T
    ///
    /// Acc := [3] T
    /// for i from n-2 down to 0 {
    ///     Q := k[i+1] ? T : −T
    ///     Acc := (Acc + Q) + Acc
    /// }
    /// return (k[0] = 0) ? (Acc - T) : Acc
    fn mul_bits<'a, CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        bits: impl Iterator<Item = &'a Boolean>,
    ) -> Result<Self, SynthesisError> {

        let bits = bits.cloned().collect::<Vec<Boolean>>();

        // Select a random T if self is infinity, to avoid exceptional cases
        let random_t = Self::alloc(cs.ns(|| "alloc random T"), || {
            let mut rng = OsRng::default();
            Ok(loop {
                let r = SWProjective::<P>::rand(&mut rng);
                if !r.is_zero() { break(r) }
            })
        })?;
        let t = Self::conditionally_select(
            cs.ns(|| "select self or random T"),
            &self.infinity,
            &random_t,
            self
        )?;

        // Acc := [3] T
        let mut acc = {
            let mut t_copy = t.clone();
            t_copy.double_in_place(cs.ns(|| "[2] * T"))?;
            //TODO: Is it ok unsafe ?
            t_copy.add_unsafe(cs.ns(|| "[3] * T"), &t)
        }?;

        for (i, bit) in bits.iter().enumerate()
            // Skip the LSB (we handle it after the loop)
            .skip(1)
            // Scan over the scalar bits in big-endian order
            .rev()
            // Skip the MSB (already accumulated)
            .skip(1)
            {
                let mut cs = cs.ns(|| format!("bit {}", i));

                // Q := k[i+1] ? T : −T
                let neg_y = t.y.negate(cs.ns(|| "neg y"))?;
                let selected_y = NonNativeFieldGadget::conditionally_select(
                    cs.ns(|| "select y or -y"),
                    bit,
                    &t.y,
                    &neg_y
                )?;
                let q = Self::new(t.x.clone(), selected_y, t.infinity);

                // Acc := (Acc + Q) + Acc
                // TODO: Is it ok unsafe ?
                acc = acc.double_and_add_unsafe(cs.ns(|| "double and add"), &q)?;
            }

        // return (k[0] = 0) ? (Acc - T) : Acc
        // TODO: Is it ok unsafe ?
        let neg_t = t.negate(cs.ns(|| "neg T"))?;
        let acc_minus_t = acc.add_unsafe(
            cs.ns(|| "Acc - T"),
            &neg_t
        )?;

        let result = Self::conditionally_select(
            cs.ns(|| "select acc or acc - T"),
            &bits[0],
            &acc_minus_t,
            &acc
        )?;

        // If self was infinity, return 0 instead of result
        let zero = Self::zero(cs.ns(|| "alloc 0"))?;
        Self::conditionally_select(
            cs.ns(|| "result or 0"),
            &self.infinity,
            &zero,
            &result
        )
    }

    ///This will take [(4 + 1) * ceil(len(bits)/2)] constraints to put the x lookup constraint
    ///into the addition formula. See coda/src/lib/snarky_curves/snarky_curves.ml "scale_known"
    #[inline]
    fn mul_bits_fixed_base<'a, CS: ConstraintSystem<ConstraintF>>(
        base: &'a SWProjective<P>,
        mut cs: CS,
        bits: &[Boolean],
    ) -> Result<Self, SynthesisError>{

        // Avoid exceptional cases when base = infinity
        if base.is_zero() {
            // TODO: If returning error is too much we might as well hardcode base,
            //       retrieve the infinity flag and return 0 or the mul result at
            //       the end
            return Err(SynthesisError::Other("Base cannot be infinity !".to_owned()));
        }
        let mut to_sub = SWProjective::<P>::zero();

        let mut t = base.clone();
        let sigma = base.clone();

        // Avoid exceptional cases when acc = base or acc = zero
        let shift = Self::alloc(cs.ns(|| "alloc random shift"), || {
            let mut rng = OsRng::default();
            Ok(loop {
                let r = SWProjective::<P>::rand(&mut rng);
                if !r.is_zero() && &r != base { break(r) }
            })
        })?;

        let mut acc = shift.clone();

        let mut bit_vec = Vec::new();
        bit_vec.extend_from_slice(bits);
        //Simply add padding. This should be safe, since the padding bit will be part of the
        //circuit. (It is also done elsewhere).
        if bits.len() % 2 != 0 {
            bit_vec.push(Boolean::constant(false))
        }

        for (i, bits) in bit_vec.chunks(2).enumerate() {
            let ti = t.clone();
            let two_ti = ti.double();
            let mut table = [
                sigma,
                sigma + &ti,
                sigma + &two_ti,
                sigma + &ti + &two_ti,
            ];

            //Compute constants
            SWProjective::batch_normalization(&mut table);
            let x_coords = [table[0].x, table[1].x, table[2].x, table[3].x];
            let y_coords = [table[0].y, table[1].y, table[2].y, table[3].y];
            let precomp = Boolean::and(cs.ns(|| format!("b0 AND b1_{}", i)), &bits[0], &bits[1])?;

            //Lookup x and y
            let x = NonNativeFieldGadget::two_bit_lookup_lc(cs.ns(|| format!("Lookup x_{}", i)), &precomp, &[bits[0], bits[1]],  &x_coords)?;
            let y = NonNativeFieldGadget::two_bit_lookup_lc(cs.ns(|| format!("Lookup y_{}", i)), &precomp, &[bits[0], bits[1]],  &y_coords)?;

            //Perform addition
            let adder: Self = Self::new(x, y, Boolean::constant(false));
            //TODO: Can we use add unsafe ?
            acc = acc.add(cs.ns(||format!("Add_{}", i)), &adder)?;
            t = t.double().double();
            to_sub += &sigma;
        }
        acc = acc.sub_constant(cs.ns(|| "acc - sigma*n_div_2"), &to_sub)?;
        acc = acc.sub(cs.ns(|| "subtract shift"), &shift)?;
        Ok(acc)
    }

    fn get_value(&self) -> Option<<Self as GroupGadget<SWProjective<P>, ConstraintF>>::Value> {
        match (self.x.get_value(), self.y.get_value(), self.infinity.get_value()) {
            (Some(x), Some(y), Some(infinity)) => Some(SWAffine::<P>::new(x, y, infinity).into_projective()),
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

impl<P, ConstraintF, SimulationF> PartialEq
for GroupAffineNonNativeGadget<P, ConstraintF, SimulationF>
    where
        P: SWModelParameters<BaseField = SimulationF>,
        ConstraintF: PrimeField,
        SimulationF: PrimeField + SquareRootField
{
    fn eq(&self, other: &Self) -> bool {
        self.x == other.x && self.y == other.y
    }
}

impl<P, ConstraintF, SimulationF> Eq
for GroupAffineNonNativeGadget<P, ConstraintF, SimulationF>
    where
        P: SWModelParameters<BaseField = SimulationF>,
        ConstraintF: PrimeField,
        SimulationF: PrimeField + SquareRootField
{
}


impl<P, ConstraintF, SimulationF> ToBitsGadget<ConstraintF>
for GroupAffineNonNativeGadget<P, ConstraintF, SimulationF>
    where
        P: SWModelParameters<BaseField = SimulationF>,
        ConstraintF: PrimeField,
        SimulationF: PrimeField + SquareRootField
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
        SimulationF: PrimeField + SquareRootField
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
        SimulationF: PrimeField + SquareRootField
{
    fn is_eq<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self
    ) -> Result<Boolean, SynthesisError> {
        let b0 = self.x.is_eq(cs.ns(|| "x"), &other.x)?;
        let b1 = self.y.is_eq(cs.ns(|| "y"),&other.y)?;
        let coordinates_equal = Boolean::and(cs.ns(|| "x AND y"), &b0, &b1)?;
        let both_are_zero = Boolean::and(
            cs.ns(|| "self.infinity AND other.infinity"),
            &self.infinity,
            &other.infinity
        )?;
        Boolean::or(cs.ns(|| "coordinates_equal OR both_are_zero"), &coordinates_equal, &both_are_zero)

    }

    #[inline]
    fn conditional_enforce_equal<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
        should_enforce: &Boolean
    ) -> Result<(), SynthesisError> {
        self
            .is_eq(cs.ns(|| "is_eq(self, other)"), &other)?
            .conditional_enforce_equal(
                cs.ns(|| "enforce condition"),
                &Boolean::constant(true), &should_enforce
            )?;
        Ok(())
    }

    #[inline]
    fn conditional_enforce_not_equal<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
        should_enforce: &Boolean
    ) -> Result<(), SynthesisError> {
        let is_equal = self.is_eq(cs.ns(|| "is_eq(self, other)"), other)?;
        Boolean::and(cs.ns(|| "is_equal AND should_enforce"), &is_equal, should_enforce)?
            .enforce_equal(cs.ns(|| "is_equal AND should_enforce == false"), &Boolean::Constant(false))
    }
}

impl<P, ConstraintF, SimulationF> GroupAffineNonNativeGadget<P, ConstraintF, SimulationF>
    where
        P: SWModelParameters<BaseField = SimulationF>,
        ConstraintF: PrimeField,
        SimulationF: PrimeField + SquareRootField

{
    pub fn new(x: NonNativeFieldGadget<SimulationF, ConstraintF>, y: NonNativeFieldGadget<SimulationF, ConstraintF>, infinity: Boolean) -> Self {
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
    ) -> Result<Self, SynthesisError>
    {
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
            // This is done below when we calculate inv (by F::inverse)
            let inv = x2_minus_x1.inverse(cs.ns(|| "compute inv"))?;
            NonNativeFieldGadget::alloc(cs.ns(|| "lambda"), || {
                Ok(y2_minus_y1.get_value().get()? * &inv.get_value().get()?)
            })
        } else {
            NonNativeFieldGadget::alloc(cs.ns(|| "lambda"), || {
                Ok(y2_minus_y1.get_value().get()? * &x2_minus_x1.get_value().get()?.inverse().get()?)
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
    /// Neither `self` nor `other` can be the neutral element, and other != ±self;
    /// If `safe` is set, enforce in the circuit exceptional cases not occurring.
    fn double_and_add_internal<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
        safe: bool,
    ) -> Result<Self, SynthesisError>
    {
        // lambda_1 := (y2 - y1)/(x2 - x1);
        // x3 = lambda_1^2 - x1 - x2;
        //
        // lambda_2 = 2·y1/(x1 - x3) - lambda_1.
        // x4 = lambda_2^2 - x1 - x3;
        // y4 = lambda_2 * (x1 - x4) - y1;
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
                Ok(y2_minus_y1.get_value().get()? * &x2_minus_x1.get_value().get()?.inverse().get()?)
            })
        }?;

        // Check lambda
        lambda.mul_equals(cs.ns(|| "check lambda"), &x2_minus_x1, &y2_minus_y1)?;

        let x_3 = NonNativeFieldGadget::alloc(&mut cs.ns(|| "x_3"), || {
            let lambda_val = lambda.get_value().get()?;
            let x1 = self.x.get_value().get()?;
            let x2 = other.x.get_value().get()?;
            Ok((lambda_val.square() - &x1) - &x2)
        })?;

        // Check x3
        let x3_plus_x1_plus_x2 = x_3
            .add(cs.ns(|| "x3 + x1"), &self.x)?
            .add(cs.ns(|| "x3 + x1 + x2"), &other.x)?;
        lambda.mul_equals(cs.ns(|| "check x3"), &lambda, &x3_plus_x1_plus_x2)?;

        // TODO: We already enforced no exceptional cases with lambda_1. Do we need to
        //       do it here too ?
        let lambda_2 = NonNativeFieldGadget::alloc(
            cs.ns(|| "lambda_2"),
            || {
                let x1_val = self.x.get_value().get()?;
                let y1_val = self.y.get_value().get()?;
                let x3_val = x_3.get_value().get()?;
                let lambda_val = lambda.get_value().get()?;

                let x1_minus_x3_inv = (x1_val - &x3_val).inverse().get()?;
                let y1_div_x1_minus_x3 = y1_val * &x1_minus_x3_inv;
                Ok((y1_div_x1_minus_x3 + &y1_div_x1_minus_x3) - &lambda_val)
            }
        )?;

        // Check lambda_2
        let x1_minus_x3 = self.x.sub(cs.ns(|| "x1 - x3"), &x_3)?;
        let two_y1 = self.y.double(cs.ns(|| "2y1"))?;
        let lambda_2_plus_lambda = lambda_2.add(cs.ns(|| "lambda_2 + lambda_1"), &lambda)?;

        lambda_2_plus_lambda.mul_equals(
            cs.ns(|| "(lambda_2 + lambda) * (x1 - x3) = 2y1"),
            &x1_minus_x3,
            &two_y1
        )?;

        let x_4 = NonNativeFieldGadget::alloc(&mut cs.ns(|| "x_4"), || {
            let lambda_2_val = lambda_2.get_value().get()?;
            let x1_val = self.x.get_value().get()?;
            let x3_val = x_3.get_value().get()?;
            Ok((lambda_2_val.square() - &x1_val) - &x3_val)
        })?;

        // Check x4
        let x4_plus_x1_plus_x3 = x_4
            .add(cs.ns(|| "x4 + x1"), &self.x)?
            .add(cs.ns(|| "x3 + x1 + x3"), &x_3)?;
        lambda_2.mul_equals(cs.ns(|| "check x4"), &lambda_2, &x4_plus_x1_plus_x3)?;

        let y_4 = NonNativeFieldGadget::alloc(&mut cs.ns(|| "y_4"), || {
            let lambda_2_val = lambda_2.get_value().get()?;
            let x_1_val = self.x.get_value().get()?;
            let y_1_val = self.y.get_value().get()?;
            let x_4_val = x_4.get_value().get()?;
            Ok(lambda_2_val * &(x_1_val - &x_4_val) - &y_1_val)
        })?;

        // Check y4
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
        SimulationF: PrimeField + SquareRootField
{
    #[inline]
    fn conditionally_select<CS: ConstraintSystem<ConstraintF>>(
        mut cs: CS,
        cond: &Boolean,
        first: &Self,
        second: &Self,
    ) -> Result<Self, SynthesisError> {
        let x = NonNativeFieldGadget::conditionally_select(&mut cs.ns(|| "x"), cond, &first.x, &second.x)?;
        let y = NonNativeFieldGadget::conditionally_select(&mut cs.ns(|| "y"), cond, &first.y, &second.y)?;
        let infinity = Boolean::conditionally_select(&mut cs.ns(|| "infinity"), cond, &first.infinity, &second.infinity)?;

        Ok(Self::new(x, y, infinity))
    }

    fn cost() -> usize {
        2 * <NonNativeFieldGadget<SimulationF, ConstraintF> as CondSelectGadget<ConstraintF>>::cost() +
            <Boolean as CondSelectGadget<ConstraintF>>::cost()
    }
}



impl<P, ConstraintF, SimulationF> ConstantGadget<SWProjective<P>, ConstraintF>
for GroupAffineNonNativeGadget<P, ConstraintF, SimulationF>
    where
        P: SWModelParameters<BaseField = SimulationF>,
        ConstraintF: PrimeField,
        SimulationF: PrimeField + SquareRootField
{
    fn from_value<CS: ConstraintSystem<ConstraintF>>(
        mut cs: CS,
        value: &SWProjective<P>,
    ) -> Self
    {
        let value = value.into_affine();
        let x = NonNativeFieldGadget::from_value(cs.ns(|| "hardcode x"), &value.x);
        let y = NonNativeFieldGadget::from_value(cs.ns(|| "hardcode y"), &value.y);
        let infinity = Boolean::constant(value.infinity);

        Self::new(x, y, infinity)
    }

    fn get_constant(&self) ->SWProjective<P> {
        let value_proj = SWAffine::<P>::new(
            self.x.get_value().unwrap(),
            self.y.get_value().unwrap(),
            self.infinity.get_value().unwrap()
        ).into_projective();
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
        SimulationF: PrimeField + SquareRootField
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
            },
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
            &infinity.not()
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
            },
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
        let ge = alloc_and_prime_order_check(
            cs.ns(|| "alloc and prime order check"),
            value_gen
        )?;

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
            },
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