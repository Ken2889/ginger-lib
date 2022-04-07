use algebra::{
    curves::{
        short_weierstrass_jacobian::{AffineRep, Jacobian},
        Curve, EndoMulParameters, SWModelParameters,
    },
    fields::{BitIterator, Field, PrimeField},
    groups::Group,
};
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use std::ops::{Add, Mul};
use std::{borrow::Borrow, marker::PhantomData, ops::Neg};
use num_traits::{Zero, One};

use crate::{
    groups::{check_mul_bits_fixed_base_inputs, check_mul_bits_inputs},
    prelude::*,
    Assignment,
};

#[derive(Derivative)]
#[derivative(Debug, Clone)]
#[must_use]
pub struct AffineGadget<
    P: SWModelParameters,
    ConstraintF: PrimeField,
    F: FieldGadget<P::BaseField, ConstraintF>,
> {
    pub x: F,
    pub y: F,
    pub infinity: Boolean,
    _params: PhantomData<P>,
    _engine: PhantomData<ConstraintF>,
}

impl<P, ConstraintF, F> AffineGadget<P, ConstraintF, F>
where
    P: SWModelParameters,
    ConstraintF: PrimeField,
    F: FieldGadget<P::BaseField, ConstraintF>,
{
    pub fn new(x: F, y: F, infinity: Boolean) -> Self {
        Self {
            x,
            y,
            infinity,
            _params: PhantomData,
            _engine: PhantomData,
        }
    }

    #[inline]
    /// Incomplete addition: neither `self` nor `other` can be the neutral
    /// element, and other != ±self.
    /// If `safe` is set, enforce in the circuit exceptional cases not occurring.
    fn add_internal<CS: ConstraintSystemAbstract<ConstraintF>>(
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
            // This is done below when we calculate inv (by F::inverse)
            let inv = x2_minus_x1.inverse(cs.ns(|| "compute inv"))?;
            F::alloc(cs.ns(|| "lambda"), || {
                Ok(y2_minus_y1.get_value().get()? * &inv.get_value().get()?)
            })
        } else {
            F::alloc(cs.ns(|| "lambda"), || {
                Ok(y2_minus_y1.get_value().get()?
                    * &x2_minus_x1.get_value().get()?.inverse().get()?)
            })
        }?;

        let x_3 = F::alloc(&mut cs.ns(|| "x_3"), || {
            let lambda_val = lambda.get_value().get()?;
            let x1 = self.x.get_value().get()?;
            let x2 = other.x.get_value().get()?;
            Ok((lambda_val.square() - &x1) - &x2)
        })?;

        let y_3 = F::alloc(&mut cs.ns(|| "y_3"), || {
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
    pub fn add_unsafe<CS: ConstraintSystemAbstract<ConstraintF>>(
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
    fn double_and_add_internal<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
        safe: bool,
    ) -> Result<Self, SynthesisError> {
        // The double-and-add sum P_4 = P_3 + P_1, where P_3 = P_1 + P_2,
        // under the above presumptions on P_1 and P_2 is enforced by just 5
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
            F::alloc(cs.ns(|| "lambda_1"), || {
                Ok(y2_minus_y1.get_value().get()? * &inv_1.get_value().get()?)
            })
        } else {
            // By our presumptions, x_2 - x_1 != 0
            F::alloc(cs.ns(|| "lambda_1"), || {
                Ok(y2_minus_y1.get_value().get()?
                    * &x2_minus_x1.get_value().get()?.inverse().get()?)
            })
        }?;

        // Constraint 1.
        lambda_1.mul_equals(cs.ns(|| "check lambda_1"), &x2_minus_x1, &y2_minus_y1)?;

        let x_3 = F::alloc(&mut cs.ns(|| "x_3"), || {
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
            F::alloc(cs.ns(|| "lambda_2"), || {
                let lambda_val = lambda_1.get_value().get()?;
                let two_y1_val = two_y1.get_value().get()?;

                let two_y1_div_x1_minus_x3 = two_y1_val * &inv_2.get_value().get()?;
                Ok(two_y1_div_x1_minus_x3 - &lambda_val)
            })
        } else {
            F::alloc(cs.ns(|| "lambda_2"), || {
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
        let x_4 = F::alloc(&mut cs.ns(|| "x_4"), || {
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
        let y_4 = F::alloc(&mut cs.ns(|| "y_4"), || {
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
    // // ToDo: evaluate if it may be worthy to make it complete
    pub fn double_and_add<CS: ConstraintSystemAbstract<ConstraintF>>(
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
    pub fn double_and_add_unsafe<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        self.double_and_add_internal(cs, other, false)
    }
}

impl<P, ConstraintF, F> PartialEq for AffineGadget<P, ConstraintF, F>
where
    P: SWModelParameters,
    ConstraintF: PrimeField,
    F: FieldGadget<P::BaseField, ConstraintF>,
{
    fn eq(&self, other: &Self) -> bool {
        self.x == other.x && self.y == other.y
    }
}

impl<P, ConstraintF, F> Eq for AffineGadget<P, ConstraintF, F>
where
    P: SWModelParameters,
    ConstraintF: PrimeField,
    F: FieldGadget<P::BaseField, ConstraintF>,
{
}

impl<P, ConstraintF, F> GroupGadget<Jacobian<P>, ConstraintF> for AffineGadget<P, ConstraintF, F>
where
    P: SWModelParameters,
    ConstraintF: PrimeField,
    F: FieldGadget<P::BaseField, ConstraintF>,
{
    type Value = Jacobian<P>;
    type Variable = (F::Variable, F::Variable);

    #[inline]
    fn get_value(&self) -> Option<Self::Value> {
        match (
            self.x.get_value(),
            self.y.get_value(),
            self.infinity.get_value(),
        ) {
            (Some(x), Some(y), Some(infinity)) => Some(if infinity {
                Jacobian::<P>::zero()
            } else {
                Jacobian::<P>::from_affine(&AffineRep::<P>::new(x, y))
            }),
            (None, None, None) => None,
            _ => unreachable!(),
        }
    }

    #[inline]
    fn get_variable(&self) -> Self::Variable {
        (self.x.get_variable(), self.y.get_variable())
    }

    #[inline]
    fn zero<CS: ConstraintSystemAbstract<ConstraintF>>(mut cs: CS) -> Result<Self, SynthesisError> {
        Ok(Self::new(
            F::zero(cs.ns(|| "x=zero"))?,
            F::zero(cs.ns(|| "y=zero"))?,
            Boolean::constant(true),
        ))
    }

    #[inline]
    fn is_zero<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        _: CS,
    ) -> Result<Boolean, SynthesisError> {
        Ok(self.infinity)
    }

    #[inline]
    // Algorithm for complete addition ported in R1CS from zcash: https://github.com/ebfull/halo/blob/master/src/gadgets/ecc.rs#L357.
    // The algorithm from zcash works only with Weierstrass curves y^2 = x^3+b, the algorithm here
    // is modified to work with generic curves y^2 = x^3 +ax + b, for b != 0 (as if b=0 then the point
    // (0,0), which is currently used to represent the identity point, will belong to the curve)
    //ToDo: in case in the future we may need to use curves with b=0, then it should be possible to
    // modify the function to employ the point (0,1) as the representation for the identity point
    fn add<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        let zero = F::zero(cs.ns(|| "alloc constant 0"))?;
        let is_same_x = F::alloc(cs.ns(|| "alloc x1 == x2"),
                                     || Ok(
                                         if self.x.get_value().get()? == other.x.get_value().get()? {
                                             P::BaseField::one()
                                         } else {
                                             P::BaseField::zero()
                                         })
        )?;
        let not_is_same_x = is_same_x.negate(cs.ns(|| "-is_same_x"))?.add_constant(cs.ns(|| "1 - is_same_x"), &P::BaseField::one())?;

        let x2_minus_x1 = other.x.sub(cs.ns(|| "x2 - x1"), &self.x)?;
        let inv = F::alloc(cs.ns(|| "alloc (x2-x1)^-1"), ||
            Ok(
                x2_minus_x1.get_value().get()?.inverse().unwrap_or(P::BaseField::one())
            )
        )?;

        // enforce that is_same_x = 0 if x2 != x1
        x2_minus_x1.mul_equals(cs.ns(|| "enforce (x2-x1)*is_same_x = 0"), &is_same_x, &zero)?;
        // enforce that is_same_x = 1 if x2 == x1
        x2_minus_x1.mul_equals(cs.ns(|| "enforce (x2-x1)*(x2-x1)^-1 = 1-is_same_x"), &inv, &not_is_same_x)?;

        // compute lambda_diff = (y2-y1)/(x2-x1+is_same_x), the value for lambda to be used in case x1 != x2
        let y2_minus_y1 = other.y.sub(cs.ns(|| "y2 - y1"), &self.y)?;
        let x2_minus_x1_plus_x_same = x2_minus_x1.add(cs.ns(|| "x2 - x1 + x_is_same"), &is_same_x)?;
        let lambda_diff = F::alloc(cs.ns(|| "alloc lambda_diff"), || Ok(
            y2_minus_y1.get_value().get()?*x2_minus_x1_plus_x_same.get_value().get()?.inverse().unwrap()
            // safe to unwrap inverse as x2_minus_x1_plus_x_same cannot be 0 by construction
            )
        )?;
        lambda_diff.mul_equals(cs.ns(|| "enforce lambda_diff = (y2-y1) div (x2-x1+is_same_x"), &x2_minus_x1_plus_x_same, &y2_minus_y1)?;

        // compute lambda_same = (3x1^2+a)/(2y1), the value for lambda to be used in case x1 = x2.
        // The correct value of lambda_same can be enforced with the constraint
        // 2y1*lambda_same = 3x1^2+a.
        // Note that in case y1 = 0, then the value of lambda_same is unconstrained, as
        // 2y1*lambda_same = 0 independently from the value of lambda_same;
        // However, since we consider only curves with prime order, then there cannot be points with
        // y1=0 besides the point at infinity, which is represented as x1=0, y1=0.
        // Therefore, in case `self` is the identity (i.e., x1=,y1=0), then there are no values of
        // lambda_same which would satisfy the constraint 2y1*lambda_same = 3x1^2+a, unless a == 0.
        // Therefore, we modify the constraint as (2y1+self.infinity)*lambda_same = 3x1^2+a, which
        // is satisfiable when y1=0 by simply choosing lambda_same=a
        let infinity_flag_to_field = F::from(self.infinity, cs.ns(|| "self infinity to field element"))?;
        let two_y1_plus_infinity_flag = self.y.double(cs.ns(|| "2y1"))?.add(cs.ns(|| "2y1+self.infinity"), &infinity_flag_to_field)?;
        let three_times_x1_square_plus_a = self.x.square(cs.ns(|| "x1^2"))?.mul_by_constant(cs.ns(|| "3x1^2"), &P::BaseField::from(3u128))?.add_constant(cs.ns(|| "3x1^2+a"), &P::COEFF_A)?;
        let lambda_same = F::alloc(cs.ns(|| "alloc lambda_same"), || Ok(
            three_times_x1_square_plus_a.get_value().get()?*two_y1_plus_infinity_flag.get_value().get()?.inverse().unwrap_or(P::BaseField::one())
        ))?;
        lambda_same.mul_equals(cs.ns(|| "enforce lambda_same = (3x1^2+a) div 2y1"), &two_y1_plus_infinity_flag, &three_times_x1_square_plus_a)?;

        // set lambda to either lambda_same or lambda_diff depending on is_same_x flag
        let lambda = F::alloc(cs.ns(|| "alloc lambda"), || Ok(
            if is_same_x.get_value().get()?.is_one() {
                lambda_same.get_value().get()?
            } else {
                lambda_diff.get_value().get()?
            }
        ))?;
        let lambda_minus_diff = lambda.sub(cs.ns(|| "lambda - lambda_diff"), &lambda_diff)?;
        let lambda_same_minus_diff = lambda_same.sub(cs.ns(|| "lambda_same - lambda_diff"), &lambda_diff)?;
        lambda_same_minus_diff.mul_equals(cs.ns(|| "enforce (lambda-lambda_diff) = is_same_x*(lambda_same-lambda_diff)"), &is_same_x, &lambda_minus_diff)?;

        // x3 = lambda^2-x1-x2
        let x1_plus_x2 = self.x.add(cs.ns(|| "x1+x2"), &other.x)?;
        let x3 = lambda.square(cs.ns(|| "lambda^2"))?.sub(cs.ns(|| "x3=lambda^2-x1-x2"), &x1_plus_x2)?;
        // y3 = lambda*(x1-x3)-y1
        let x1_minus_x3 = self.x.sub(cs.ns(|| "x1-x3"), &x3)?;
        let y3 = lambda.mul(cs.ns(|| "lambda*(x1-x3)"), &x1_minus_x3)?.sub(cs.ns(|| "y3=lambda*(x1-x3)-y1"), &self.y)?;

        // compute a flag is_sum_zero which is true iff self+other == identity
        let y1_plus_y2 = self.y.add(cs.ns(|| "y1+y2"), &other.y)?;
        let is_sum_zero = F::alloc(cs.ns(|| "alloc self+other == 0"), || Ok(
            if y1_plus_y2.get_value().get()?.is_zero() {
                is_same_x.get_value().get()?
            } else {
                P::BaseField::zero()
            }
        ))?;
        // enforce sum_is_zero == 0 if y1+y2 != 0, that is if the sum is not the identity
        y1_plus_y2.mul_equals(cs.ns(|| "enforce (y1+y2)*sum_is_zero=0"), &is_sum_zero, &zero)?;
        let same_x_minus_sum_zero = is_same_x.sub(cs.ns(|| "is_same_x-sum_is_zero"), &is_sum_zero)?;
        let inv = F::alloc(cs.ns(|| "alloc (y1+y2)^-1"), || Ok(
            // set inv to is_same_x if y1+y2 !=0, otherwise we can set it to an arbitrary as it has no impact on the constraint
            is_same_x.get_value().get()?*y1_plus_y2.get_value().get()?.inverse().unwrap_or(P::BaseField::one())
        ))?;

        // enforce sum_is_zero == is_same_x if y1+y2 == 0, as in this case the sum is the identity iff the x-coordinates are the same
        y1_plus_y2.mul_equals(cs.ns(|| "enforce (y1+y2)*(y1+y2)^-1=is_same_x-sum_is_zero"), &inv, &same_x_minus_sum_zero)?;

        // enforce that x4 = y4 = 0 if sum is zero
        let is_sum_not_zero = is_sum_zero.negate(cs.ns(|| "-is_sum_zero"))?.add_constant(cs.ns(|| "1-is_sum_zero"), &P::BaseField::one())?;
        let x4 = x3.mul(cs.ns(|| "x4 = x3*(1-is_sum_zero)"), &is_sum_not_zero)?;
        let y4 = y3.mul(cs.ns(|| "y4 = y3*(1-is_sum_zero)"), &is_sum_not_zero)?;

        // deal with the case when self is the identity
        let x5 = F::conditionally_select(cs.ns(|| "x5=x2 if self == 0, x4 otherwise"), &self.infinity, &other.x, &x4)?;
        let y5 = F::conditionally_select(cs.ns(|| "y5=y2 if self == 0, y4 otherwise"), &self.infinity, &other.y, &y4)?;

        // deal with the case when other is the identity
        let x_out = F::conditionally_select(cs.ns(|| "x_out=x1 if other == 0, x5 otherwise"), &other.infinity, &self.x, &x5)?;
        let y_out = F::conditionally_select(cs.ns(|| "y_out=y1 if other == 0, y5 otherwise"), &other.infinity, &self.y, &y5)?;

        let infinity_out = F::try_into(is_sum_zero)?;

        Ok(Self::new(x_out, y_out, infinity_out))
    }

    /// Incomplete addition: neither `self` nor `other` can be the neutral
    /// element.
    // ToDo: make addition complete
    fn add_constant<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Jacobian<P>,
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
        let other = other.into_affine().unwrap();
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

        let lambda = F::alloc(cs.ns(|| "lambda"), || {
            Ok(y2_minus_y1.get_value().get()? * &inv.get_value().get()?)
        })?;

        let x_3 = F::alloc(&mut cs.ns(|| "x_3"), || {
            let lambda_val = lambda.get_value().get()?;
            let x1 = self.x.get_value().get()?;
            let x2 = other_x;
            Ok((lambda_val.square() - &x1) - &x2)
        })?;

        let y_3 = F::alloc(&mut cs.ns(|| "y_3"), || {
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

    #[inline]
    fn double_in_place<CS: ConstraintSystemAbstract<ConstraintF>>(
        &mut self,
        mut cs: CS,
    ) -> Result<(), SynthesisError> {
        let a = P::COEFF_A;
        let x_squared = self.x.square(cs.ns(|| "x^2"))?;

        let one = P::BaseField::one();
        let two = one.double();
        let three = two + &one;

        let three_x_squared = x_squared.mul_by_constant(cs.ns(|| "3 * x^2"), &three)?;
        let three_x_squared_plus_a = three_x_squared.add_constant(cs.ns(|| "3 * x^2 + a"), &a)?;

        let two_y = self.y.double(cs.ns(|| "2y"))?;

        let lambda = F::alloc(cs.ns(|| "lambda"), || {
            let y_doubled_inv = two_y.get_value().get()?.inverse().get()?;
            Ok(three_x_squared_plus_a.get_value().get()? * &y_doubled_inv)
        })?;

        // Check lambda
        lambda.mul_equals(cs.ns(|| "check lambda"), &two_y, &three_x_squared_plus_a)?;

        // Allocate fresh x and y as a temporary workaround to reduce the R1CS density.
        let x = F::alloc(cs.ns(|| "new x"), || {
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

        let y = F::alloc(cs.ns(|| "new y"), || {
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

    fn negate<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<Self, SynthesisError> {
        Ok(Self::new(
            self.x.clone(),
            self.y.negate(cs.ns(|| "negate y"))?,
            self.infinity,
        ))
    }

    /// [Hopwood]'s optimized scalar multiplication, adapted to the general case of no
    /// leading-one assumption. This is achieved by transforming the scalar to (almost)
    /// constant length by adding the scalar field modulus, and applying the Hopwood algorithm
    /// to a bit sequence of length `n+1`, where `n` is the length of the scalar field modulus.
    /// Takes `7*n + O(1)` number of constraints instead of `6*n+O(1)`.
    ///
    /// Given a little-endian sequence `bits` of at most `n` Boolean gadgets, computes
    /// the scalar multiple of `&self`, assuming the latter is assured to be in the prime order
    /// subgroup. Due to incomplete arithmetics, is not satifiable for the scalars from the set
    /// {0, p-2, p-1, p, p+1}.
    ///
    /// [Hopwood] https://github.com/zcash/zcash/issues/3924
    /// Implementation adapted from https://github.com/ebfull/halo/blob/master/src/gadgets/ecc.rs#L1762.
    fn mul_bits<'a, CS: ConstraintSystemAbstract<ConstraintF>>(
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
            let selected_y =
                F::conditionally_select(cs.ns(|| "select y or -y"), bit, &t.y, &neg_y)?;
            let q = Self::new(t.x.clone(), selected_y, t.infinity);

            // Acc := (Acc + Q) + Acc using double_and_add_internal
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
        Assuming that T is in the correct subgroup, no exceptions for affine arithmetic
        are met.
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

        // No exceptions can be hit here either, so we are allowed to use unsafe add.
        // (For T = 0 we don't care.)
        for (i, bit) in bits
            .iter()
            .enumerate()
            // Skip the two least significant bits (we handle them after the loop)
            .skip(3)
            // Scan over the scalar bits in big-endian order
            .rev()
        {
            double_and_add_step(cs.ns(|| format!("bit {}", i + 2)), bit, &mut acc, &t, false)?;
        }

        /* The last three bits are treated by a careful decision between add()
        and add_unsafe().
        */

        // Why the step processing bit[2] needs to be treated with a
        // secure add: The scalar after adding p consists of n+1 bits
        //             n-1 bits
        //     /-----------------------------\
        //     (bits[n], ... ,bits[3], bits[2], bits[1], bits[0])
        //
        // and the result of `acc` after processing bit[2] is
        //
        //                 n bits
        //     /---------------------------------\
        //     [bits[n], bits[n-1],..., bits[2], 1] * T.
        //
        // This output is equal to 0 (and hence causes an exception in the
        // last add when processing bits[2]) iff
        //
        //     [bits[n], bits[n-1],....,bits[2], 1] = p,
        //
        // or equivalently [bit[n],...,bits[2],bits[1]] = {p or p-1}.
        // This corresponds to
        //     scalar + p  = 2 * {p or p-1} + bits[0]
        // or  scalar being from {p-2, p-1, p, p + 1}.
        // A more detailed exploration shows that this set is the complete set
        // of exceptions.
        double_and_add_step(cs.ns(|| "bit 2"), &bits[2], &mut acc, &t, true)?;

        // Why the step processing bit[1] needs to be treated with a
        // secure add:
        // After processing bit[1] `acc` is equal to
        //
        //                 n+1 bits
        //     /---------------------------------------\
        //     [bits[n], bits[n-1],..., bits[2], bits[1], 1] * T
        //
        // which is 0 iff
        //
        //     [bits[n], bits[n-1],....,bits[2],bits[1], 1] = p,
        //
        // or equivalently [bit[n],...,bits[2],bits[1],bits[0]] = {p or p-1}.
        // These cases corresponds to
        //     scalar + p  = {p or p-1}
        // or a scalar from  {0 , -1}. The latter cannot be achieved by an
        // unsigned integer representation. The case scalar = 0 is not
        // covered by the secure add from the step of bits[2].
        double_and_add_step(cs.ns(|| "bit 1"), &bits[1], &mut acc, &t, true)?;

        // The final bit is taken into account by correcting the `1` in
        //
        //     [bits[n], bits[n-1],....,bits[2],bits[1], 1] * T,
        //
        // via substracting T and a subsequent conditional choice
        //
        //      return (k[0] = 0) ? (Acc - T) : Acc.
        //
        // We hit exceptions in this sub if and only if
        //
        //   [bits[n], bits[n-1],....,bits[2],bits[1], 1]*T = +/- T,
        // or
        //  [bits[n], bits[n-1],....,bits[2],bits[1], 1] = +/- 1  mod p.
        // Hence
        //
        //  [bits[n], bits[n-1],....,bits[2],bits[1], 0] = {-2,0} mod p,
        //
        // and [bits[n],...,bits[1],bits[0]] is contained in {-2,-1,0,1} mod p.
        // As this case is already covered by the secure add of step bit[2],
        // we may use add_unsafe() here.
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

    /// Fixed base scalar multiplication as mentioned by [Hopwood] using a signed
    /// digit representation. Takes roughly 2 constraints per scalar bit.
    /// Bits must be in little endian form, and as most as long as the scalar field
    /// modulus.
    /// CAUTION: Due to the use of incomplete arithemtics, there are few exceptions
    /// described in `fn check_mul_bits_fixed_base_inputs()`.
    ///
    /// [Hopwood]: https://github.com/zcash/zcash/issues/3924
    #[inline]
    fn mul_bits_fixed_base<'a, CS: ConstraintSystemAbstract<ConstraintF>>(
        base: &'a Jacobian<P>,
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
        let mut to_sub = Jacobian::<P>::zero();

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
            Jacobian::batch_normalization(&mut table);
            let x_coords = [table[0].x, table[1].x, table[2].x, table[3].x];
            let y_coords = [table[0].y, table[1].y, table[2].y, table[3].y];
            let precomp = Boolean::and(cs.ns(|| format!("b0 AND b1_{}", i)), &bits[0], &bits[1])?;

            //Lookup x and y
            let x = F::two_bit_lookup_lc(
                cs.ns(|| format!("Lookup x_{}", i)),
                &precomp,
                &[bits[0], bits[1]],
                &x_coords,
            )?;
            let y = F::two_bit_lookup_lc(
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
                    // acc = acc.add(cs.ns(|| format!("Add_{}", i)), &adder)?;
                    acc = acc.add_internal(cs.ns(|| format!("Add_{}", i)), &adder, true)?;
                }
            }

            // Update values for next chunk
            t = t.double().double();
            to_sub += &table[0];
        }
        acc = acc.sub_constant(cs.ns(|| "acc - to_sub"), &to_sub)?;
        Ok(acc)
    }

    fn mul_bits_fixed_base_with_precomputed_base_powers<'a, CS, I, B>(
        &mut self,
        _cs: CS,
        _scalar_bits_with_base_powers: I,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystemAbstract<ConstraintF>,
        I: Iterator<Item = (B, &'a Jacobian<P>)>,
        B: Borrow<Boolean>,
    {
        todo!()
    }

    /// Useful in context when you have some signed representation of the scalar's digits, like
    /// in BH hash. I decided here to keep the same logic as TE implementation  for future extensibility:
    /// in fact there is no actual difference between "outer" and "inner" sums since they all
    /// are SW unsafe additions. The code could be simplified, but nothing changes from a number
    /// of constraints point of view.
    fn mul_bits_fixed_base_with_3_bit_signed_digit_precomputed_base_powers<'a, CS, I, J, B>(
        mut cs: CS,
        bases: &[B],
        scalars: &[J],
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystemAbstract<ConstraintF>,
        I: Borrow<[Boolean]>,
        J: Borrow<[I]>,
        B: Borrow<[Jacobian<P>]>,
    {
        const CHUNK_SIZE: usize = 3;
        let mut sw_result: Option<AffineGadget<P, ConstraintF, F>> = None;
        let mut result: Option<AffineGadget<P, ConstraintF, F>> = None;
        let mut process_segment_result = |mut cs: r1cs_core::Namespace<_, _>,
                                          result: &AffineGadget<P, ConstraintF, F>|
         -> Result<(), SynthesisError> {
            let segment_result = result.clone();
            match sw_result {
                None => {
                    sw_result = Some(segment_result);
                }
                Some(ref mut sw_result) => {
                    *sw_result =
                        segment_result.add_unsafe(cs.ns(|| "sw outer addition"), sw_result)?;
                }
            }
            Ok(())
        };
        // Compute ∏(h_i^{m_i}) for all i.
        for (segment_i, (segment_bits_chunks, segment_powers)) in
            scalars.iter().zip(bases.iter()).enumerate()
        {
            for (i, (bits, base_power)) in segment_bits_chunks
                .borrow()
                .iter()
                .zip(segment_powers.borrow().iter())
                .enumerate()
            {
                let base_power = base_power.borrow();
                let mut acc_power = *base_power;
                let mut coords = vec![];
                for _ in 0..4 {
                    coords.push(acc_power);
                    acc_power += base_power;
                }
                let bits = bits.borrow().to_bits(
                    &mut cs.ns(|| format!("Convert Scalar {}, {} to bits", segment_i, i)),
                )?;
                if bits.len() != CHUNK_SIZE {
                    return Err(SynthesisError::Unsatisfiable);
                }
                // TODO: check if zero possible
                let coords = Jacobian::<P>::batch_into_affine(coords.as_slice())?;
                let x_coeffs = coords.iter().map(|p| p.x).collect::<Vec<_>>();
                let y_coeffs = coords.iter().map(|p| p.y).collect::<Vec<_>>();
                let precomp = Boolean::and(
                    cs.ns(|| format!("precomp in window {}, {}", segment_i, i)),
                    &bits[0],
                    &bits[1],
                )?;
                let x = F::two_bit_lookup_lc(
                    cs.ns(|| format!("x in window {}, {}", segment_i, i)),
                    &precomp,
                    &[bits[0], bits[1]],
                    &x_coeffs,
                )?;
                let y = F::three_bit_cond_neg_lookup(
                    cs.ns(|| format!("y lookup in window {}, {}", segment_i, i)),
                    &bits,
                    &precomp,
                    &y_coeffs,
                )?;
                let tmp = Self::new(x, y, Boolean::constant(false));
                match result {
                    None => {
                        result = Some(tmp);
                    }
                    Some(ref mut result) => {
                        *result = tmp.add_unsafe(
                            cs.ns(|| format!("addition of window {}, {}", segment_i, i)),
                            result,
                        )?;
                    }
                }
            }
            process_segment_result(cs.ns(|| format!("window {}", segment_i)), &result.unwrap())?;
            result = None;
        }
        if result.is_some() {
            process_segment_result(cs.ns(|| "leftover"), &result.unwrap())?;
        }
        Ok(sw_result.unwrap())
    }

    fn fixed_base_msm_with_precomputed_base_powers<'a, CS, T, I, B>(
        _cs: CS,
        _bases: &[B],
        _scalars: I,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystemAbstract<ConstraintF>,
        T: 'a + ToBitsGadget<ConstraintF> + ?Sized,
        I: Iterator<Item = &'a T>,
        B: Borrow<[Jacobian<P>]>,
    {
        todo!()
    }

    fn fixed_base_msm<'a, CS, T, IS, IB>(
        mut cs: CS,
        mut bases: IB,
        mut scalars: IS,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystemAbstract<ConstraintF>,
        T: 'a + ToBitsGadget<ConstraintF> + ?Sized,
        IS: Iterator<Item = &'a T>,
        IB: Iterator<Item = &'a Jacobian<P>>,
    {
        // Pre - check on sizes.
        // Other checks on scalars and bases will be performed directly when calling the mul_bits_fixed_base.
        // TODO: Other pre-checks we can perform ?
        let scalars_len = scalars
            .size_hint()
            .1
            .expect("Scalars iterator size should be known at this point");
        
        let bases_len = bases
            .size_hint()
            .1
            .expect("Bases iterator size should be known at this point");

        if bases_len < scalars_len || bases_len == 0 {
            return Err(SynthesisError::Other(
                format!(
                    "Unable to enforce MSM. Bases are not enough for scalars. Number of bases: {}, number of scalars: {}",
                    bases_len,
                    scalars_len
                )
            ));
        }

        // Initialize result to avoid exceptional cases due to incomplete arithmetic
        let mut scalar_bits = scalars
            .next()
            .unwrap() // Cannot fail as we checked scalars > bases and bases cannot be 0
            .to_bits(cs.ns(|| "scalar 0 to bits"))?;
        scalar_bits.reverse(); // mul_bits_fixed_base requires the bits in little endian form

        let mut result = Self::mul_bits_fixed_base(
            bases.next().unwrap(), // Cannot fail as we checked bases > 0
            cs.ns(|| "base_0 ^ scalar_0"),
            scalar_bits.as_slice(),
        )?;

        // Process remaining scalars and bases
        for (i, (base, scalar)) in bases.zip(scalars).enumerate() {
            scalar_bits = scalar.to_bits(
                cs.ns(|| format!("Scalar {} to bits", i + 1))
            )?;
            scalar_bits.reverse();

            let term_i = Self::mul_bits_fixed_base(
                base,
                cs.ns(|| format!("base_{} ^ scalar_{}", i + 1, i + 1)),
                scalar_bits.as_slice(),
            )?;
            result = result.add(cs.ns(|| format!("add term_{}", i)), &term_i)?;
        }

        Ok(result)
    }

    fn cost_of_add() -> usize {
        3 * F::cost_of_mul_equals() + F::cost_of_inv()
    }

    fn cost_of_double() -> usize {
        3 * F::cost_of_mul() + F::cost_of_mul_equals()
    }
}

impl<P, ConstraintF, F> EndoMulCurveGadget<Jacobian<P>, ConstraintF>
    for AffineGadget<P, ConstraintF, F>
where
    P: EndoMulParameters,
    ConstraintF: PrimeField,
    F: FieldGadget<P::BaseField, ConstraintF>,
{
    /// Given an arbitrary curve element `&self`, applies the endomorphism
    /// defined by `ENDO_COEFF`.
    fn apply_endomorphism<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<Self, SynthesisError> {
        Ok(Self::new(
            self.x.mul_by_constant(cs.ns(|| "endo x"), &P::ENDO_COEFF)?,
            self.y.clone(),
            self.infinity,
        ))
    }

    /// The endomorphism-based scalar multiplication circuit from [Halo],taking only
    /// 3.5 constraints per "scalar" bit. Assumes that `ENDO_SCALAR` satisfies the minimal
    /// distance property as mentioned in `SWModelParameters`.
    /// Given any non-trivial point `P= &self` of the prime order r subgroup, and a slice
    /// of an even number of at most `lambda` Booleans `bits`, enforces that the result equals
    ///     phi(bits) * P,
    /// where `phi(bits)` is the equivalent scalar representation of `bits`.
    ///
    /// [Halo]: https://eprint.iacr.org/2019/1021
    fn endo_mul<CS: ConstraintSystemAbstract<ConstraintF>>(
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
                F::conditionally_select(
                    cs.ns(|| format!("conditional bit1 select endo {}", i)),
                    &bits[i * 2 + 1],
                    &endo_self.x,
                    &self.x,
                )?,
                F::conditionally_select(
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

impl<P, ConstraintF, F> CondSelectGadget<ConstraintF> for AffineGadget<P, ConstraintF, F>
where
    P: SWModelParameters,
    ConstraintF: PrimeField,
    F: FieldGadget<P::BaseField, ConstraintF>,
{
    #[inline]
    fn conditionally_select<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        cond: &Boolean,
        first: &Self,
        second: &Self,
    ) -> Result<Self, SynthesisError> {
        let x = F::conditionally_select(&mut cs.ns(|| "x"), cond, &first.x, &second.x)?;
        let y = F::conditionally_select(&mut cs.ns(|| "y"), cond, &first.y, &second.y)?;
        let infinity = Boolean::conditionally_select(
            &mut cs.ns(|| "infinity"),
            cond,
            &first.infinity,
            &second.infinity,
        )?;

        Ok(Self::new(x, y, infinity))
    }

    fn cost() -> usize {
        2 * <F as CondSelectGadget<ConstraintF>>::cost()
            + <Boolean as CondSelectGadget<ConstraintF>>::cost()
    }
}

impl<P, ConstraintF, F> EqGadget<ConstraintF> for AffineGadget<P, ConstraintF, F>
where
    P: SWModelParameters,
    ConstraintF: PrimeField,
    F: FieldGadget<P::BaseField, ConstraintF>,
{
    fn is_eq<CS: ConstraintSystemAbstract<ConstraintF>>(
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
    fn conditional_enforce_equal<CS: ConstraintSystemAbstract<ConstraintF>>(
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
    fn conditional_enforce_not_equal<CS: ConstraintSystemAbstract<ConstraintF>>(
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

impl<P, ConstraintF, F> AllocGadget<Jacobian<P>, ConstraintF> for AffineGadget<P, ConstraintF, F>
where
    P: SWModelParameters,
    ConstraintF: PrimeField,
    F: FieldGadget<P::BaseField, ConstraintF>,
{
    #[inline]
    fn alloc<FN, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        value_gen: FN,
    ) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Jacobian<P>>,
    {
        let (x, y, infinity) = match value_gen() {
            Ok(ge) => {
                let ge = ge.borrow();
                if ge.is_zero() {
                    (Ok(P::BaseField::zero()), Ok(P::BaseField::zero()), Ok(true))
                } else {
                    let ge = ge.into_affine().unwrap();
                    (Ok(ge.x), Ok(ge.y), Ok(false))
                }
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

        let x = F::alloc(&mut cs.ns(|| "x"), || x)?;
        let y = F::alloc(&mut cs.ns(|| "y"), || y)?;
        let infinity = Boolean::alloc(&mut cs.ns(|| "infinity"), || infinity)?;

        // Check that y^2 = x^3 + ax +b
        // We do this by checking that y^2 - b = x * (x^2 +a)
        let x2 = x.square(&mut cs.ns(|| "x^2"))?;
        let y2 = y.square(&mut cs.ns(|| "y^2"))?;

        let x2_plus_a = x2.add_constant(cs.ns(|| "x^2 + a"), &a)?;
        let y2_minus_b = y2.add_constant(cs.ns(|| "y^2 - b"), &b.neg())?;

        let x2_plus_a_times_x = x2_plus_a.mul(cs.ns(|| "(x^2 + a)*x"), &x)?;

        x2_plus_a_times_x.conditional_enforce_equal(
            cs.ns(|| "on curve check"),
            &y2_minus_b,
            &infinity.not(),
        )?;

        Ok(Self::new(x, y, infinity))
    }

    #[inline]
    fn alloc_without_check<FN, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        value_gen: FN,
    ) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Jacobian<P>>,
    {
        let (x, y, infinity) = match value_gen() {
            Ok(ge) => {
                let ge = ge.borrow();
                if ge.is_zero() {
                    (Ok(P::BaseField::zero()), Ok(P::BaseField::zero()), Ok(true))
                } else {
                    let ge = ge.into_affine().unwrap();
                    (Ok(ge.x), Ok(ge.y), Ok(false))
                }
            }
            _ => (
                Err(SynthesisError::AssignmentMissing),
                Err(SynthesisError::AssignmentMissing),
                Err(SynthesisError::AssignmentMissing),
            ),
        };

        let x = F::alloc(&mut cs.ns(|| "x"), || x)?;
        let y = F::alloc(&mut cs.ns(|| "y"), || y)?;
        let infinity = Boolean::alloc(&mut cs.ns(|| "infinity"), || infinity)?;

        Ok(Self::new(x, y, infinity))
    }

    #[inline]
    fn alloc_checked<FN, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        value_gen: FN,
    ) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Jacobian<P>>,
    {
        let alloc_and_prime_order_check =
            |mut cs: r1cs_core::Namespace<_, _>, value_gen: FN| -> Result<Self, SynthesisError> {
                let cofactor_weight = BitIterator::new(P::COFACTOR).filter(|b| *b).count();
                // If we multiply by r, we actually multiply by r - 2.
                let r_minus_1 = (-P::ScalarField::one()).into_repr();
                let r_weight = BitIterator::new(&r_minus_1).filter(|b| *b).count();
                // We pick the most efficient method of performing the prime order check:
                // If the cofactor has lower hamming weight than the scalar field's modulus,
                // we first multiply by the inverse of the cofactor, and then, after allocating,
                // multiply by the cofactor. This ensures the resulting point has no cofactors
                //
                // Else, we multiply by the scalar field's modulus and ensure that the result
                // is zero.
                if cofactor_weight < r_weight {
                    let ge = Self::alloc(cs.ns(|| "Alloc checked"), || {
                        value_gen().map(|ge| ge.borrow().scale_by_cofactor_inv())
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
    fn alloc_input<FN, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        value_gen: FN,
    ) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Jacobian<P>>,
    {
        let (x, y, infinity) = match value_gen() {
            Ok(ge) => {
                let ge = ge.borrow();
                if ge.is_zero() {
                    (Ok(P::BaseField::zero()), Ok(P::BaseField::zero()), Ok(true))
                } else {
                    let ge = ge.into_affine().unwrap();
                    (Ok(ge.x), Ok(ge.y), Ok(false))
                }
            }
            _ => (
                Err(SynthesisError::AssignmentMissing),
                Err(SynthesisError::AssignmentMissing),
                Err(SynthesisError::AssignmentMissing),
            ),
        };

        let b = P::COEFF_B;
        let a = P::COEFF_A;

        let x = F::alloc_input(&mut cs.ns(|| "x"), || x)?;
        let y = F::alloc_input(&mut cs.ns(|| "y"), || y)?;
        let infinity = Boolean::alloc_input(&mut cs.ns(|| "infinity"), || infinity)?;

        // Check that y^2 = x^3 + ax +b
        // We do this by checking that y^2 - b = x * (x^2 +a)
        let x2 = x.square(&mut cs.ns(|| "x^2"))?;
        let y2 = y.square(&mut cs.ns(|| "y^2"))?;

        let x2_plus_a = x2.add_constant(cs.ns(|| "x^2 + a"), &a)?;
        let y2_minus_b = y2.add_constant(cs.ns(|| "y^2 - b"), &b.neg())?;

        let x2_plus_a_times_x = x2_plus_a.mul(cs.ns(|| "(x^2 + a)*x"), &x)?;

        x2_plus_a_times_x.conditional_enforce_equal(
            cs.ns(|| "on curve check"),
            &y2_minus_b,
            &infinity.not(),
        )?;

        Ok(Self::new(x, y, infinity))
    }
}

impl<P, ConstraintF, F> ConstantGadget<Jacobian<P>, ConstraintF> for AffineGadget<P, ConstraintF, F>
where
    P: SWModelParameters,
    ConstraintF: PrimeField,
    F: FieldGadget<P::BaseField, ConstraintF>,
{
    fn from_value<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        value: &Jacobian<P>,
    ) -> Self {
        if value.is_zero() {
            Self::zero(cs).unwrap()
        } else {
            let value = value.into_affine().unwrap();
            let x = F::from_value(cs.ns(|| "hardcode x"), &value.x);
            let y = F::from_value(cs.ns(|| "hardcode y"), &value.y);
            let infinity = Boolean::constant(false);
            Self::new(x, y, infinity)
        }
    }

    fn get_constant(&self) -> Jacobian<P> {
        let value_proj = if self.infinity.get_value().unwrap() {
            Jacobian::<P>::zero()
        } else {
            Jacobian::<P>::from_affine(&AffineRep::<P>::new(
                self.x.get_value().unwrap(),
                self.y.get_value().unwrap(),
            ))
        };
        let x = value_proj.x;
        let y = value_proj.y;
        let z = value_proj.z;
        Jacobian::<P>::new(x, y, z)
    }
}

impl<P, ConstraintF, F> ToBitsGadget<ConstraintF> for AffineGadget<P, ConstraintF, F>
where
    P: SWModelParameters,
    ConstraintF: PrimeField,
    F: FieldGadget<P::BaseField, ConstraintF>,
{
    fn to_bits<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        let mut x_bits = self.x.to_bits(&mut cs.ns(|| "X Coordinate To Bits"))?;
        let y_bits = self.y.to_bits(&mut cs.ns(|| "Y Coordinate To Bits"))?;
        x_bits.extend_from_slice(&y_bits);
        x_bits.push(self.infinity);
        Ok(x_bits)
    }

    fn to_bits_strict<CS: ConstraintSystemAbstract<ConstraintF>>(
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

impl<P, ConstraintF, F> ToBytesGadget<ConstraintF> for AffineGadget<P, ConstraintF, F>
where
    P: SWModelParameters,
    ConstraintF: PrimeField,
    F: FieldGadget<P::BaseField, ConstraintF>,
{
    fn to_bytes<CS: ConstraintSystemAbstract<ConstraintF>>(
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

    fn to_bytes_strict<CS: ConstraintSystemAbstract<ConstraintF>>(
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

#[derive(Derivative)]
#[derivative(Debug, Clone)]
#[must_use]
pub struct CompressAffinePointGadget<ConstraintF: PrimeField> {
    pub x: FpGadget<ConstraintF>,
    pub y: FpGadget<ConstraintF>,
    pub infinity: Boolean,
    _engine: PhantomData<ConstraintF>,
}

impl<ConstraintF> CompressAffinePointGadget<ConstraintF>
where
    ConstraintF: PrimeField,
{
    pub fn new(x: FpGadget<ConstraintF>, y: FpGadget<ConstraintF>, infinity: Boolean) -> Self {
        Self {
            x,
            y,
            infinity,
            _engine: PhantomData,
        }
    }
}

use crate::fields::fp::FpGadget;
use crate::groups::EndoMulCurveGadget;
use crate::ToCompressedBitsGadget;

impl<ConstraintF> ToCompressedBitsGadget<ConstraintF> for CompressAffinePointGadget<ConstraintF>
where
    ConstraintF: PrimeField,
{
    /// Enforce compression of a point through serialization of the x coordinate and storing
    /// a sign bit for the y coordinate.
    fn to_compressed<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        //Enforce x_coordinate to bytes
        let mut compressed_bits = self.x.to_bits_strict(cs.ns(|| "x_to_bits_strict"))?;
        compressed_bits.push(self.infinity);
        let is_odd = self.y.is_odd(cs.ns(|| "y parity"))?;
        compressed_bits.push(is_odd);
        Ok(compressed_bits)
    }
}
