//! A polynomial represented in evaluations form.

use crate::{get_best_evaluation_domain, DensePolynomial, EvaluationDomain};
use crate::{serialize::*, PrimeField};
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};

/// Stores a polynomial in evaluation form.
#[derive(Debug)]
pub struct Evaluations<F: PrimeField> {
    /// The evaluations of a polynomial over the domain `D`
    pub evals: Vec<F>,
    /// Evaluation domain
    pub domain: Box<dyn EvaluationDomain<F>>,
}

impl<F: PrimeField> CanonicalSerialize for Evaluations<F> {
    fn serialize<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
        CanonicalSerialize::serialize(&self.evals, writer)
    }

    fn serialized_size(&self) -> usize {
        self.evals.serialized_size()
    }
}

impl<F: PrimeField> CanonicalDeserialize for Evaluations<F> {
    fn deserialize<R: Read>(reader: R) -> Result<Self, SerializationError> {
        let evals: Vec<F> = CanonicalDeserialize::deserialize(reader)?;
        let domain =
            get_best_evaluation_domain::<F>(evals.len()).ok_or(SerializationError::InvalidData)?;

        Ok(Self { evals, domain })
    }
}

impl<F: PrimeField> Evaluations<F> {
    /// Construct `Self` from evaluations and a domain.
    pub fn from_vec_and_domain(evals: Vec<F>, domain: Box<dyn EvaluationDomain<F>>) -> Self {
        Self { evals, domain }
    }

    /// Interpolate a polynomial from a list of evaluations
    pub fn interpolate_by_ref(&self) -> DensePolynomial<F> {
        DensePolynomial::from_coefficients_vec(self.domain.ifft(&self.evals))
    }

    /// Interpolate a polynomial from a list of evaluations
    pub fn interpolate(self) -> DensePolynomial<F> {
        let Self { mut evals, domain } = self;
        domain.ifft_in_place(&mut evals);
        DensePolynomial::from_coefficients_vec(evals)
    }
}

impl<F: PrimeField> std::ops::Index<usize> for Evaluations<F> {
    type Output = F;

    fn index(&self, index: usize) -> &F {
        &self.evals[index]
    }
}

impl<'a, 'b, F: PrimeField> Mul<&'a Evaluations<F>> for &'b Evaluations<F> {
    type Output = Evaluations<F>;

    #[inline]
    fn mul(self, other: &'a Evaluations<F>) -> Evaluations<F> {
        let mut result = self.clone();
        result *= other;
        result
    }
}

impl<'a, F: PrimeField> MulAssign<&'a Evaluations<F>> for Evaluations<F> {
    #[inline]
    fn mul_assign(&mut self, other: &'a Evaluations<F>) {
        assert_eq!(
            self.domain.as_ref(),
            other.domain.as_ref(),
            "domains are unequal"
        );
        self.evals
            .iter_mut()
            .zip(&other.evals)
            .for_each(|(a, b)| *a *= b);
    }
}

impl<'a, 'b, F: PrimeField> Add<&'a Evaluations<F>> for &'b Evaluations<F> {
    type Output = Evaluations<F>;

    #[inline]
    fn add(self, other: &'a Evaluations<F>) -> Evaluations<F> {
        let mut result = self.clone();
        result += other;
        result
    }
}

impl<'a, F: PrimeField> AddAssign<&'a Evaluations<F>> for Evaluations<F> {
    #[inline]
    fn add_assign(&mut self, other: &'a Evaluations<F>) {
        assert_eq!(
            self.domain.as_ref(),
            other.domain.as_ref(),
            "domains are unequal"
        );
        self.evals
            .iter_mut()
            .zip(&other.evals)
            .for_each(|(a, b)| *a += b);
    }
}

impl<'a, 'b, F: PrimeField> Sub<&'a Evaluations<F>> for &'b Evaluations<F> {
    type Output = Evaluations<F>;

    #[inline]
    fn sub(self, other: &'a Evaluations<F>) -> Evaluations<F> {
        let mut result = self.clone();
        result -= other;
        result
    }
}

impl<'a, F: PrimeField> SubAssign<&'a Evaluations<F>> for Evaluations<F> {
    #[inline]
    fn sub_assign(&mut self, other: &'a Evaluations<F>) {
        assert_eq!(
            self.domain.as_ref(),
            other.domain.as_ref(),
            "domains are unequal"
        );
        self.evals
            .iter_mut()
            .zip(&other.evals)
            .for_each(|(a, b)| *a -= b);
    }
}

impl<'a, 'b, F: PrimeField> Div<&'a Evaluations<F>> for &'b Evaluations<F> {
    type Output = Evaluations<F>;

    #[inline]
    fn div(self, other: &'a Evaluations<F>) -> Evaluations<F> {
        let mut result = self.clone();
        result /= other;
        result
    }
}

impl<'a, F: PrimeField> DivAssign<&'a Evaluations<F>> for Evaluations<F> {
    #[inline]
    fn div_assign(&mut self, other: &'a Evaluations<F>) {
        assert_eq!(
            self.domain.as_ref(),
            other.domain.as_ref(),
            "domains are unequal"
        );
        self.evals
            .iter_mut()
            .zip(&other.evals)
            .for_each(|(a, b)| *a /= b);
    }
}

impl<F: PrimeField> Clone for Evaluations<F> {
    fn clone(&self) -> Self {
        Self {
            evals: self.evals.clone(),
            domain: self.domain.clone(),
        }
    }
}

impl<F: PrimeField> PartialEq for Evaluations<F> {
    fn eq(&self, other: &Self) -> bool {
        self.evals.eq(&other.evals) && self.domain.eq(&other.domain)
    }
}
