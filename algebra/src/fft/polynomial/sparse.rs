//! A sparse polynomial represented in coefficient form.

use std::fmt;

use crate::DensePolynomial;
use crate::{DenseOrSparsePolynomial, EvaluationDomain, Evaluations};
use crate::{Field, PrimeField};

/// Stores a sparse polynomial in coefficient form.
#[derive(Clone, PartialEq, Eq, Hash, Default)]
pub struct SparsePolynomial<F: Field> {
    /// The coefficient a_i of `x^i` is stored as (i, a_i) in `self.coeffs`.
    /// the entries in `self.coeffs` are sorted in increasing order of `i`.
    pub coeffs: Vec<(usize, F)>,
}

impl<F: Field> fmt::Debug for SparsePolynomial<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        for (i, coeff) in self.coeffs.iter().filter(|(_, c)| !c.is_zero()) {
            if *i == 0 {
                write!(f, "\n{:?}", coeff)?;
            } else if *i == 1 {
                write!(f, " + \n{:?} * x", coeff)?;
            } else {
                write!(f, " + \n{:?} * x^{}", coeff, i)?;
            }
        }
        Ok(())
    }
}

impl<F: Field> SparsePolynomial<F> {
    /// Returns the zero polynomial.
    pub fn zero() -> Self {
        Self { coeffs: Vec::new() }
    }

    /// Checks if the given polynomial is zero.
    pub fn is_zero(&self) -> bool {
        self.coeffs.len() == 0 || self.coeffs.iter().all(|(_, c)| c.is_zero())
    }

    /// Constructs a new polynomial from a list of coefficients.
    pub fn from_coefficients_slice(coeffs: &[(usize, F)]) -> Self {
        Self::from_coefficients_vec(coeffs.to_vec())
    }

    /// Constructs a new polynomial from a list of coefficients.
    pub fn from_coefficients_vec(mut coeffs: Vec<(usize, F)>) -> Self {
        // While there are zeros at the end of the coefficient vector, pop them off.
        while coeffs.last().map_or(false, |(_, c)| c.is_zero()) {
            coeffs.pop();
        }

        Self { coeffs }
    }

    /// Returns the degree of the polynomial.
    pub fn degree(&self) -> usize {
        if self.is_zero() {
            0
        } else {
            debug_assert!(self.coeffs.last().map_or(false, |(_, c)| !c.is_zero()));
            self.coeffs.last().unwrap().0
        }
    }

    /// Evaluates `self` at the given `point` in the field.
    pub fn evaluate(&self, point: F) -> F {
        if self.is_zero() {
            return F::zero();
        }
        let mut total = F::zero();
        for (i, c) in &self.coeffs {
            total += &(*c * &point.pow(&[*i as u64]));
        }
        total
    }

    /// Perform a naive n^2 multiplicatoin of `self` by `other`.
    pub fn mul(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            SparsePolynomial::zero()
        } else {
            let mut result = std::collections::HashMap::new();
            for (i, self_coeff) in self.coeffs.iter() {
                for (j, other_coeff) in other.coeffs.iter() {
                    let cur_coeff = result.entry(i + j).or_insert(F::zero());
                    *cur_coeff += &(*self_coeff * other_coeff);
                }
            }
            let mut result = result.into_iter().collect::<Vec<_>>();
            result.sort_by(|a, b| a.0.cmp(&b.0));
            SparsePolynomial::from_coefficients_vec(result)
        }
    }
}

impl<F: PrimeField> SparsePolynomial<F> {
    /// Evaluate `self` over `domain`.
    pub fn evaluate_over_domain_by_ref(
        &self,
        domain: Box<dyn EvaluationDomain<F>>,
    ) -> Evaluations<F> {
        let poly: DenseOrSparsePolynomial<'_, F> = self.into();
        DenseOrSparsePolynomial::<F>::evaluate_over_domain(poly, domain)
    }

    /// Evaluate `self` over `domain`.
    pub fn evaluate_over_domain(self, domain: Box<dyn EvaluationDomain<F>>) -> Evaluations<F> {
        let poly: DenseOrSparsePolynomial<'_, F> = self.into();
        DenseOrSparsePolynomial::<F>::evaluate_over_domain(poly, domain)
    }
}

impl<F: Field> Into<DensePolynomial<F>> for SparsePolynomial<F> {
    fn into(self) -> DensePolynomial<F> {
        let mut other = vec![F::zero(); self.degree() + 1];
        for (i, coeff) in self.coeffs {
            other[i] = coeff;
        }
        DensePolynomial::from_coefficients_vec(other)
    }
}

#[cfg(all(test, feature = "bls12_381"))]
mod tests {
    use crate::fields::bls12_381::fr::Fr;
    use crate::Field;
    use crate::{get_best_evaluation_domain, DensePolynomial, SparsePolynomial};

    #[test]
    fn evaluate_over_domain() {
        for size in 2..18 {
            let domain_size = 1 << size;
            let domain = get_best_evaluation_domain::<Fr>(domain_size).unwrap();
            let two = Fr::one() + &Fr::one();
            let sparse_poly = SparsePolynomial::from_coefficients_vec(vec![(0, two), (1, two)]);
            let evals1 = sparse_poly.evaluate_over_domain_by_ref(domain.clone());

            let dense_poly: DensePolynomial<Fr> = sparse_poly.into();
            let evals2 = dense_poly.clone().evaluate_over_domain(domain);
            assert_eq!(evals1.clone().interpolate(), evals2.clone().interpolate());
            assert_eq!(evals1.interpolate(), dense_poly);
            assert_eq!(evals2.interpolate(), dense_poly);
        }
    }
}
