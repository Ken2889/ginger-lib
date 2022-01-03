//! Submodule that implements the algebraic oracle proof, i.e. the information-theoretic
//! description of [Coboundary Marlin].
//!
//! We replace the sumcheck as used by [Marlin] with a coboundary criterion, which does
//! use degree bound proofs, and allow a more lightweight randomization for obtaining
//! zero-knowledge.
//!
//! [Marlin]: https://eprint.iacr.org/2019/1047
//! [Coboundary Marlin]: https://eprint.iacr.org/2021/930
use crate::{String, ToString, Vec};
use algebra::{get_best_evaluation_domain, DensePolynomial, EvaluationDomain, Evaluations};
use algebra::{Field, PrimeField};
use poly_commit::PolynomialLabel;
use r1cs_core::SynthesisError;
use std::marker::PhantomData;

use rayon::prelude::*;

/// Describes data structures and the algorithms used by the indexer.
pub mod indexer;
/// Describes data structures and the algorithms used by the interactive prover.
pub mod prover;
pub(crate) mod sparse_linear_algebra;
/// Describes data structures and the algorithms used by the interactive verifier.
pub mod verifier;

/// A helper struct to bundle the setup, prover and verifier functions for the
/// algebraic oracle proof from [HGB].
///
/// [HGB]: https://eprint.iacr.org/2021/930
pub struct IOP<F: Field> {
    field: PhantomData<F>,
}

impl<F: PrimeField> IOP<F> {
    /// The labels for the polynomials output by the indexer.
    #[rustfmt::skip]
    pub const INDEXER_POLYNOMIALS: [&'static str; 12] = [
        // Polynomials for A
        "a_row", "a_col", "a_row_col", "a_val_row_col",
        // Polynomials for B
        "b_row", "b_col", "b_row_col", "b_val_row_col",
        // Polynomials for C
        "c_row", "c_col", "c_row_col", "c_val_row_col",
    ];

    /// The labels for the polynomials output by the prover.
    #[rustfmt::skip]
    pub const PROVER_POLYNOMIALS: [&'static str; 7] = [
        // First sumcheck
        "w", "y_a", "y_b", "u_1", "h_1",
        // Second sumcheck
        "u_2", "h_2",
    ];

    /// An iterator over the polynomials output by the indexer and the prover.
    pub fn polynomial_labels() -> impl Iterator<Item = String> {
        Self::INDEXER_POLYNOMIALS
            .iter()
            .chain(&Self::PROVER_POLYNOMIALS)
            .map(|s| s.to_string())
    }

    /// The maximum degree of polynomials produced by the indexer and prover
    /// of this protocol.
    /// The number of the variables always includes the "one" variable addressing
    /// the constants of the arithmetic circuit.
    pub fn max_degree(
        num_constraints: usize,
        num_variables: usize,
        num_non_zero: usize,
        zk: bool,
    ) -> Result<usize, Error> {
        let num_formatted_variables = num_variables;
        let padded_matrix_dim = std::cmp::max(num_formatted_variables, num_constraints);
        let domain_h_size = get_best_evaluation_domain::<F>(padded_matrix_dim)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?
            .size();
        let domain_k_size = get_best_evaluation_domain::<F>(num_non_zero)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?
            .size();
        // The largest oracle degrees for the outer and inner sumcheck are
        //      deg h_1(X) = if zk { 2|H| } else { 2|H| - 1 }.
        //      deg h_2(X) = 3 * |K| - 4.
        // We hence return the max (deg h_1(X), deg h_2(X))
        Ok(*[
            2 * domain_h_size - (1 - zk as usize), // h_1 max degree
            3 * domain_k_size - 4,                 // h_2 max degree
        ]
        .iter()
        .max()
        .unwrap()) // This is really the degree not the number of coefficients
    }

    /// Format the public input according to the requirements of the constraint
    /// system
    pub(crate) fn format_public_input(public_input: &[F]) -> Vec<F> {
        let mut input = vec![F::one()];
        input.extend_from_slice(public_input);
        input
    }

    /// Take in a previously formatted public input and removes the formatting
    /// imposed by the constraint system.
    pub(crate) fn unformat_public_input(input: &[F]) -> Vec<F> {
        input[1..].to_vec()
    }

    /// Auxiliary function to verify the two sumcheck equations given the evalations
    /// via an `EvaluationProvider` (as defined below).
    // Note: To complete Marlin verification, one still has to check the opening proofs.
    #[allow(non_snake_case)]
    pub fn verify_sumchecks(
        public_input: &[F],
        evals: &poly_commit::Evaluations<F>,
        state: &verifier::VerifierState<F>,
    ) -> Result<(), Error> {
        let domain_h = &state.domain_h;
        let g_h = domain_h.group_gen();

        let domain_k = &state.domain_k;
        let g_k = domain_k.group_gen();
        let k_size_inv = domain_k.size_inv();

        let public_input = Self::format_public_input(public_input);
        let domain_x = get_best_evaluation_domain::<F>(public_input.len())
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        if state.first_round_msg.is_none() {
            return Err(Error::Other("First round message is empty".to_owned()));
        }

        let first_round_msg = state.first_round_msg.unwrap();
        let alpha = first_round_msg.alpha;
        let (eta_a, eta_b, eta_c) = first_round_msg.get_etas();

        let beta = match state.second_round_msg {
            Some(v) => v.beta,
            None => Err(Error::Other("Second round message is empty".to_owned()))?,
        };

        let gamma = match state.gamma {
            Some(v) => v,
            None => Err(Error::Other("Gamma is empty".to_owned()))?,
        };

        let v_H_at_alpha = domain_h.evaluate_vanishing_polynomial(alpha);
        let v_H_at_beta = domain_h.evaluate_vanishing_polynomial(beta);

        // Evaluate polynomials at beta
        let l_alpha_beta = state.domain_h.eval_lagrange_kernel(alpha, beta);
        let v_X_at_beta = domain_x.evaluate_vanishing_polynomial(beta);

        let w_at_beta = get_poly_eval(evals, "w".into(), beta)?;
        let y_a_at_beta = get_poly_eval(evals, "y_a".into(), beta)?;
        let y_b_at_beta = get_poly_eval(evals, "y_b".into(), beta)?;
        let u_1_at_beta = get_poly_eval(evals, "u_1".into(), beta)?;
        let u_1_at_g_beta = get_poly_eval(evals, "u_1".into(), g_h * beta)?;
        let h_1_at_beta = get_poly_eval(evals, "h_1".into(), beta)?;

        // we compute the public input polynomial using FFT
        // That is, we compute
        //  x_at_beta = <L(X,beta), inputs >_I
        // over the input domain I.
        let x_at_beta = domain_x
            .evaluate_all_lagrange_coefficients(beta)
            .into_iter()
            .zip(public_input) // note that zip automatically manages lower public_input lengths.
            .map(|(l, x)| l * &x)
            .fold(F::zero(), |x, y| x + &y);

        let y_eta_at_beta =
            eta_a * y_a_at_beta + eta_b * y_b_at_beta + eta_c * y_a_at_beta * y_b_at_beta;

        let v_1 =
            l_alpha_beta * y_eta_at_beta + u_1_at_g_beta - u_1_at_beta + h_1_at_beta * v_H_at_beta;

        let v_2 = x_at_beta + v_X_at_beta * w_at_beta;

        // We could safely consider v2 != 0, because it is overwhelmingly non-zero.
        // However, considering the case v2 == 0 is more elegant as is guarantees
        // the perfect completeness of the proving system.
        if v_2.is_zero() && !v_1.is_zero() {
            return Err(Error::VerificationEquationFailed(
                // TODO: find a more descriptive error name
                "Inner sumcheck".to_owned(),
            ));
        } else {
            // Inner sumcheck, using the provided evaluation values:
            //      a(X) == b(X)*(v/m + U_2(gX) - U_2(X)) + h_2(X)*(X^m-1)
            // at X=gamma, with
            //      b(X) = Product_{M=A*,B*,C*} (beta - row_M(X))*(alpha - col_M(X)),
            //      a(X) = (beta^n-1)*(alpha^n-1)*Sum_{M=A*,B*,C*} eta_M * val_M(X)*p_M(X),
            //      v = v_1/v_2,
            // where
            //      p_M(X) =  prod_{N!=M}(beta-row_N(X))(alpha-col_N(X))
            //             =  prod_{N!=M} (alpha*beta -alpha*row_N(X)-beta*col_N(X)+row.col_N(X))
            //
            // In order to avoid an expensive division by v_2, the following equality is
            // checked instead:
            //      v_2*a(X) == b(X)*(v_1/m + v_2*(U_2(gX) - U_2(X))) + v_2*h_2(X)*(X^m-1)
            // at X=gamma.
            let inner_sumcheck = {
                let alpha_beta = alpha * beta;

                // Evaluate polynomials at gamma

                let v_K_at_gamma = domain_k.evaluate_vanishing_polynomial(gamma);

                let u_2_at_gamma = get_poly_eval(evals, "u_2".into(), gamma)?;
                let u_2_at_g_gamma = get_poly_eval(evals, "u_2".into(), g_k * gamma)?;
                let h_2_at_gamma = get_poly_eval(evals, "h_2".into(), gamma)?;

                let a_row_at_gamma = get_poly_eval(evals, "a_row".into(), gamma)?;
                let a_col_at_gamma = get_poly_eval(evals, "a_col".into(), gamma)?;
                let a_row_col_at_gamma = get_poly_eval(evals, "a_row_col".into(), gamma)?;
                let a_val_row_col_at_gamma = get_poly_eval(evals, "a_val_row_col".into(), gamma)?;

                let b_row_at_gamma = get_poly_eval(evals, "b_row".into(), gamma)?;
                let b_col_at_gamma = get_poly_eval(evals, "b_col".into(), gamma)?;
                let b_row_col_at_gamma = get_poly_eval(evals, "b_row_col".into(), gamma)?;
                let b_val_row_col_at_gamma = get_poly_eval(evals, "b_val_row_col".into(), gamma)?;

                let c_row_at_gamma = get_poly_eval(evals, "c_row".into(), gamma)?;
                let c_col_at_gamma = get_poly_eval(evals, "c_col".into(), gamma)?;
                let c_row_col_at_gamma = get_poly_eval(evals, "c_row_col".into(), gamma)?;
                let c_val_row_col_at_gamma = get_poly_eval(evals, "c_val_row_col".into(), gamma)?;

                // The denominator terms, using row.col_M(X)

                let a_denom_at_gamma =
                    alpha_beta - (beta * a_row_at_gamma) - (alpha * a_col_at_gamma)
                        + a_row_col_at_gamma;
                let b_denom_at_gamma =
                    alpha_beta - (beta * b_row_at_gamma) - (alpha * b_col_at_gamma)
                        + b_row_col_at_gamma;
                let c_denom_at_gamma =
                    alpha_beta - (beta * c_row_at_gamma) - (alpha * c_col_at_gamma)
                        + c_row_col_at_gamma;

                // b(X) at X=gamma
                let b_at_gamma = a_denom_at_gamma * b_denom_at_gamma * c_denom_at_gamma;
                let b_expr_at_gamma =
                    b_at_gamma * (v_2 * (u_2_at_g_gamma - u_2_at_gamma) + &(v_1 * k_size_inv));

                let mut inner_sumcheck =
                    (eta_a * b_denom_at_gamma * c_denom_at_gamma * a_val_row_col_at_gamma)
                        + (eta_b * a_denom_at_gamma * c_denom_at_gamma * b_val_row_col_at_gamma)
                        + (eta_c * b_denom_at_gamma * a_denom_at_gamma * c_val_row_col_at_gamma);

                inner_sumcheck *= v_2;
                inner_sumcheck *= v_H_at_alpha * v_H_at_beta * domain_h.size_inv().square();
                inner_sumcheck -= b_expr_at_gamma;
                inner_sumcheck -= v_2 * v_K_at_gamma * h_2_at_gamma;
                inner_sumcheck
            };

            if !inner_sumcheck.is_zero() {
                return Err(Error::VerificationEquationFailed(
                    "Inner sumcheck".to_owned(),
                ));
            }
        }

        Ok(())
    }
}

fn get_poly_eval<F: Field>(
    evals: &poly_commit::Evaluations<F>,
    label: PolynomialLabel,
    point: F,
) -> Result<F, Error> {
    let key = (label.clone(), point);
    evals.get(&key).copied().ok_or(Error::MissingEval(label))
}

/// Describes the failure modes of the IOP scheme.
#[derive(Debug)]
pub enum Error {
    /// During verification, a required evaluation is missing
    MissingEval(String),
    /// One of IOP verification equations has failed.
    VerificationEquationFailed(String),
    /// The instance generated during proving does not match that in the index.
    InstanceDoesNotMatchIndex,
    /// An error occurred during constraint generation.
    ConstraintSystemError(SynthesisError),
    /// The given coboundary polynomial evaluations over a domain don't sum to zero.
    InvalidCoboundaryPolynomial,
    /// Other error
    Other(String),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::MissingEval(err) => write!(f, "Evaluation {} missing", err),
            Error::VerificationEquationFailed(err) => {
                write!(f, "Verification equation {} failed", err)
            }
            Error::InstanceDoesNotMatchIndex => write!(
                f,
                "The instance generated during proving does not match that in the index"
            ),
            Error::ConstraintSystemError(err) => write!(f, "{}", err),
            Error::InvalidCoboundaryPolynomial => write!(
                f,
                "The given coboundary polynomial evaluations over a domain don't sum to zero"
            ),
            Error::Other(message) => write!(f, "{}", message),
        }
    }
}

impl std::error::Error for Error {}

impl From<SynthesisError> for Error {
    fn from(other: SynthesisError) -> Self {
        Error::ConstraintSystemError(other)
    }
}

/// The Lagrange kernel
/// `L_H(X,Y) = 1/|H| * (Y*V_H(X) - X*V_H(Y)) / (X-Y)`
/// where `V_H()` is the vanishing polynomial over `H`.
pub trait LagrangeKernel<F: PrimeField> {
    /// Succinct evaluation of `L(x,y)`.
    fn eval_lagrange_kernel(&self, x: F, y: F) -> F;

    /// Domain evaluation of `L(X,y)`, for `y` not being from `H`.
    fn domain_eval_lagrange_kernel(&self, y: F) -> Result<Vec<F>, Error>;
}

impl<F: PrimeField> LagrangeKernel<F> for Box<dyn EvaluationDomain<F>> {
    // L_H(x,y) = (y*V_H(x) - x*V_H(y)) / (x-y) for x!=y,
    // L_H(x,x) = (1 + (n - 1) * x^n) / n.
    // In particular, if both x and y belong to H,
    // L_H(x,y) = 0 for x!=y
    // L_H(x,x) = 1
    fn eval_lagrange_kernel(&self, x: F, y: F) -> F {
        let n = self.size_as_field_element();
        let n_inv = self.size_inv();
        if x != y {
            n_inv
                * (y * self.evaluate_vanishing_polynomial(x)
                    - x * self.evaluate_vanishing_polynomial(y))
                / (x - y)
        } else {
            n_inv * (F::one() + (n - F::one()) * x.pow(&[(self.size()) as u64]))
        }
    }

    // Compute L_H(X,y) = -(y^n - 1) / n * X / (X-y) using batch inversion and index reversion.
    // Costs essentially a vector product and a batch inversion.
    fn domain_eval_lagrange_kernel(&self, y: F) -> Result<Vec<F>, Error> {
        let v_at_y = self.evaluate_vanishing_polynomial(y);
        if v_at_y.is_zero() {
            Err(Error::Other(
                "argument should not belong to the domain".to_owned(),
            ))
        } else {
            let c1 = -self.size_as_field_element() / v_at_y;
            let c2 = -c1 * y;
            let mut inverses: Vec<_> = self.elements().map(|x| c1 + c2 * x).collect();
            // Index reversion for batch inverting X.
            inverses[1..].reverse();
            algebra::fields::batch_inversion(&mut inverses);
            Ok(inverses)
        }
    }
}

/// A boundary polynomial `U(X)` for a polynomial `p(X)` over a cyclic subgroup
/// of `F` is subject to `U(gX)-U(X) = p(X) mod (X^n-1)`, where `g` is a generator
/// for the cyclic sugroup, and `n` is  its order.
// TODO: Why do we need a separate struct for it? It is as any other polynomial.
pub struct BoundaryPolynomial<F: PrimeField> {
    /// The boundary polynomial.
    poly: DensePolynomial<F>,
    /// Evaluations of the boundary polynomial over the D domain.
    evals: Evaluations<F>,
}

impl<F: PrimeField> Clone for BoundaryPolynomial<F> {
    fn clone(&self) -> Self {
        let cloned_evals = Evaluations::<F>::from_vec_and_domain(
            self.evals.evals.clone(),
            self.evals.domain.clone_and_box(),
        );
        Self {
            poly: self.poly.clone(),
            evals: cloned_evals,
        }
    }
}

impl<F: PrimeField> BoundaryPolynomial<F> {
    /// Construct a `self` instance from a boundary polynomial.
    pub fn new(
        boundary_poly: DensePolynomial<F>,
        domain: Box<dyn EvaluationDomain<F>>,
    ) -> Result<Self, Error> {
        let poly_evals = (&boundary_poly).evaluate_over_domain_by_ref(domain);

        Ok(Self {
            poly: boundary_poly,
            evals: poly_evals,
        })
    }

    /// Return the underlying boundary polynomial, consuming `self`.
    pub fn polynomial(self) -> DensePolynomial<F> {
        self.poly
    }

    /// Borrow the underlying boundary polynomial.
    pub fn polynomial_ref(&self) -> &DensePolynomial<F> {
        &self.poly
    }

    /// Return the evaluations over D of the boundary polynomial, consuming `self`.
    pub fn evals(self) -> Evaluations<F> {
        self.evals
    }

    /// Return the evaluations over D of the boundary polynomial, borrowing `self`.
    pub fn evals_ref(&self) -> &Evaluations<F> {
        &self.evals
    }

    /// Compute the boundary polynomial given a coboundary polynomial
    /// evaluations `poly_evals` over the elements of a domain D.
    pub fn from_coboundary_polynomial_evals(poly_evals: Evaluations<F>) -> Result<Self, Error> {
        let domain = poly_evals.domain;
        let evals = poly_evals.evals;

        // Z(1) = 0, or any arbitrary value
        let mut z_evals = Vec::with_capacity(evals.len());
        z_evals.push(F::zero());

        // The other coefficients of the boundary polynomial will be the cumulative sum
        // of the evaluations of the coboundary poly over the domain, e.g.:
        // Z(1) = 0
        // Z(g) = Z(1) + p'(1)
        // Z(g^2) = Z(1) + p'(1) + p'(g)
        // ...
        // Z(g^(|H| - 1) )= Z(1) + p(1) + p'(g) + p'(g^2) + .... + p'(g^( |H| - 2 )) ,
        // and finally
        // Z(g^|H|) = 0 = p'(g) + p'(g^2) + ... + p'(g^|H - 1|) + p'(g^|H|), will be excluded
        let mut cum_sum_poly_evals = evals
            .into_iter()
            .scan(F::zero(), |acc, x| {
                *acc += x;
                Some(*acc)
            })
            .collect::<Vec<_>>();

        // Poly evals over domain should sum to zero
        if cum_sum_poly_evals[cum_sum_poly_evals.len() - 1] != F::zero() {
            return Err(Error::InvalidCoboundaryPolynomial);
        }

        z_evals.append(&mut cum_sum_poly_evals);
        z_evals.pop(); // Pop the last zero

        let z_evals = Evaluations::from_vec_and_domain(z_evals, domain);

        let z_poly = z_evals.interpolate_by_ref();

        Ok(Self {
            poly: z_poly,
            evals: z_evals,
        })
    }

    /// Compute the boundary polynomial given a coboundary polynomial `poly`
    /// over a domain `domain`.
    /// Coboundaries `p(X)` are characterized by the domain sum
    /// `sum_x p(x) = 0 `.
    pub fn from_coboundary_polynomial(
        poly: &DensePolynomial<F>,
        domain: Box<dyn EvaluationDomain<F>>,
    ) -> Result<Self, Error> {
        Self::from_coboundary_polynomial_evals(poly.evaluate_over_domain_by_ref(domain))
    }

    /// Given the domain evaluations `poly_evals` of a polynomial `p(X)` with non-zero
    /// domain sum `v = Sum_{x in D} p(x)`, construct a boundary polynomial U(X) for the
    /// centered polynomial `p'(X) = p(X) - v/|D|`, and return both `Z(X)` and `v/|D|`.
    pub fn from_non_coboundary_polynomial_evals(
        poly_evals: Evaluations<F>,
    ) -> Result<(Self, F), Error> {
        let v = poly_evals.evals.par_iter().sum::<F>();
        let v_over_domain = v * poly_evals.domain.size_inv();
        let normalized_poly_evals = Evaluations::from_vec_and_domain(
            poly_evals
                .evals
                .into_par_iter()
                .map(|eval| eval - v_over_domain)
                .collect(),
            poly_evals.domain,
        );
        let boundary_poly = Self::from_coboundary_polynomial_evals(normalized_poly_evals)?;
        Ok((boundary_poly, v_over_domain))
    }

    /// The same as `fn from_non_coboundary_polynomial_evals`, given the coefficents of
    /// the polynomial `poly` instead.
    pub fn from_non_coboundary_polynomial(
        poly: &DensePolynomial<F>,
        domain: Box<dyn EvaluationDomain<F>>,
    ) -> Result<(Self, F), Error> {
        Self::from_non_coboundary_polynomial_evals(poly.evaluate_over_domain_by_ref(domain))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use algebra::UniformRand;
    use algebra::{fields::tweedle::fr::Fr, Group};
    use algebra::{get_best_evaluation_domain, DenseOrSparsePolynomial, DensePolynomial};
    use rand::thread_rng;

    #[test]
    fn eval_on_domain_with_same_inputs() {
        for domain_size in 1..10 {
            let domain = get_best_evaluation_domain::<Fr>(1 << domain_size).unwrap();
            for x in domain.elements() {
                let l_xx = domain.eval_lagrange_kernel(x, x);
                assert_eq!(l_xx, Fr::one());
            }
        }
    }

    #[test]
    fn eval_on_domain_with_different_inputs() {
        for domain_size in 1..5 {
            let domain = get_best_evaluation_domain::<Fr>(1 << domain_size).unwrap();
            for x in domain.elements() {
                for y in domain.elements() {
                    if x != y {
                        let l_xy = domain.eval_lagrange_kernel(x, y);
                        assert_eq!(l_xy, Fr::zero());
                    }
                }
            }
        }
    }

    #[test]
    fn domain_eval_with_input_inside_domain() {
        for domain_size in 1..10 {
            let domain = get_best_evaluation_domain::<Fr>(1 << domain_size).unwrap();
            for y in domain.elements() {
                let result = domain.domain_eval_lagrange_kernel(y);
                assert!(result.is_err());
            }
        }
    }

    #[test]
    fn domain_eval_with_input_outside_domain() {
        let rng = &mut thread_rng();
        for domain_size in 1..10 {
            let domain = get_best_evaluation_domain::<Fr>(1 << domain_size).unwrap();
            let y = Fr::rand(rng);
            let manual: Vec<_> = domain
                .elements()
                .map(|x| domain.eval_lagrange_kernel(x, y))
                .collect();
            let fast = domain.domain_eval_lagrange_kernel(y).unwrap();
            assert_eq!(fast, manual);
        }
    }

    #[test]
    fn test_summation() {
        let rng = &mut thread_rng();
        let size = 1 << 4;
        let domain = get_best_evaluation_domain::<Fr>(1 << 4).unwrap();
        let size_as_fe = domain.size_as_field_element();
        let poly = DensePolynomial::rand(size, rng);

        let mut sum: Fr = Fr::zero();
        for eval in domain.elements().map(|e| poly.evaluate(e)) {
            sum += eval;
        }
        let first = poly.coeffs[0] * size_as_fe;
        let last = *poly.coeffs.last().unwrap() * size_as_fe;
        println!("sum: {:?}", sum);
        println!("a_0: {:?}", first);
        println!("a_n: {:?}", last);
        println!("first + last: {:?}\n", first + last);
        assert_eq!(sum, first + last);
    }

    #[test]
    fn test_alternator_polynomial() {
        use algebra::Evaluations;
        let domain_k = get_best_evaluation_domain::<Fr>(1 << 4).unwrap();
        let domain_h = get_best_evaluation_domain::<Fr>(1 << 3).unwrap();
        let domain_h_elems = domain_h
            .elements()
            .collect::<std::collections::HashSet<_>>();
        let alternator_poly_evals = domain_k
            .elements()
            .map(|e| {
                if domain_h_elems.contains(&e) {
                    Fr::one()
                } else {
                    Fr::zero()
                }
            })
            .collect();
        let v_k: DenseOrSparsePolynomial<_> = domain_k.vanishing_polynomial().into();
        let v_h: DenseOrSparsePolynomial<_> = domain_h.vanishing_polynomial().into();
        let (divisor, remainder) = v_k.divide_with_q_and_r(&v_h).unwrap();
        assert!(remainder.is_zero());
        println!("Divisor: {:?}", divisor);
        println!(
            "{:#?}",
            divisor
                .coeffs
                .iter()
                .filter_map(|f| if !f.is_zero() {
                    Some(f.into_repr())
                } else {
                    None
                })
                .collect::<Vec<_>>()
        );

        for e in domain_h.elements() {
            println!("{:?}", divisor.evaluate(e));
        }
        // Let p = v_K / v_H;
        // The alternator polynomial is p * t, where t is defined as
        // the LDE of p(h)^{-1} for all h in H.
        //
        // Because for each h in H, p(h) equals a constant c, we have that t
        // is the constant polynomial c^{-1}.
        //
        // Q: what is the constant c? Why is p(h) constant? What is the easiest
        // way to calculate c?
        let alternator_poly =
            Evaluations::from_vec_and_domain(alternator_poly_evals, domain_k).interpolate();
        let (quotient, remainder) = DenseOrSparsePolynomial::from(alternator_poly.clone())
            .divide_with_q_and_r(&DenseOrSparsePolynomial::from(divisor))
            .unwrap();
        assert!(remainder.is_zero());
        println!("quotient: {:?}", quotient);
        println!(
            "{:#?}",
            quotient
                .coeffs
                .iter()
                .filter_map(|f| if !f.is_zero() {
                    Some(f.into_repr())
                } else {
                    None
                })
                .collect::<Vec<_>>()
        );

        println!("{:?}", alternator_poly);
    }

    #[test]
    fn test_coboundary_polynomial() {
        let rng = &mut thread_rng();

        for domain_size in 1..20 {
            let domain = get_best_evaluation_domain::<Fr>(1 << domain_size).unwrap();
            let size = domain.size();

            // Get random poly
            let p = DensePolynomial::<Fr>::rand(size, rng);

            // Compute the boundary polynomial Z
            let (z_poly, v) =
                BoundaryPolynomial::from_non_coboundary_polynomial(&p, domain.clone()).unwrap();
            let z_evals = z_poly.evals();

            // Compute the coboundary polynomial P'(X) = P(X) - v/|domain|
            let mut p_coeffs = p.coeffs;
            p_coeffs[0] -= v;
            let p_prime = DensePolynomial::from_coefficients_vec(p_coeffs);

            // Compute the evaluations of p_prime over domain
            let p_prime_evals = p_prime.evaluate_over_domain(domain);

            // Test that indeed Z is a boundary polynomial, e.g. :
            // Z(g^i) - z(g^i-1) == p'(g^i) <=> Z(g*x) - Z(x) = p'(x) for each x in domain
            for i in 1..size {
                assert_eq!(
                    z_evals[i] - z_evals[i - 1],
                    p_prime_evals[i - 1],
                    "{}",
                    format!("Equality {} failed on domain size 2^{}", i, size)
                );
            }
        }
    }
}
