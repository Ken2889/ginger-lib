use crate::{String, ToString, Vec};
use algebra::{get_best_evaluation_domain, DensePolynomial, EvaluationDomain, Evaluations};
use algebra::{Field, PrimeField};
use poly_commit::{LabeledPolynomial, PolynomialLabel};
use r1cs_core::SynthesisError;
use std::{borrow::Borrow, marker::PhantomData};

use rayon::prelude::*;

pub(crate) mod constraint_systems;
/// Describes data structures and the algorithms used by the AHP indexer.
pub mod indexer;
/// Describes data structures and the algorithms used by the AHP prover.
pub mod prover;
/// Describes data structures and the algorithms used by the AHP verifier.
pub mod verifier;

/// The algebraic holographic proof defined in [CHMMVW19](https://eprint.iacr.org/2019/1047),
/// modified as described in our white paper (TODO: add link):
/// We adapt the grand product argument of [PLONK](https://eprint.iacr.org/2019/953), which is a
/// coboundary criterion for cocycles over the group action on the domain, and prove the both outer
/// and inner sumcheck without low degree extension of the polynomials in question.
/// This allows a more lightweight randomization to obtain zero-knowledge, and moreover gets
/// rid of proving degree bounds.
pub struct AHPForR1CS<F: Field> {
    field: PhantomData<F>,
}

impl<F: PrimeField> AHPForR1CS<F> {
    /// The labels for the polynomials output by the AHP indexer.
    #[rustfmt::skip]
    pub const INDEXER_POLYNOMIALS: [&'static str; 12] = [
        // Polynomials for A
        "a_row", "a_col", "a_val", "a_row_col",
        // Polynomials for B
        "b_row", "b_col", "b_val", "b_row_col",
        // Polynomials for C
        "c_row", "c_col", "c_val", "c_row_col",
    ];

    /// The labels for the polynomials output by the AHP prover.
    #[rustfmt::skip]
    pub const PROVER_POLYNOMIALS: [&'static str; 8] = [
        // First sumcheck
        "w", "z_a", "z_b", "t", "z_1", "h_1",
        // Second sumcheck
        "z_2", "h_2",
    ];

    pub(crate) fn polynomial_labels() -> impl Iterator<Item = String> {
        Self::INDEXER_POLYNOMIALS
            .iter()
            .chain(&Self::PROVER_POLYNOMIALS)
            .map(|s| s.to_string())
    }

    /// Check that the (formatted) public input is of the form 2^n for some integer n.
    pub fn num_formatted_public_inputs_is_admissible(num_inputs: usize) -> bool {
        num_inputs.count_ones() == 1
    }

    /// Check that the (formatted) public input is of the form 2^n for some integer n.
    pub fn formatted_public_input_is_admissible(input: &[F]) -> bool {
        Self::num_formatted_public_inputs_is_admissible(input.len())
    }

    /// The maximum degree of polynomials produced by the indexer and prover
    /// of this protocol.
    /// The number of the variables must include the "one" variable. That is, it
    /// must be with respect to the number of formatted public inputs.
    pub fn max_degree(
        num_constraints: usize,
        num_variables: usize,
        num_non_zero: usize,
        zk: bool,
    ) -> Result<usize, Error> {
        let padded_matrix_dim =
            constraint_systems::padded_matrix_dim(num_variables, num_constraints);
        let domain_h_size = get_best_evaluation_domain::<F>(padded_matrix_dim)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?
            .size();
        let domain_k_size = get_best_evaluation_domain::<F>(num_non_zero)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?
            .size();
        // If zk is chosen, we secure the witness-related polynomials to leak no
        // information when queried twice, since the multi-point multi-poly open
        // from Boneh et al samples an extra query point.
        let zk_bound = if zk { 2 } else { 0 };
        Ok(*[
            2 * domain_h_size + 2 * zk_bound - 3, // h_1 max degree
            domain_h_size - 1,                    // For exceptional case of high zk_bound
            3 * domain_k_size - 4,                // h_2 max degree
        ]
        .iter()
        .max()
        .unwrap()) // This is really the degree not the number of coefficients
    }

    /// Get all the strict degree bounds enforced in the AHP.
    pub fn get_degree_bounds(_info: &indexer::IndexInfo<F>) -> [usize; 2] {
        [0usize; 2]
    }

    /// Does the algebraic checks on the opening values (inner and outer sumcheck).
    /// To complete Marlin verification, one still has to check the opening proofs.
    #[allow(non_snake_case)]
    pub fn verify_sumchecks<E>(
        public_input: &[F],
        evals: &E,
        state: &verifier::VerifierState<F>,
    ) -> Result<(), Error>
    where
        E: EvaluationsProvider<F>,
    {
        let domain_h = &state.domain_h;
        let g_h = domain_h.group_gen();

        let domain_k = &state.domain_k;
        let g_k = domain_k.group_gen();
        let k_size = domain_k.size_as_field_element();

        let public_input = constraint_systems::format_public_input(public_input);
        if !Self::formatted_public_input_is_admissible(&public_input) {
            return Err(Error::InvalidPublicInputLength);
        }
        let x_domain = get_best_evaluation_domain::<F>(public_input.len())
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        if state.first_round_msg.is_none() {
            return Err(Error::Other("First round message is empty".to_owned()));
        }

        let first_round_msg = state.first_round_msg.unwrap();
        let alpha = first_round_msg.alpha;
        let eta_a = first_round_msg.eta_a;
        let eta_b = first_round_msg.eta_b;
        let eta_c = first_round_msg.eta_c;

        let beta = match state.second_round_msg {
            Some(v) => v.beta,
            None => return Err(Error::Other("Second round message is empty".to_owned())),
        };

        let gamma = match state.gamma {
            Some(v) => v,
            None => return Err(Error::Other("Gamma is empty".to_owned())),
        };

        let v_H_at_alpha = domain_h.evaluate_vanishing_polynomial(alpha);
        let v_H_at_beta = domain_h.evaluate_vanishing_polynomial(beta);

        let t_at_beta = evals.get_poly_eval("t".into(), beta)?;

        // Outer sumcheck using the provided evaluation values:
        let outer_sumcheck = {
            // Evaluate polynomials at beta
            let r_alpha_at_beta = state
                .domain_h
                .eval_unnormalized_bivariate_lagrange_poly(alpha, beta);
            let v_X_at_beta = x_domain.evaluate_vanishing_polynomial(beta);

            let w_at_beta = evals.get_poly_eval("w".into(), beta)?;
            let z_a_at_beta = evals.get_poly_eval("z_a".into(), beta)?;
            let z_b_at_beta = evals.get_poly_eval("z_b".into(), beta)?;
            let z_1_at_beta = evals.get_poly_eval("z_1".into(), beta)?;
            let z_1_at_g_beta = evals.get_poly_eval("z_1".into(), g_h * beta)?;
            let h_1_at_beta = evals.get_poly_eval("h_1".into(), beta)?;

            // we compute the public input polynomial using FFT
            let x_at_beta = x_domain
                .evaluate_all_lagrange_coefficients(beta)
                .into_iter()
                .zip(public_input)
                .map(|(l, x)| l * &x)
                .fold(F::zero(), |x, y| x + &y);

            // Outer sumcheck, using
            // z(X) = x(X) + w(X) * v_X(X)
            (r_alpha_at_beta * (eta_a + eta_c * z_b_at_beta) * z_a_at_beta)
                + (r_alpha_at_beta * eta_b * z_b_at_beta)
                - (t_at_beta * v_X_at_beta * w_at_beta)
                - (t_at_beta * x_at_beta)
                - (v_H_at_beta * h_1_at_beta)
                + z_1_at_beta
                - z_1_at_g_beta
        };

        if !outer_sumcheck.is_zero() {
            return Err(Error::VerificationEquationFailed(
                "Outer sumcheck".to_owned(),
            ));
        }

        //  Inner sumcheck, using the provided evaluation values
        let inner_sumcheck = {
            let beta_alpha = beta * alpha;

            // Evaluate polynomials at gamma

            let v_K_at_gamma = domain_k.evaluate_vanishing_polynomial(gamma);

            let z_2_at_gamma = evals.get_poly_eval("z_2".into(), gamma)?;
            let z_2_at_g_gamma = evals.get_poly_eval("z_2".into(), g_k * gamma)?;
            let h_2_at_gamma = evals.get_poly_eval("h_2".into(), gamma)?;

            let a_row_at_gamma = evals.get_poly_eval("a_row".into(), gamma)?;
            let a_col_at_gamma = evals.get_poly_eval("a_col".into(), gamma)?;
            let a_row_col_at_gamma = evals.get_poly_eval("a_row_col".into(), gamma)?;
            let a_val_at_gamma = evals.get_poly_eval("a_val".into(), gamma)?;

            let b_row_at_gamma = evals.get_poly_eval("b_row".into(), gamma)?;
            let b_col_at_gamma = evals.get_poly_eval("b_col".into(), gamma)?;
            let b_row_col_at_gamma = evals.get_poly_eval("b_row_col".into(), gamma)?;
            let b_val_at_gamma = evals.get_poly_eval("b_val".into(), gamma)?;

            let c_row_at_gamma = evals.get_poly_eval("c_row".into(), gamma)?;
            let c_col_at_gamma = evals.get_poly_eval("c_col".into(), gamma)?;
            let c_row_col_at_gamma = evals.get_poly_eval("c_row_col".into(), gamma)?;
            let c_val_at_gamma = evals.get_poly_eval("c_val".into(), gamma)?;

            // Linearization of the inner sumcheck equation

            let a_denom_at_gamma = beta_alpha - (alpha * a_row_at_gamma) - (beta * a_col_at_gamma)
                + a_row_col_at_gamma;
            let b_denom_at_gamma = beta_alpha - (alpha * b_row_at_gamma) - (beta * b_col_at_gamma)
                + b_row_col_at_gamma;
            let c_denom_at_gamma = beta_alpha - (alpha * c_row_at_gamma) - (beta * c_col_at_gamma)
                + c_row_col_at_gamma;

            let b_at_gamma = a_denom_at_gamma * b_denom_at_gamma * c_denom_at_gamma;
            let b_expr_at_gamma =
                b_at_gamma * (z_2_at_g_gamma - z_2_at_gamma + &(t_at_beta / &k_size));

            let mut inner_sumcheck = (eta_a * b_denom_at_gamma * c_denom_at_gamma * a_val_at_gamma)
                + (eta_b * a_denom_at_gamma * c_denom_at_gamma * b_val_at_gamma)
                + (eta_c * b_denom_at_gamma * a_denom_at_gamma * c_val_at_gamma);

            inner_sumcheck *= v_H_at_alpha * v_H_at_beta;
            inner_sumcheck -= b_expr_at_gamma;
            inner_sumcheck -= v_K_at_gamma * h_2_at_gamma;
            inner_sumcheck
        };

        if !inner_sumcheck.is_zero() {
            return Err(Error::VerificationEquationFailed(
                "Inner sumcheck".to_owned(),
            ));
        }

        Ok(())
    }
}

/// Abstraction that provides evaluations of polynomials
pub trait EvaluationsProvider<F: Field> {
    /// Get the evaluation of a polynomial given its `label` at `point`.
    fn get_poly_eval(&self, label: PolynomialLabel, point: F) -> Result<F, Error>;
}

impl<'a, F: Field> EvaluationsProvider<F> for poly_commit::Evaluations<'a, F> {
    fn get_poly_eval(&self, label: PolynomialLabel, point: F) -> Result<F, Error> {
        let key = (label.clone(), point);
        self.get(&key).copied().ok_or(Error::MissingEval(label))
    }
}

impl<'a, F: Field, T: Borrow<LabeledPolynomial<F>>> EvaluationsProvider<F> for Vec<T> {
    fn get_poly_eval(&self, _label: PolynomialLabel, _point: F) -> Result<F, Error> {
        unimplemented!()
    }
}

/// Describes the failure modes of the AHP scheme.
#[derive(Debug)]
pub enum Error {
    /// During verification, a required evaluation is missing
    MissingEval(String),
    /// One of AHP verification equations has failed.
    VerificationEquationFailed(String),
    /// The number of public inputs is incorrect.
    InvalidPublicInputLength,
    /// The instance generated during proving does not match that in the index.
    InstanceDoesNotMatchIndex,
    /// Currently we only support square constraint matrices.
    NonSquareMatrix,
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
            Error::InvalidPublicInputLength => {
                write!(f, "The number of public inputs is incorrect")
            }
            Error::InstanceDoesNotMatchIndex => write!(
                f,
                "The instance generated during proving does not match that in the index"
            ),
            Error::NonSquareMatrix => {
                write!(f, "Currently we only support square constraint matrices")
            }
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

/// The derivative of the vanishing polynomial
pub trait UnnormalizedBivariateLagrangePoly<F: PrimeField> {
    /// Evaluate the polynomial
    fn eval_unnormalized_bivariate_lagrange_poly(&self, x: F, y: F) -> F;

    /// Evaluate over a batch of inputs
    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(&self, x: F) -> Vec<F>;

    /// Evaluate the magic polynomial over `self`
    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_same_inputs(&self) -> Vec<F>;
}

impl<F: PrimeField> UnnormalizedBivariateLagrangePoly<F> for Box<dyn EvaluationDomain<F>> {
    fn eval_unnormalized_bivariate_lagrange_poly(&self, x: F, y: F) -> F {
        if x != y {
            (self.evaluate_vanishing_polynomial(x) - self.evaluate_vanishing_polynomial(y))
                / (x - y)
        } else {
            self.size_as_field_element() * x.pow(&[(self.size() - 1) as u64])
        }
    }

    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(&self, x: F) -> Vec<F> {
        let vanish_x = self.evaluate_vanishing_polynomial(x);
        let mut inverses: Vec<F> = self.elements().map(|y| x - y).collect();
        algebra::fields::batch_inversion(&mut inverses);

        inverses
            .par_iter_mut()
            .for_each(|denominator| *denominator *= vanish_x);
        inverses
    }

    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_same_inputs(&self) -> Vec<F> {
        let mut elems: Vec<F> = self
            .elements()
            .map(|e| e * self.size_as_field_element())
            .collect();
        elems[1..].reverse();
        elems
    }
}

/// A coboundary polynomial over a domain D is a polynomial P
/// s.t. sum_{x_in_D}(P(x)) = 0.
/// Given a coboundary polynomial P over a domain D, a boundary
/// polynomial is a polynomial Z s.t. P(X) = Z(g X) - Z(X) mod v_D(X)
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
        //TODO: Prefix sum here. Parallelize ? Is it worth it ? (rayon (crossbeam too) has no parallel impl for scan())
        let mut poly_cum_sum_evals = evals
            .into_iter()
            .scan(F::zero(), |acc, x| {
                *acc += x;
                Some(*acc)
            })
            .collect::<Vec<_>>();

        // Poly evals over domain should sum to zero
        if poly_cum_sum_evals[poly_cum_sum_evals.len() - 1] != F::zero() {
            return Err(Error::InvalidCoboundaryPolynomial);
        }

        z_evals.append(&mut poly_cum_sum_evals);
        z_evals.pop(); // Pop the last zero

        let z_evals = Evaluations::from_vec_and_domain(z_evals, domain);

        let z_poly = z_evals.interpolate_by_ref();

        Ok(Self {
            poly: z_poly,
            evals: z_evals,
        })
    }

    /// Compute the boundary polynomial given a coboundary
    /// polynomial `poly` over a domain `domain`.
    pub fn from_coboundary_polynomial(
        poly: &DensePolynomial<F>,
        domain: Box<dyn EvaluationDomain<F>>,
    ) -> Result<Self, Error> {
        Self::from_coboundary_polynomial_evals(poly.evaluate_over_domain_by_ref(domain))
    }

    /// Given the domain evaluations `poly_evals` of a polynomial p(X) with non-zero
    /// domain sum v = Sum_{x in D} p(x), construct a boundary polynomial Z(X) for the
    /// centered polynomial p'(X) = p(X) - v/|D|, and return both Z(X) and v/|D|.
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

    /// Given a polynomial `poly` with non-zero sum over `domain` v = Sum_{x in D} p(x),
    /// construct a boundary polynomial Z(X) for the centered polynomial
    /// p'(X) = p(X) - v/|D|, and return both Z(X) and v/|D|.
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
    use algebra::fields::tweedle::fr::Fr;
    use algebra::UniformRand;
    use algebra::{get_best_evaluation_domain, DenseOrSparsePolynomial, DensePolynomial};
    use rand::thread_rng;

    #[test]
    fn domain_unnormalized_bivariate_lagrange_poly() {
        for domain_size in 1..10 {
            let domain = get_best_evaluation_domain::<Fr>(1 << domain_size).unwrap();
            let manual: Vec<_> = domain
                .elements()
                .map(|elem| domain.eval_unnormalized_bivariate_lagrange_poly(elem, elem))
                .collect();
            let fast = domain.batch_eval_unnormalized_bivariate_lagrange_poly_with_same_inputs();
            assert_eq!(fast, manual);
        }
    }

    #[test]
    fn domain_unnormalized_bivariate_lagrange_poly_diff_inputs() {
        let rng = &mut thread_rng();
        for domain_size in 1..10 {
            let domain = get_best_evaluation_domain::<Fr>(1 << domain_size).unwrap();
            let x = Fr::rand(rng);
            let manual: Vec<_> = domain
                .elements()
                .map(|y| domain.eval_unnormalized_bivariate_lagrange_poly(x, y))
                .collect();
            let fast = domain.batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(x);
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
