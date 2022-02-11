//! Submodule that implements the algebraic oracle proof for t-dlog-accumulator Marlin.

use algebra::Field;
use algebra::{get_best_evaluation_domain, Curve, Group};
use poly_commit::PolynomialLabel;
use r1cs_core::SynthesisError;
use std::marker::PhantomData;

use marlin::iop::{Error, LagrangeKernel};

/// Describes data structures and the algorithms used by the indexer.
pub mod indexer;
/// Describes data structures and the algorithms used by the interactive prover.
pub mod prover;
/// Describes data structures and the algorithms used by the interactive verifier.
pub mod verifier;

/// A helper struct to bundle the setup, prover and verifier functions for the
/// algebraic oracle proof from [HGB].
///
/// [HGB]: https://eprint.iacr.org/2021/930
pub struct IOP<G1: Curve, G2: Curve> {
    g1: PhantomData<G1>,
    g2: PhantomData<G2>,
}

impl<G1: Curve, G2: Curve> IOP<G1, G2> {
    /// The labels for the polynomials output by the indexer.
    #[rustfmt::skip]
    pub const INDEXER_POLYNOMIALS: [&'static str; 9] = [
        // Polynomials for A
        "a_row", "a_col", "a_val_row_col",
        // Polynomials for B
        "b_row", "b_col", "b_val_row_col",
        // Polynomials for C
        "c_row", "c_col", "c_val_row_col",
    ];
    /// The labels for the polynomials output by the prover.
    #[rustfmt::skip]
    pub const PROVER_POLYNOMIALS: [&'static str; 12] = [
        // Input poly
        "x",
        // First round oracles
        "w", "y_a", "y_b",
        // Second round oracles
        "u_1", "h_1", "t",
        // Third round oracles
        "curr_bridging_poly", "prev_bridging_poly",
        // Fourth round oracle
        "curr_t_acc_poly",
        // Accumulator oracles
        "prev_t_acc_poly", "prev_bullet_poly",
    ];

    /// An iterator over the polynomials output by the indexer and the prover.
    pub fn polynomial_labels() -> impl Iterator<Item = String> {
        Self::PROVER_POLYNOMIALS.iter().map(|s| s.to_string())
    }

    /// The maximum degree of polynomials produced by the indexer and prover
    /// of this protocol.
    /// The number of the variables always includes the "one" variable addressing
    /// the constants of the arithmetic circuit.
    pub fn max_degree(
        num_constraints: usize,
        num_variables: usize,
        zk: bool,
    ) -> Result<usize, Error> {
        let padded_matrix_dim = std::cmp::max(num_variables, num_constraints);
        let domain_h_size = get_best_evaluation_domain::<G1::ScalarField>(padded_matrix_dim)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?
            .size();
        // The largest oracle degree for the outer sumcheck is
        //      deg h_1(X) = if zk { 2|H| } else { 2|H| - 1 }.
        Ok(2 * domain_h_size - (1 - zk as usize)) // This is really the degree not the number of coefficients
    }

    /// Format the public input according to the requirements of the constraint
    /// system
    pub(crate) fn format_public_input(public_input: &[G1::ScalarField]) -> Vec<G1::ScalarField> {
        let mut input = vec![G1::ScalarField::one()];
        input.extend_from_slice(public_input);
        input
    }

    /// Take in a previously formatted public input and removes the formatting
    /// imposed by the constraint system.
    pub(crate) fn unformat_public_input(input: &[G1::ScalarField]) -> Vec<G1::ScalarField> {
        input[1..].to_vec()
    }

    /// Auxiliary function to verify the outer sumcheck equation.
    #[allow(non_snake_case)]
    pub fn verify_outer_sumcheck(
        public_input: &[G1::ScalarField],
        evals: &poly_commit::Evaluations<G1::ScalarField>,
        state: &verifier::VerifierState<G1, G2>,
    ) -> Result<(), Error> {
        let domain_h = &state.domain_h;
        let g_h = domain_h.group_gen();

        let public_input = Self::format_public_input(public_input);
        let domain_x = get_best_evaluation_domain::<G1::ScalarField>(public_input.len())
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        if state.first_round_msg.is_none() {
            return Err(Error::Other("First round message is empty".to_owned()));
        }

        let first_round_msg = state.first_round_msg.as_ref().unwrap();
        let alpha = first_round_msg.alpha;
        let eta = &first_round_msg.eta;

        let beta = match state.second_round_msg {
            Some(v) => v.beta,
            None => Err(Error::Other("Second round message is empty".to_owned()))?,
        };

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
        let t_at_beta = get_poly_eval(evals, "t".into(), beta)?;
        let x_at_beta = get_poly_eval(evals, "x".into(), beta)?;

        let y_at_beta = x_at_beta + v_X_at_beta * w_at_beta;

        let y_eta_at_beta =
            eta[0] * y_a_at_beta + eta[1] * y_b_at_beta + eta[2] * y_a_at_beta * y_b_at_beta;

        let outer_sumcheck = t_at_beta * y_at_beta - l_alpha_beta * y_eta_at_beta - u_1_at_g_beta
            + u_1_at_beta
            - h_1_at_beta * v_H_at_beta;

        if !outer_sumcheck.is_zero() {
            return Err(Error::VerificationEquationFailed(
                "Outer sumcheck".to_owned(),
            ));
        }

        Ok(())
    }

    /// Auxiliary function to verify the inner sumcheck aggregation rounds.
    pub fn verify_inner_sumcheck_aggregation(
        evals: &poly_commit::Evaluations<G1::ScalarField>,
        state: &verifier::VerifierState<G1, G2>,
    ) -> Result<(), Error> {
        if state.first_round_msg.is_none() {
            return Err(Error::Other("First round message is empty".to_owned()));
        }
        if state.second_round_msg.is_none() {
            return Err(Error::Other("Second round message is empty".to_owned()));
        }
        if state.third_round_msg.is_none() {
            return Err(Error::Other("Third round message is empty".to_owned()));
        }

        let alpha = state.first_round_msg.as_ref().unwrap().alpha;
        let beta = state.second_round_msg.unwrap().beta;
        let gamma = state.third_round_msg.unwrap().gamma;
        let lambda = state.third_round_msg.unwrap().lambda;

        let prev_alpha = state.previous_inner_sumcheck_acc.1.alpha;

        let curr_bridging_poly_at_alpha = get_poly_eval(evals, "curr_bridging_poly".into(), alpha)?;
        let curr_bridging_poly_at_gamma = get_poly_eval(evals, "curr_bridging_poly".into(), gamma)?;
        let prev_bridging_poly_at_prev_alpha =
            get_poly_eval(evals, "prev_bridging_poly".into(), prev_alpha)?;
        let prev_bridging_poly_at_gamma = get_poly_eval(evals, "prev_bridging_poly".into(), gamma)?;
        let t_at_beta = get_poly_eval(evals, "t".into(), beta)?;
        let prev_t_acc_poly_at_beta = get_poly_eval(evals, "prev_t_acc_poly".into(), beta)?;
        let curr_t_acc_poly_at_beta = get_poly_eval(evals, "curr_t_acc_poly".into(), beta)?;

        let check_first_round_1 = curr_bridging_poly_at_alpha - t_at_beta;
        let check_first_round_2 = prev_bridging_poly_at_prev_alpha - prev_t_acc_poly_at_beta;
        let check_second_round = curr_bridging_poly_at_gamma + lambda * prev_bridging_poly_at_gamma
            - curr_t_acc_poly_at_beta;

        if !check_first_round_1.is_zero() {
            return Err(Error::VerificationEquationFailed(
                "Inner sumcheck aggregation first round: current bridging poly".to_owned(),
            ));
        }

        if !check_first_round_2.is_zero() {
            return Err(Error::VerificationEquationFailed(
                "Inner sumcheck aggregation first round: previous bridging poly".to_owned(),
            ));
        }

        if !check_second_round.is_zero() {
            return Err(Error::VerificationEquationFailed(
                "Inner sumcheck aggregation second round".to_owned(),
            ));
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
