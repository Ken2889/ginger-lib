//! Submodule that implements the algebraic oracle proof for t-dlog-accumulator Marlin.

use crate::darlin::IPACurve;
use algebra::get_best_evaluation_domain;
use num_traits::{One, Zero};
use r1cs_core::SynthesisError;
use std::marker::PhantomData;

use marlin::iop::{get_poly_eval, Error, LagrangeKernel};

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
pub struct IOP<G1, G2>
where
    G1: IPACurve,
    G2: IPACurve,
{
    g1: PhantomData<G1>,
    g2: PhantomData<G2>,
}

impl<G1, G2> IOP<G1, G2>
where
    G1: IPACurve,
    G2: IPACurve,
{
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
        let public_input = Self::format_public_input(public_input);

        let domain_h = &state.domain_h;
        let domain_x = get_best_evaluation_domain::<G1::ScalarField>(public_input.len())
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let (alpha, eta) = match &state.first_round_msg {
            Some(msg) => (msg.alpha, msg.get_etas()),
            None => return Err(Error::Other("First round message is empty".to_owned())),
        };

        let beta = match &state.second_round_msg {
            Some(msg) => msg.beta,
            None => return Err(Error::Other("Second round message is empty".to_owned())),
        };

        let v_H_at_beta = domain_h.evaluate_vanishing_polynomial(beta);

        // Evaluate polynomials at beta
        let l_alpha_beta = domain_h.eval_lagrange_kernel(alpha, beta);
        let v_X_at_beta = domain_x.evaluate_vanishing_polynomial(beta);

        let w_at_beta = get_poly_eval(evals, "w", "beta")?;
        let y_a_at_beta = get_poly_eval(evals, "y_a", "beta")?;
        let y_b_at_beta = get_poly_eval(evals, "y_b", "beta")?;
        let u_1_at_beta = get_poly_eval(evals, "u_1", "beta")?;
        let u_1_at_g_beta = get_poly_eval(evals, "u_1", "g * beta")?;
        let h_1_at_beta = get_poly_eval(evals, "h_1", "beta")?;
        let t_at_beta = get_poly_eval(evals, "t", "beta")?;
        let x_at_beta = get_poly_eval(evals, "x", "beta")?;

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

    pub fn verify_dlog_aggregation(
        evals: &poly_commit::Evaluations<G1::ScalarField>,
        state: &verifier::VerifierState<G1, G2>,
    ) -> Result<(), Error> {
        let gamma = match &state.third_round_msg {
            Some(msg) => msg.gamma,
            None => return Err(Error::Other("Third round message is empty".to_owned())),
        };

        let prev_dlog_poly_at_gamma = state.previous_acc.non_native[0]
            .dlog_item
            .check_poly
            .evaluate(gamma);
        let prev_dlog_poly_at_gamma_from_prover =
            get_poly_eval(evals, "prev_bullet_poly", "gamma")?;

        if prev_dlog_poly_at_gamma_from_prover != prev_dlog_poly_at_gamma {
            return Err(Error::VerificationEquationFailed(
                "Dlog aggregation".to_owned(),
            ));
        }
        Ok(())
    }

    /// Auxiliary function to verify the inner sumcheck aggregation rounds.
    pub fn verify_inner_sumcheck_aggregation(
        evals: &poly_commit::Evaluations<G1::ScalarField>,
        state: &verifier::VerifierState<G1, G2>,
    ) -> Result<(), Error> {
        let lambda = match &state.third_round_msg {
            Some(msg) => msg.lambda,
            None => return Err(Error::Other("Third round message is empty".to_owned())),
        };

        let curr_bridging_poly_at_alpha = get_poly_eval(evals, "curr_bridging_poly", "alpha")?;
        let t_at_beta = get_poly_eval(evals, "t", "beta")?;

        if curr_bridging_poly_at_alpha != t_at_beta {
            return Err(Error::VerificationEquationFailed(
                "Inner sumcheck aggregation first round: current bridging poly".to_owned(),
            ));
        }

        let prev_bridging_poly_at_prev_alpha =
            get_poly_eval(evals, "prev_bridging_poly", "prev_alpha")?;
        let prev_t_acc_poly_at_beta = get_poly_eval(evals, "prev_t_acc_poly", "beta")?;

        if prev_bridging_poly_at_prev_alpha != prev_t_acc_poly_at_beta {
            return Err(Error::VerificationEquationFailed(
                "Inner sumcheck aggregation first round: previous bridging poly".to_owned(),
            ));
        }

        let curr_bridging_poly_at_gamma = get_poly_eval(evals, "curr_bridging_poly", "gamma")?;
        let prev_bridging_poly_at_gamma = get_poly_eval(evals, "prev_bridging_poly", "gamma")?;
        let curr_t_acc_poly_at_beta = get_poly_eval(evals, "curr_t_acc_poly", "beta")?;

        if curr_bridging_poly_at_gamma + lambda * prev_bridging_poly_at_gamma
            != curr_t_acc_poly_at_beta
        {
            return Err(Error::VerificationEquationFailed(
                "Inner sumcheck aggregation second round".to_owned(),
            ));
        }

        Ok(())
    }
}
