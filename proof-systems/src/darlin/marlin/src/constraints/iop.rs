use crate::constraints::polynomials::AlgebraForIOP;
use crate::iop::indexer::IndexInfo;
use algebra::{get_best_evaluation_domain, EndoMulCurve, Field, PrimeField};
use fiat_shamir::constraints::FiatShamirRngGadget;
use poly_commit::{Evaluations, QueryMap};
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use r1cs_std::boolean::Boolean;
use r1cs_std::fields::nonnative::nonnative_field_gadget::NonNativeFieldGadget;
use r1cs_std::fields::FieldGadget;
use r1cs_std::groups::EndoMulCurveGadget;
use r1cs_std::prelude::EqGadget;
use r1cs_std::FromBitsGadget;
use std::collections::BTreeSet;
use std::iter::FromIterator;
use std::marker::PhantomData;

/// Gadget for the IOP.
pub struct IOPVerificationGadget<G, GG>
where
    G: EndoMulCurve,
    GG: EndoMulCurveGadget<G, G::BaseField>,
{
    g: PhantomData<G>,
    gg: PhantomData<GG>,
}

#[derive(Clone)]
pub struct VerifierStateGadget<SimulationF: PrimeField, ConstraintF: PrimeField> {
    domain_h_size: u64,
    domain_k_size: u64,

    first_round_msg: Option<VerifierFirstMsgGadget<SimulationF, ConstraintF>>,
    second_round_msg: Option<VerifierSecondMsgGadget<SimulationF, ConstraintF>>,

    gamma: Option<NonNativeFieldGadget<SimulationF, ConstraintF>>,
}

#[derive(Clone)]
pub struct VerifierFirstMsgGadget<SimulationF: PrimeField, ConstraintF: PrimeField> {
    pub alpha: NonNativeFieldGadget<SimulationF, ConstraintF>,
    pub eta: NonNativeFieldGadget<SimulationF, ConstraintF>,
}

#[derive(Clone)]
pub struct VerifierSecondMsgGadget<SimulationF: PrimeField, ConstraintF: PrimeField> {
    pub beta: NonNativeFieldGadget<SimulationF, ConstraintF>,
}

#[derive(Clone)]
pub struct VerifierThirdMsgGadget<SimulationF: PrimeField, ConstraintF: PrimeField> {
    pub gamma: NonNativeFieldGadget<SimulationF, ConstraintF>,
}

impl<G, GG> IOPVerificationGadget<G, GG>
where
    G: EndoMulCurve,
    GG: EndoMulCurveGadget<G, G::BaseField>,
{
    /// The verifier first round, samples the random challenges `eta` and `alpha` for reducing the R1CS identies
    /// to a sumcheck.
    pub fn verifier_first_round<
        FSG: FiatShamirRngGadget<G::BaseField>,
        CS: ConstraintSystemAbstract<G::BaseField>,
    >(
        mut cs: CS,
        index_info: &IndexInfo<G::ScalarField>,
        fs_rng: &mut FSG,
    ) -> Result<
        (
            VerifierFirstMsgGadget<G::ScalarField, G::BaseField>,
            VerifierStateGadget<G::ScalarField, G::BaseField>,
        ),
        SynthesisError,
    > {
        let num_formatted_variables = index_info.num_inputs + index_info.num_witness;
        let num_constraints = index_info.num_constraints;
        let padded_matrix_dim = std::cmp::max(num_formatted_variables, num_constraints);
        let domain_h = get_best_evaluation_domain::<G::ScalarField>(padded_matrix_dim)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let domain_k = get_best_evaluation_domain::<G::ScalarField>(index_info.num_non_zero)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let chals = fs_rng.enforce_get_many_challenges::<_, 128>(
            cs.ns(|| "squeeze bits for alpha and eta challenges"),
            2,
        )?;

        let alpha =
            NonNativeFieldGadget::from_bits(cs.ns(|| "read alpha challenge from bits"), &chals[0])?;

        let eta =
            NonNativeFieldGadget::from_bits(cs.ns(|| "read eta challenge from bits"), &chals[1])?;

        let msg = VerifierFirstMsgGadget { alpha, eta };

        let new_state = VerifierStateGadget {
            domain_h_size: domain_h.size() as u64,
            domain_k_size: domain_k.size() as u64,
            first_round_msg: Some(msg.clone()),
            second_round_msg: None,
            gamma: None,
        };

        Ok((msg, new_state))
    }

    /// Second round of the verifier, samples the random challenge `beta` for probing
    /// the outer sumcheck identity.
    pub fn verifier_second_round<
        FSG: FiatShamirRngGadget<G::BaseField>,
        CS: ConstraintSystemAbstract<G::BaseField>,
    >(
        mut cs: CS,
        mut state: VerifierStateGadget<G::ScalarField, G::BaseField>,
        fs_rng: &mut FSG,
    ) -> Result<
        (
            VerifierSecondMsgGadget<G::ScalarField, G::BaseField>,
            VerifierStateGadget<G::ScalarField, G::BaseField>,
        ),
        SynthesisError,
    > {
        let chal =
            fs_rng.enforce_get_challenge::<_, 128>(cs.ns(|| "squeeze bits for beta challenge"))?;

        let beta =
            NonNativeFieldGadget::from_bits(cs.ns(|| "read beta challenge from bits"), &chal)?;

        let msg = VerifierSecondMsgGadget { beta };
        state.second_round_msg = Some(msg.clone());

        Ok((msg, state))
    }

    /// Second round of the verifier, samples the random challenge `gamma` for probing
    /// the inner sumcheck identity.
    pub fn verifier_third_round<
        FSG: FiatShamirRngGadget<G::BaseField>,
        CS: ConstraintSystemAbstract<G::BaseField>,
    >(
        mut cs: CS,
        mut state: VerifierStateGadget<G::ScalarField, G::BaseField>,
        fs_rng: &mut FSG,
    ) -> Result<
        (
            VerifierThirdMsgGadget<G::ScalarField, G::BaseField>,
            VerifierStateGadget<G::ScalarField, G::BaseField>,
        ),
        SynthesisError,
    > {
        let chal =
            fs_rng.enforce_get_challenge::<_, 128>(cs.ns(|| "squeeze bits for gamma challenge"))?;

        let gamma =
            NonNativeFieldGadget::from_bits(cs.ns(|| "read gamma challenge from bits"), &chal)?;

        let msg = VerifierThirdMsgGadget {
            gamma: gamma.clone(),
        };
        state.gamma = Some(gamma);

        Ok((msg, state))
    }

    /// Auxiliary function to verify the two sumcheck equations given the evalations.
    #[allow(non_snake_case)]
    pub(crate) fn verify_sumchecks<CS: ConstraintSystemAbstract<G::BaseField>>(
        mut cs: CS,
        formatted_public_input: &[NonNativeFieldGadget<G::ScalarField, G::BaseField>],
        evals: &Evaluations<NonNativeFieldGadget<G::ScalarField, G::BaseField>>,
        state: &VerifierStateGadget<G::ScalarField, G::BaseField>,
    ) -> Result<(), SynthesisError> {
        let domain_h = get_best_evaluation_domain::<G::ScalarField>(state.domain_h_size as usize)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let h_size_inv = domain_h.size_inv();

        let domain_k = get_best_evaluation_domain::<G::ScalarField>(state.domain_k_size as usize)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let k_size_inv = domain_k.size_inv();

        let zero = NonNativeFieldGadget::<G::ScalarField, G::BaseField>::zero(cs.ns(|| "zero"))?;

        let domain_x = get_best_evaluation_domain::<G::ScalarField>(formatted_public_input.len())
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        if state.first_round_msg.is_none() {
            return Err(SynthesisError::Other(
                "First round message is empty".to_owned(),
            ));
        }

        let first_round_msg = state.first_round_msg.as_ref().unwrap();
        let alpha = first_round_msg.alpha.clone();
        let eta = first_round_msg.eta.clone();
        let eta_squared = eta.square(cs.ns(|| "eta^2"))?;

        let beta = match state.second_round_msg.as_ref() {
            Some(v) => v.beta.clone(),
            None => Err(SynthesisError::Other(
                "Second round message is empty".to_owned(),
            ))?,
        };

        let gamma = match state.gamma.as_ref() {
            Some(v) => v,
            None => Err(SynthesisError::Other("Gamma is empty".to_owned()))?,
        };

        let v_H_at_alpha = AlgebraForIOP::eval_vanishing_polynomial(
            cs.ns(|| "alpha^|H| - 1"),
            &alpha,
            domain_h.size() as u64,
        )?;

        let v_H_at_beta = AlgebraForIOP::eval_vanishing_polynomial(
            cs.ns(|| "beta^|H| - 1"),
            &beta,
            domain_h.size() as u64,
        )?;

        let v_K_at_gamma = AlgebraForIOP::eval_vanishing_polynomial(
            cs.ns(|| "gamma^|K| - 1"),
            &gamma,
            domain_k.size() as u64,
        )?;

        let v_X_at_beta = AlgebraForIOP::eval_vanishing_polynomial(
            cs.ns(|| "beta^|X| - 1"),
            &beta,
            domain_x.size() as u64,
        )?;

        // Evaluate polynomials at beta
        let l_alpha_beta = AlgebraForIOP::prepared_eval_lagrange_kernel(
            cs.ns(|| "evaluate bivariate Lagrange poly"),
            &alpha,
            &beta,
            &v_H_at_alpha,
            &v_H_at_beta,
            &h_size_inv,
        )?;

        let w_at_beta = evals
            .get(&("w".into(), "beta".into()))
            .ok_or_else(|| SynthesisError::AssignmentMissing)?;
        let y_a_at_beta = evals
            .get(&("y_a".into(), "beta".into()))
            .ok_or_else(|| SynthesisError::AssignmentMissing)?;
        let y_b_at_beta = evals
            .get(&("y_b".into(), "beta".into()))
            .ok_or_else(|| SynthesisError::AssignmentMissing)?;
        let u_1_at_beta = evals
            .get(&("u_1".into(), "beta".into()))
            .ok_or_else(|| SynthesisError::AssignmentMissing)?;
        let u_1_at_g_beta = evals
            .get(&("u_1".into(), "g_h * beta".into()))
            .ok_or_else(|| SynthesisError::AssignmentMissing)?;
        let h_1_at_beta = evals
            .get(&("h_1".into(), "beta".into()))
            .ok_or_else(|| SynthesisError::AssignmentMissing)?;
        let x_at_beta = evals
            .get(&("x".into(), "beta".into()))
            .ok_or_else(|| SynthesisError::AssignmentMissing)?;

        #[rustfmt::skip]
        let y_eta_at_beta = {
            let term_1 = eta
                .mul_without_prereduce(cs.ns(|| "eta * y_b_at_beta"), &y_b_at_beta)?;
            let term_2 = eta_squared
                .mul(cs.ns(|| "eta^2 * y_a_at_beta"), &y_a_at_beta)?
                .mul_without_prereduce(cs.ns(|| "eta^2 * y_a_at_beta * y_b_at_beta"), &y_b_at_beta)?;
            term_1
                .add(cs.ns(|| "eta * y_b_at_beta + eta^2 * y_a_at_beta * y_b_at_beta"),&term_2)?
                .reduce(cs.ns(|| "reduce(eta * y_b_at_beta + eta^2 * y_a_at_beta * y_b_at_beta)"))?
                .add(cs.ns(|| "y_a_at_beta + eta * y_b_at_beta + eta^2 * y_a_at_beta * y_b_at_beta"), &y_a_at_beta)?
        };
        #[rustfmt::skip]
        let v_1 = {
            let term_1 = l_alpha_beta
                .mul_without_prereduce(cs.ns(|| "l_alpha_beta * y_eta_at_beta"), &y_eta_at_beta)?;
            let term_2 = h_1_at_beta
                .mul_without_prereduce(cs.ns(|| "h_1_at_beta * v_H_at_beta"), &v_H_at_beta)?;
            term_1
                .add(cs.ns(|| "l_alpha_beta * y_eta_at_beta + h_1_at_beta * v_H_at_beta"), &term_2)?
                .reduce(cs.ns(|| "reduce(l_alpha_beta * y_eta_at_beta + h_1_at_beta * v_H_at_beta)"))?
                .add(cs.ns(|| "l_alpha_beta * y_eta_at_beta + h_1_at_beta * v_H_at_beta + u_1_at_g_beta"), &u_1_at_g_beta)?
                .sub(cs.ns(|| "l_alpha_beta * y_eta_at_beta + h_1_at_beta * v_H_at_beta + u_1_at_g_beta - u_1_at_beta"), &u_1_at_beta)?           
        };

        #[rustfmt::skip]
        let v_2 = v_X_at_beta
            .mul(cs.ns(|| "v_X_at_beta * w_at_beta"), &w_at_beta)?
            .add(cs.ns(|| "x_at_beta + v_X_at_beta * w_at_beta"), &x_at_beta)?;

        let v_1_is_zero = v_1.is_eq(cs.ns(|| "v_1 == 0 ?"), &zero)?;
        let v_2_is_not_zero = v_2.is_neq(cs.ns(|| "v_2 != 0 ?"), &zero)?;
        let outer_check = Boolean::or(
            cs.ns(|| "(v_1 == 0 || v_2 != 0) ?"),
            &v_1_is_zero,
            &v_2_is_not_zero,
        )?;

        outer_check.enforce_equal(
            cs.ns(|| "enforce (v_1 == 0 || v_2 != 0)"),
            &Boolean::constant(true),
        )?;

        let inner_sumcheck = {
            let alpha_beta = alpha.mul_without_prereduce(cs.ns(|| "alpha * beta"), &beta)?;

            // Evaluate polynomials at gamma

            let u_2_at_gamma = evals
                .get(&("u_2".into(), "gamma".into()))
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;
            let u_2_at_g_gamma = evals
                .get(&("u_2".into(), "g_k * gamma".into()))
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;
            let h_2_at_gamma = evals
                .get(&("h_2".into(), "gamma".into()))
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;

            let a_row_at_gamma = evals
                .get(&("a_row".into(), "gamma".into()))
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;
            let a_col_at_gamma = evals
                .get(&("a_col".into(), "gamma".into()))
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;
            let a_row_col_at_gamma = evals
                .get(&("a_row_col".into(), "gamma".into()))
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;
            let a_val_row_col_at_gamma = evals
                .get(&("a_val_row_col".into(), "gamma".into()))
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;

            let b_row_at_gamma = evals
                .get(&("b_row".into(), "gamma".into()))
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;
            let b_col_at_gamma = evals
                .get(&("b_col".into(), "gamma".into()))
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;
            let b_row_col_at_gamma = evals
                .get(&("b_row_col".into(), "gamma".into()))
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;
            let b_val_row_col_at_gamma = evals
                .get(&("b_val_row_col".into(), "gamma".into()))
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;

            let c_row_at_gamma = evals
                .get(&("c_row".into(), "gamma".into()))
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;
            let c_col_at_gamma = evals
                .get(&("c_col".into(), "gamma".into()))
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;
            let c_row_col_at_gamma = evals
                .get(&("c_row_col".into(), "gamma".into()))
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;
            let c_val_row_col_at_gamma = evals
                .get(&("c_val_row_col".into(), "gamma".into()))
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;

            // The denominator terms, using row.col_M(X)
            #[rustfmt::skip]
            let a_denom_at_gamma = {
                let minus_a_row_at_gamma = a_row_at_gamma.negate(cs.ns(|| "-a_row_at_gamma"))?;
                let minus_a_col_at_gamma = a_col_at_gamma.negate(cs.ns(|| "-a_col_at_gamma"))?;
                let term_1 = beta.mul_without_prereduce(cs.ns(|| "-(beta * a_row_at_gamma)"), &minus_a_row_at_gamma)?;
                let term_2 = alpha.mul_without_prereduce(cs.ns(|| "-(alpha * a_col_at_gamma)"), &minus_a_col_at_gamma)?;
                alpha_beta
                    .add(cs.ns(|| "alpha_beta - beta * a_row_at_gamma"), &term_1)?
                    .add(cs.ns(|| "alpha_beta - beta * a_row_at_gamma - alpha * a_col_at_gamma"), &term_2)?
                    .reduce(cs.ns(|| "reduce(alpha_beta - beta * a_row_at_gamma - alpha * a_col_at_gamma)"))?
                    .add(cs.ns(|| "alpha_beta - beta * a_row_at_gamma - alpha * a_col_at_gamma + a_row_col_at_gamma"), &a_row_col_at_gamma)?
            };
            #[rustfmt::skip]
                let b_denom_at_gamma = {
                let minus_b_row_at_gamma = b_row_at_gamma.negate(cs.ns(|| "-b_row_at_gamma"))?;
                let minus_b_col_at_gamma = b_col_at_gamma.negate(cs.ns(|| "-b_col_at_gamma"))?;
                let term_1 = beta.mul_without_prereduce(cs.ns(|| "-(beta * b_row_at_gamma)"), &minus_b_row_at_gamma)?;
                let term_2 = alpha.mul_without_prereduce(cs.ns(|| "-(alpha * b_col_at_gamma)"), &minus_b_col_at_gamma)?;
                alpha_beta
                    .add(cs.ns(|| "alpha_beta - beta * b_row_at_gamma"), &term_1)?
                    .add(cs.ns(|| "alpha_beta - beta * b_row_at_gamma - alpha * b_col_at_gamma"), &term_2)?
                    .reduce(cs.ns(|| "reduce(alpha_beta - beta * b_row_at_gamma - alpha * b_col_at_gamma)"))?
                    .add(cs.ns(|| "alpha_beta - beta * b_row_at_gamma - alpha * b_col_at_gamma + b_row_col_at_gamma"), &b_row_col_at_gamma)?
            };
            #[rustfmt::skip]
                let c_denom_at_gamma = {
                let minus_c_row_at_gamma = c_row_at_gamma.negate(cs.ns(|| "-c_row_at_gamma"))?;
                let minus_c_col_at_gamma = c_col_at_gamma.negate(cs.ns(|| "-c_col_at_gamma"))?;
                let term_1 = beta.mul_without_prereduce(cs.ns(|| "-(beta * c_row_at_gamma)"), &minus_c_row_at_gamma)?;
                let term_2 = alpha.mul_without_prereduce(cs.ns(|| "-(alpha * c_col_at_gamma)"), &minus_c_col_at_gamma)?;
                alpha_beta
                    .add(cs.ns(|| "alpha_beta - beta * c_row_at_gamma"), &term_1)?
                    .add(cs.ns(|| "alpha_beta - beta * c_row_at_gamma - alpha * c_col_at_gamma"), &term_2)?
                    .reduce(cs.ns(|| "reduce(alpha_beta - beta * c_row_at_gamma - alpha * c_col_at_gamma)"))?
                    .add(cs.ns(|| "alpha_beta - beta * c_row_at_gamma - alpha * c_col_at_gamma + c_row_col_at_gamma"), &c_row_col_at_gamma)?
            };

            // b(X) at X=gamma
            let ab_denom_at_gamma = a_denom_at_gamma.mul(
                cs.ns(|| "a_denom_at_gamma * b_denom_at_gamma"),
                &b_denom_at_gamma,
            )?;

            let b_expr_at_gamma = {
                let b_at_gamma = ab_denom_at_gamma.mul(
                    cs.ns(|| "a_denom_at_gamma * b_denom_at_gamma * c_denom_at_gamma"),
                    &c_denom_at_gamma,
                )?;
                let u_2_diff =
                    u_2_at_g_gamma.sub(cs.ns(|| "u_2_at_g_gamma - u_2_at_gamma"), &u_2_at_gamma)?;
                let term_1 = v_2.mul_without_prereduce(
                    cs.ns(|| "v_2 * (u_2_at_g_gamma - u_2_at_gamma)"),
                    &u_2_diff,
                )?;
                let term_2 = v_1
                    .mul_by_constant_without_prereduce(cs.ns(|| "v_1 * k_size_inv"), &k_size_inv)?;
                term_1
                    .add(
                        cs.ns(|| "v_2 * (u_2_at_g_gamma - u_2_at_gamma) + v_1 * k_size_inv"),
                        &term_2,
                    )?
                    .reduce(cs.ns(|| "reduce"))?
                    .mul(cs.ns(|| "b_expr_at_gamma"), &b_at_gamma)?
            };

            #[rustfmt::skip]
            let inner_sumcheck = {
                let term_1 = b_denom_at_gamma
                    .mul(cs.ns(|| "b_denom_at_gamma * c_denom_at_gamma"), &c_denom_at_gamma)?
                    .mul_without_prereduce(cs.ns(|| "b_denom_at_gamma * c_denom_at_gamma * a_val_row_col_at_gamma"), &a_val_row_col_at_gamma)?;
                let term_2 = a_denom_at_gamma
                    .mul(cs.ns(|| "a_denom_at_gamma * c_denom_at_gamma"), &c_denom_at_gamma)?
                    .mul(cs.ns(|| "a_denom_at_gamma * c_denom_at_gamma * b_val_row_col_at_gamma"), &b_val_row_col_at_gamma)?
                    .mul_without_prereduce(cs.ns(|| "eta * a_denom_at_gamma * c_denom_at_gamma * b_val_row_col_at_gamma"), &eta)?;
                let term_3 = ab_denom_at_gamma
                    .mul(cs.ns(|| "b_denom_at_gamma * a_denom_at_gamma * c_val_row_col_at_gamma"), &c_val_row_col_at_gamma)?
                    .mul_without_prereduce(cs.ns(|| "eta^2 * b_denom_at_gamma * a_denom_at_gamma * c_val_row_col_at_gamma"), &eta_squared)?;
                let term_4 = v_2
                    .mul(cs.ns(|| "v_2 * v_K_at_gamma"), &v_K_at_gamma)?
                    .negate(cs.ns(|| "-v_2 * v_K_at_gamma"))?
                    .mul_without_prereduce(cs.ns(|| "-v2 * v_K_at_gamma * h_2_at_gamma"), &h_2_at_gamma)?;
                term_1
                    .add(cs.ns(|| "term_1 + term_2"), &term_2)?
                    .add(cs.ns(|| "term_1 + term_2 + term_3"), &term_3)?
                    .reduce(cs.ns(|| "reduce(term_1 + term_2 + term_3)"))?
                    .mul(cs.ns(|| "... * v_2"), &v_2)?
                    .mul(cs.ns(|| "... * v_H_at_alpha"), &v_H_at_alpha)?
                    .mul(cs.ns(|| "... * v_H_at_beta"), &v_H_at_beta)?
                    .mul_by_constant_without_prereduce(cs.ns(|| "... * |H|^(-2)"), &(h_size_inv.square()))?
                    .add(cs.ns(|| "... + term_4"), &term_4)?
                    .reduce(cs.ns(|| "... .reduce()"))?
                    .sub(cs.ns(|| "... - b_expr_at_gamma"), &b_expr_at_gamma)?
            };
            inner_sumcheck
        };

        inner_sumcheck.enforce_equal(cs.ns(|| "inner_sumcheck"), &zero)?;
        Ok(())
    }

    /// Output the query state and next round state.
    pub fn verifier_query_map_gadget<'a, CS: ConstraintSystemAbstract<G::BaseField>>(
        mut cs: CS,
        state: VerifierStateGadget<G::ScalarField, G::BaseField>,
    ) -> Result<
        (
            QueryMap<'a, NonNativeFieldGadget<G::ScalarField, G::BaseField>>,
            VerifierStateGadget<G::ScalarField, G::BaseField>,
        ),
        SynthesisError,
    > {
        if state.second_round_msg.is_none() {
            return Err(SynthesisError::Other(
                "Second round message is empty".to_owned(),
            ));
        }
        let beta = state.second_round_msg.as_ref().unwrap().clone().beta;

        if state.gamma.is_none() {
            return Err(SynthesisError::Other("Gamma is empty".to_owned()));
        }
        let gamma = state.gamma.as_ref().unwrap().clone();

        let domain_h = get_best_evaluation_domain::<G::ScalarField>(state.domain_h_size as usize)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let domain_k = get_best_evaluation_domain::<G::ScalarField>(state.domain_k_size as usize)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let g_h = domain_h.group_gen();
        let g_k = domain_k.group_gen();

        let g_h_times_beta = beta.mul_by_constant(cs.ns(|| "g_H * beta"), &g_h)?;
        let g_k_times_gamma = gamma.mul_by_constant(cs.ns(|| "g_K * beta"), &g_k)?;

        let queries_at_beta = BTreeSet::from_iter(vec![
            "w".to_string(),
            "y_a".to_string(),
            "y_b".to_string(),
            "u_1".to_string(),
            "h_1".to_string(),
        ]);
        let queries_at_gamma = BTreeSet::from_iter(vec![
            "u_2".to_string(),
            "h_2".to_string(),
            "a_row".to_string(),
            "a_col".to_string(),
            "a_row_col".to_string(),
            "a_val_row_col".to_string(),
            "b_row".to_string(),
            "b_col".to_string(),
            "b_row_col".to_string(),
            "b_val_row_col".to_string(),
            "c_row".to_string(),
            "c_col".to_string(),
            "c_row_col".to_string(),
            "c_val_row_col".to_string(),
        ]);
        let queries_at_g_beta = BTreeSet::from_iter(vec!["u_1".to_string()]);
        let queries_at_g_gamma = BTreeSet::from_iter(vec!["u_2".to_string()]);

        let query_map = {
            let mut map = QueryMap::new();
            map.insert("beta".to_string(), (beta, queries_at_beta));
            map.insert("gamma".to_string(), (gamma, queries_at_gamma));
            map.insert("g * beta".to_string(), (g_h_times_beta, queries_at_g_beta));
            map.insert(
                "g * gamma".to_string(),
                (g_k_times_gamma, queries_at_g_gamma),
            );
            map
        };

        Ok((query_map, state))
    }
}
