#![allow(non_snake_case)]

use crate::ahp::indexer::IndexInfo;
use crate::ahp::*;

use algebra::PrimeField;
use algebra::{get_best_evaluation_domain, EvaluationDomain};
use poly_commit::rng::FiatShamirRng;
use poly_commit::QuerySet;

/// State of the AHP verifier
pub struct VerifierState<F: PrimeField> {
    pub(crate) domain_h: Box<dyn EvaluationDomain<F>>,
    pub(crate) domain_k: Box<dyn EvaluationDomain<F>>,

    pub(crate) first_round_msg: Option<VerifierFirstMsg<F>>,
    pub(crate) second_round_msg: Option<VerifierSecondMsg<F>>,

    pub(crate) gamma: Option<F>,
}

/// First message of the verifier.
#[derive(Copy, Clone)]
pub struct VerifierFirstMsg<F> {
    /// Query for the random polynomial.
    pub alpha: F,
    /// Randomizer for the lincheck for `A`.
    pub eta_a: F,
    /// Randomizer for the lincheck for `B`.
    pub eta_b: F,
    /// Randomizer for the lincheck for `C`.
    pub eta_c: F,
}

/// Second verifier message.
#[derive(Copy, Clone)]
pub struct VerifierSecondMsg<F> {
    /// Query for the second round of polynomials.
    pub beta: F,
}

impl<F: PrimeField> AHPForR1CS<F> {
    /// Output the first message and next round state.
    pub fn verifier_first_round<R: FiatShamirRng>(
        index_info: IndexInfo<F>,
        fs_rng: &mut R,
    ) -> Result<(VerifierFirstMsg<F>, VerifierState<F>), Error> {
        if index_info.num_constraints != (index_info.num_witness + index_info.num_inputs) {
            return Err(Error::NonSquareMatrix);
        }

        let domain_h = get_best_evaluation_domain::<F>(index_info.num_constraints)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let domain_k = get_best_evaluation_domain::<F>(index_info.num_non_zero)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let alpha: F = fs_rng.squeeze_128_bits_challenge();
        if domain_h.evaluate_vanishing_polynomial(alpha).is_zero() {
            return Err(Error::Other(
                "Sampled an alpha challenge belonging to H domain".to_owned(),
            ));
        }

        let eta: F = fs_rng.squeeze_128_bits_challenge();
        let eta_a = F::one();
        let eta_b = eta;
        let eta_c = eta_b * &eta;

        let msg = VerifierFirstMsg {
            alpha,
            eta_a,
            eta_b,
            eta_c,
        };

        let new_state = VerifierState {
            domain_h,
            domain_k,
            first_round_msg: Some(msg),
            second_round_msg: None,
            gamma: None,
        };

        Ok((msg, new_state))
    }

    /// Output the second message and next round state.
    pub fn verifier_second_round<R: FiatShamirRng>(
        mut state: VerifierState<F>,
        fs_rng: &mut R,
    ) -> Result<(VerifierSecondMsg<F>, VerifierState<F>), Error> {
        let beta: F = fs_rng.squeeze_128_bits_challenge();
        if state.domain_h.evaluate_vanishing_polynomial(beta).is_zero() {
            return Err(Error::Other(
                "Sampled a beta challenge belonging to H domain".to_owned(),
            ));
        }

        let msg = VerifierSecondMsg { beta };
        state.second_round_msg = Some(msg);

        Ok((msg, state))
    }

    /// Output the third message and next round state.
    pub fn verifier_third_round<R: FiatShamirRng>(
        mut state: VerifierState<F>,
        fs_rng: &mut R,
    ) -> VerifierState<F> {
        let gamma: F = fs_rng.squeeze_128_bits_challenge();
        state.gamma = Some(gamma);
        state
    }

    /// Output the query state and next round state.
    pub fn verifier_query_set<'a, 'b>(
        state: VerifierState<F>,
    ) -> Result<(QuerySet<'b, F>, VerifierState<F>), Error> {
        if state.second_round_msg.is_none() {
            return Err(Error::Other("Second round message is empty".to_owned()));
        }
        let beta = state.second_round_msg.unwrap().beta;

        if state.gamma.is_none() {
            return Err(Error::Other("Gamma is empty".to_owned()));
        }
        let gamma = state.gamma.unwrap();

        let g_h = state.domain_h.group_gen();
        let g_k = state.domain_k.group_gen();

        let mut query_set = QuerySet::new();

        // Outer sumcheck

        // First round polys
        query_set.insert(("w".into(), ("beta".into(), beta)));
        query_set.insert(("z_a".into(), ("beta".into(), beta)));
        query_set.insert(("z_b".into(), ("beta".into(), beta)));

        // Second round polys
        query_set.insert(("t".into(), ("beta".into(), beta)));
        query_set.insert(("z_1".into(), ("beta".into(), beta)));
        query_set.insert(("z_1".into(), ("g * beta".into(), g_h * beta)));
        query_set.insert(("h_1".into(), ("beta".into(), beta)));

        // Inner sumcheck

        // Third round polys
        query_set.insert(("z_2".into(), ("gamma".into(), gamma)));
        query_set.insert(("z_2".into(), ("g * gamma".into(), g_k * gamma)));
        query_set.insert(("h_2".into(), ("gamma".into(), gamma)));
        query_set.insert(("a_row".into(), ("gamma".into(), gamma)));
        query_set.insert(("a_col".into(), ("gamma".into(), gamma)));
        query_set.insert(("a_row_col".into(), ("gamma".into(), gamma)));
        query_set.insert(("a_val".into(), ("gamma".into(), gamma)));
        query_set.insert(("b_row".into(), ("gamma".into(), gamma)));
        query_set.insert(("b_col".into(), ("gamma".into(), gamma)));
        query_set.insert(("b_row_col".into(), ("gamma".into(), gamma)));
        query_set.insert(("b_val".into(), ("gamma".into(), gamma)));
        query_set.insert(("c_row".into(), ("gamma".into(), gamma)));
        query_set.insert(("c_col".into(), ("gamma".into(), gamma)));
        query_set.insert(("c_row_col".into(), ("gamma".into(), gamma)));
        query_set.insert(("c_val".into(), ("gamma".into(), gamma)));

        Ok((query_set, state))
    }
}
