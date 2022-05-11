#![allow(non_snake_case)]

use crate::iop::indexer::IndexInfo;
use crate::iop::*;

use algebra::{get_best_evaluation_domain, EvaluationDomain, PrimeField};
use fiat_shamir::FiatShamirRng;
use poly_commit::QueryMap;
use std::collections::BTreeSet;
use std::iter::FromIterator;

/// State of the IOP verifier
pub struct VerifierState<F: PrimeField> {
    /// Domain H.
    pub domain_h: Box<dyn EvaluationDomain<F>>,
    /// Domain K.
    pub domain_k: Box<dyn EvaluationDomain<F>>,

    /// First round verifier message.
    pub first_round_msg: Option<VerifierFirstMsg<F>>,
    /// Second round verifier message.
    pub second_round_msg: Option<VerifierSecondMsg<F>>,

    /// Challenge for third round.
    pub gamma: Option<F>,
}

/// First message of the verifier.
#[derive(Copy, Clone)]
pub struct VerifierFirstMsg<F: Field> {
    /// Query for the random polynomial.
    pub alpha: F,
    /// Randomizer for the lincheck for `A`, `B`, and `C`.
    pub eta: F,
}

impl<F: Field> VerifierFirstMsg<F> {
    /// Return a triplet with the randomizers (1, eta, eta^2)
    pub fn get_etas(&self) -> (F, F, F) {
        return (F::one(), self.eta, self.eta.square());
    }
}

/// Second verifier message.
#[derive(Copy, Clone)]
pub struct VerifierSecondMsg<F> {
    /// Query for the second round of polynomials.
    pub beta: F,
}

impl<F: PrimeField> IOP<F> {
    /// The verifier first round, samples the random challenges `eta` and `alpha` for reducing the R1CS identies
    /// to a sumcheck.
    pub fn verifier_first_round<R: FiatShamirRng>(
        index_info: IndexInfo<F>,
        fs_rng: &mut R,
    ) -> Result<(VerifierFirstMsg<F>, VerifierState<F>), Error> {
        let num_formatted_variables = index_info.num_inputs + index_info.num_witness;
        let num_constraints = index_info.num_constraints;
        let padded_matrix_dim = std::cmp::max(num_formatted_variables, num_constraints);
        let domain_h = get_best_evaluation_domain::<F>(padded_matrix_dim)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let domain_k = get_best_evaluation_domain::<F>(index_info.num_non_zero)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let chals = fs_rng.get_many_challenges::<128>(2)?;

        let alpha = F::read_bits(chals[0].to_vec()).map_err(|e| Error::Other(e.to_string()))?;

        if domain_h.evaluate_vanishing_polynomial(alpha).is_zero() {
            Err(Error::Other(
                "Sampled an alpha challenge belonging to H domain".to_owned(),
            ))?
        }

        let eta = F::read_bits(chals[1].to_vec()).map_err(|e| Error::Other(e.to_string()))?;

        let msg = VerifierFirstMsg { alpha, eta };

        let new_state = VerifierState {
            domain_h,
            domain_k,
            first_round_msg: Some(msg),
            second_round_msg: None,
            gamma: None,
        };

        Ok((msg, new_state))
    }

    /// Second round of the verifier, samples the random challenge `beta` for probing
    /// the outer sumcheck identity.
    pub fn verifier_second_round<R: FiatShamirRng>(
        mut state: VerifierState<F>,
        fs_rng: &mut R,
    ) -> Result<(VerifierSecondMsg<F>, VerifierState<F>), Error> {
        let beta = F::read_bits(fs_rng.get_challenge::<128>()?.to_vec())
            .map_err(|e| Error::Other(e.to_string()))?;

        if state.domain_h.evaluate_vanishing_polynomial(beta).is_zero() {
            Err(Error::Other(
                "Sampled a beta challenge belonging to H domain".to_owned(),
            ))?
        }

        let msg = VerifierSecondMsg { beta };
        state.second_round_msg = Some(msg);

        Ok((msg, state))
    }

    /// Third round of the verifier. Samples the random challenge `gamma` for
    /// probing the inner sumcheck identity.
    pub fn verifier_third_round<R: FiatShamirRng>(
        mut state: VerifierState<F>,
        fs_rng: &mut R,
    ) -> Result<VerifierState<F>, Error> {
        let gamma = F::read_bits(fs_rng.get_challenge::<128>()?.to_vec())
            .map_err(|e| Error::Other(e.to_string()))?;

        state.gamma = Some(gamma);
        Ok(state)
    }

    /// Output the query state and next round state.
    pub fn verifier_query_map<'a, 'b>(
        state: VerifierState<F>,
    ) -> Result<(QueryMap<'b, F>, VerifierState<F>), Error> {
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

        let queries_at_beta = BTreeSet::from_iter(vec![
            "x".to_string(),
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

        #[cfg(feature = "commit-vanishing-polys")]
        let (queries_at_alpha, queries_at_beta, queries_at_gamma) = {
            let queries_at_alpha = BTreeSet::from_iter(vec!["v_h".to_string()]);

            let mut queries_at_beta = queries_at_beta;
            queries_at_beta.insert("v_h".to_string());
            queries_at_beta.insert("v_x".to_string());

            let mut queries_at_gamma = queries_at_gamma;
            queries_at_gamma.insert("v_k".to_string());

            (queries_at_alpha, queries_at_beta, queries_at_gamma)
        };

        let query_map = {
            let mut map = QueryMap::new();
            map.insert("beta".to_string(), (beta, queries_at_beta));
            map.insert("gamma".to_string(), (gamma, queries_at_gamma));
            map.insert("g * beta".to_string(), (g_h * beta, queries_at_g_beta));
            map.insert("g * gamma".to_string(), (g_k * gamma, queries_at_g_gamma));
            #[cfg(feature = "commit-vanishing-polys")]
            {
                let alpha = state.first_round_msg.as_ref().unwrap().clone().alpha;
                map.insert("alpha".to_string(), (alpha, queries_at_alpha));
            }
            map
        };

        Ok((query_map, state))
    }
}
