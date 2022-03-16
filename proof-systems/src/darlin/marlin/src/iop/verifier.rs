#![allow(non_snake_case)]

use crate::iop::indexer::IndexInfo;
use crate::iop::*;

use algebra::PrimeField;
use algebra::{get_best_evaluation_domain, EvaluationDomain};
use fiat_shamir::FiatShamirRng;
use poly_commit::QueryMap;

/// State of the IOP verifier
pub struct VerifierState<F: PrimeField> {
    pub(crate) domain_h: Box<dyn EvaluationDomain<F>>,
    pub(crate) domain_k: Box<dyn EvaluationDomain<F>>,

    pub(crate) first_round_msg: Option<VerifierFirstMsg<F>>,
    pub(crate) second_round_msg: Option<VerifierSecondMsg<F>>,

    pub(crate) gamma: Option<F>,
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

        let alpha = F::read_bits(
            fs_rng
                .get_challenge::<128>()?
                .to_vec()
        ).map_err(|e| Error::Other(e.to_string()))?;

        if domain_h.evaluate_vanishing_polynomial(alpha).is_zero() {
            Err(Error::Other(
                "Sampled an alpha challenge belonging to H domain".to_owned(),
            ))?
        }

        let eta = F::read_bits(
            fs_rng
                .get_challenge::<128>()?
                .to_vec()
        ).map_err(|e| Error::Other(e.to_string()))?;

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
        let beta = F::read_bits(
            fs_rng
                .get_challenge::<128>()?
                .to_vec()
        ).map_err(|e| Error::Other(e.to_string()))?;

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
        let gamma = F::read_bits(
            fs_rng
                .get_challenge::<128>()?
                .to_vec()
        ).map_err(|e| Error::Other(e.to_string()))?;

        state.gamma = Some(gamma);
        Ok(state)
    }

    /// Output the query state and next round state.
    pub fn verifier_query_map(
        state: VerifierState<F>,
    ) -> Result<(QueryMap<F>, VerifierState<F>), Error> {
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

        let mut query_map = QueryMap::new();

        // Outer sumcheck

        // First round polys
        query_map.insert(("w".into(), "beta".into()), beta);
        query_map.insert(("y_a".into(), "beta".into()), beta);
        query_map.insert(("y_b".into(), "beta".into()), beta);

        // Second round polys
        query_map.insert(("u_1".into(), "beta".into()), beta);
        query_map.insert(("u_1".into(), "g_h * beta".into()), g_h * beta);
        query_map.insert(("h_1".into(), "beta".into()), beta);

        // Inner sumcheck

        // Third round polys
        query_map.insert(("u_2".into(), "gamma".into()), gamma);
        query_map.insert(("u_2".into(), "g_k * gamma".into()), g_k * gamma);
        query_map.insert(("h_2".into(), "gamma".into()), gamma);
        query_map.insert(("a_row".into(), "gamma".into()), gamma);
        query_map.insert(("a_col".into(), "gamma".into()), gamma);
        query_map.insert(("a_row_col".into(), "gamma".into()), gamma);
        query_map.insert(("a_val_row_col".into(), "gamma".into()), gamma);
        query_map.insert(("b_row".into(), "gamma".into()), gamma);
        query_map.insert(("b_col".into(), "gamma".into()), gamma);
        query_map.insert(("b_row_col".into(), "gamma".into()), gamma);
        query_map.insert(("b_val_row_col".into(), "gamma".into()), gamma);
        query_map.insert(("c_row".into(), "gamma".into()), gamma);
        query_map.insert(("c_col".into(), "gamma".into()), gamma);
        query_map.insert(("c_row_col".into(), "gamma".into()), gamma);
        query_map.insert(("c_val_row_col".into(), "gamma".into()), gamma);

        Ok((query_map, state))
    }
}
