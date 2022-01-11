#![allow(non_snake_case)]

use crate::iop::indexer::IndexInfo;
use crate::iop::*;

use algebra::{get_best_evaluation_domain, EvaluationDomain};
use poly_commit::fiat_shamir_rng::FiatShamirRng;
use poly_commit::QuerySet;

/// State of the IOP verifier
pub struct VerifierState<G1: Curve, G2: Curve> {
    /// Domain H.
    pub domain_h: Box<dyn EvaluationDomain<G1::ScalarField>>,

    /// First round verifier message.
    pub first_round_msg: Option<VerifierFirstMsg<G1::ScalarField>>,
    /// Second round verifier message.
    pub second_round_msg: Option<VerifierSecondMsg<G1::ScalarField>>,

    g2: PhantomData<G2>,
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

impl<G1: Curve, G2: Curve> IOP<G1, G2> {
    /// The verifier first round, samples the random challenges `eta` and `alpha` for reducing the R1CS identies
    /// to a sumcheck.
    pub fn verifier_first_round<R: FiatShamirRng>(
        index_info: IndexInfo<G1, G2>,
        fs_rng: &mut R,
    ) -> Result<(VerifierFirstMsg<G1::ScalarField>, VerifierState<G1, G2>), Error> {
        let num_formatted_variables = index_info.num_inputs + index_info.num_witness;
        let num_constraints = index_info.num_constraints;
        let padded_matrix_dim = std::cmp::max(num_formatted_variables, num_constraints);
        let domain_h = get_best_evaluation_domain::<G1::ScalarField>(padded_matrix_dim)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let alpha: G1::ScalarField = fs_rng.squeeze_128_bits_challenge();
        if domain_h.evaluate_vanishing_polynomial(alpha).is_zero() {
            Err(Error::Other(
                "Sampled an alpha challenge belonging to H domain".to_owned(),
            ))?
        }

        let eta: G1::ScalarField = fs_rng.squeeze_128_bits_challenge();

        let msg = VerifierFirstMsg { alpha, eta };

        let new_state = VerifierState {
            domain_h,
            first_round_msg: Some(msg),
            second_round_msg: None,
            g2: PhantomData,
        };

        Ok((msg, new_state))
    }

    /// Second round of the verifier, samples the random challenge `beta` for probing
    /// the outer sumcheck identity.
    pub fn verifier_second_round<R: FiatShamirRng>(
        mut state: VerifierState<G1, G2>,
        fs_rng: &mut R,
    ) -> Result<(VerifierSecondMsg<G1::ScalarField>, VerifierState<G1, G2>), Error> {
        let beta: G1::ScalarField = fs_rng.squeeze_128_bits_challenge();
        if state.domain_h.evaluate_vanishing_polynomial(beta).is_zero() {
            Err(Error::Other(
                "Sampled a beta challenge belonging to H domain".to_owned(),
            ))?
        }

        let msg = VerifierSecondMsg { beta };
        state.second_round_msg = Some(msg);

        Ok((msg, state))
    }

    /// Output the query state and next round state.
    pub fn verifier_query_set<'a, 'b>(
        state: VerifierState<G1, G2>,
    ) -> Result<(QuerySet<'b, G1::ScalarField>, VerifierState<G1, G2>), Error> {
        if state.second_round_msg.is_none() {
            return Err(Error::Other("Second round message is empty".to_owned()));
        }
        let beta = state.second_round_msg.unwrap().beta;

        let g_h = state.domain_h.group_gen();

        let mut query_set = QuerySet::new();

        // First round polys
        query_set.insert(("w".into(), ("beta".into(), beta)));
        query_set.insert(("y_a".into(), ("beta".into(), beta)));
        query_set.insert(("y_b".into(), ("beta".into(), beta)));

        // Second round polys
        query_set.insert(("u_1".into(), ("beta".into(), beta)));
        query_set.insert(("u_1".into(), ("g * beta".into(), g_h * beta)));
        query_set.insert(("h_1".into(), ("beta".into(), beta)));
        query_set.insert(("t".into(), ("beta".into(), beta)));

        Ok((query_set, state))
    }
}
