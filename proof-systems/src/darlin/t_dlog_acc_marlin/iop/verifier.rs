#![allow(non_snake_case)]

use crate::darlin::t_dlog_acc_marlin::data_structures::DualSumcheckItem;
use crate::darlin::t_dlog_acc_marlin::iop::indexer::IndexInfo;
use crate::darlin::t_dlog_acc_marlin::iop::IOP;
use algebra::{get_best_evaluation_domain, Curve, EvaluationDomain, Group};
use marlin::iop::Error;
use poly_commit::fiat_shamir_rng::FiatShamirRng;
use poly_commit::QuerySet;
use r1cs_core::SynthesisError;
use std::marker::PhantomData;

/// State of the IOP verifier
pub struct VerifierState<'a, G1: Curve, G2: Curve> {
    /// Domain H.
    pub domain_h: Box<dyn EvaluationDomain<G1::ScalarField>>,
    /// the previous inner-sumcheck accumulator
    pub previous_inner_sumcheck_acc: &'a DualSumcheckItem<G2, G1>,

    /// First round verifier message.
    pub first_round_msg: Option<VerifierFirstMsg<G1::ScalarField>>,
    /// Second round verifier message.
    pub second_round_msg: Option<VerifierSecondMsg<G1::ScalarField>>,
    /// Third round verifier message.
    pub third_round_msg: Option<VerifierThirdMsg<G1::ScalarField>>,

    g2: PhantomData<G2>,
}

/// First message of the verifier.
#[derive(Clone)]
pub struct VerifierFirstMsg<G: Group> {
    /// Query for the random polynomial.
    pub alpha: G::ScalarField,
    /// Randomizer for the lincheck for `A`, `B`, and `C`.
    pub eta: Vec<G::ScalarField>,
}

/// Second verifier message.
#[derive(Copy, Clone)]
pub struct VerifierSecondMsg<G: Group> {
    /// Query for the second round of polynomials.
    pub beta: G::ScalarField,
}

/// Third verifier message.
#[derive(Copy, Clone)]
pub struct VerifierThirdMsg<G: Group> {
    /// Query for the third round of polynomials.
    pub gamma: G::ScalarField,
    /// Randomizer for the aggregation of circuit polynomials.
    pub lambda: G::ScalarField,
}

impl<G1: Curve, G2: Curve> IOP<G1, G2> {
    /// Preparation of the verifier.
    pub fn verifier_init<'a>(
        index_info: &IndexInfo<G1, G2>,
        previous_inner_sumcheck_acc: &'a DualSumcheckItem<G2, G1>,
    ) -> Result<VerifierState<'a, G1, G2>, Error> {
        let num_formatted_variables = index_info.num_inputs + index_info.num_witness;
        let num_constraints = index_info.num_constraints;
        let padded_matrix_dim = std::cmp::max(num_formatted_variables, num_constraints);
        let domain_h = get_best_evaluation_domain::<G1::ScalarField>(padded_matrix_dim)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let state = VerifierState {
            domain_h,
            previous_inner_sumcheck_acc,
            first_round_msg: None,
            second_round_msg: None,
            third_round_msg: None,
            g2: PhantomData,
        };
        Ok(state)
    }
    /// The verifier first round, samples the random challenges `eta` and `alpha` for reducing the R1CS identies
    /// to a sumcheck.
    pub fn verifier_first_round<'a, R: FiatShamirRng>(
        mut state: VerifierState<'a, G1, G2>,
        fs_rng: &mut R,
    ) -> Result<(VerifierFirstMsg<G1::ScalarField>, VerifierState<'a, G1, G2>), Error> {
        let alpha: G1::ScalarField = fs_rng.squeeze_128_bits_challenge();
        if state
            .domain_h
            .evaluate_vanishing_polynomial(alpha)
            .is_zero()
        {
            Err(Error::Other(
                "Sampled an alpha challenge belonging to H domain".to_owned(),
            ))?
        }

        let eta: Vec<_> = (0..3)
            .into_iter()
            .map(|_| fs_rng.squeeze_128_bits_challenge())
            .collect();

        let msg = VerifierFirstMsg { alpha, eta };
        state.first_round_msg = Some(msg.clone());

        Ok((msg, state))
    }

    /// Second round of the verifier, samples the random challenge `beta` for probing
    /// the outer sumcheck identity.
    pub fn verifier_second_round<'a, R: FiatShamirRng>(
        mut state: VerifierState<'a, G1, G2>,
        fs_rng: &mut R,
    ) -> Result<
        (
            VerifierSecondMsg<G1::ScalarField>,
            VerifierState<'a, G1, G2>,
        ),
        Error,
    > {
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

    /// Third round of the verifier, samples the random challenges `gamma` and `lambda` for the
    /// inner sumcheck aggregation.
    pub fn verifier_third_round<'a, R: FiatShamirRng>(
        mut state: VerifierState<'a, G1, G2>,
        fs_rng: &mut R,
    ) -> Result<(VerifierThirdMsg<G1::ScalarField>, VerifierState<'a, G1, G2>), Error> {
        let gamma: G1::ScalarField = fs_rng.squeeze_128_bits_challenge();
        if state
            .domain_h
            .evaluate_vanishing_polynomial(gamma)
            .is_zero()
        {
            Err(Error::Other(
                "Sampled a gamma challenge belonging to H domain".to_owned(),
            ))?
        }

        let lambda: G1::ScalarField = fs_rng.squeeze_128_bits_challenge();

        let msg = VerifierThirdMsg { gamma, lambda };
        state.third_round_msg = Some(msg);

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
        let alpha = state.first_round_msg.as_ref().unwrap().alpha;
        let prev_alpha = state.previous_inner_sumcheck_acc.1.alpha;
        let gamma = state.third_round_msg.unwrap().gamma;

        let g_h = state.domain_h.group_gen();

        let mut query_set = QuerySet::new();

        // First round polys
        query_set.insert(("x".into(), ("beta".into(), beta)));
        query_set.insert(("w".into(), ("beta".into(), beta)));
        query_set.insert(("y_a".into(), ("beta".into(), beta)));
        query_set.insert(("y_b".into(), ("beta".into(), beta)));

        // Second round polys
        query_set.insert(("u_1".into(), ("beta".into(), beta)));
        query_set.insert(("u_1".into(), ("g * beta".into(), g_h * beta)));
        query_set.insert(("h_1".into(), ("beta".into(), beta)));
        query_set.insert(("t".into(), ("beta".into(), beta)));

        // Inner sumcheck aggregation polys
        query_set.insert(("curr_bridging_poly".into(), ("alpha".into(), alpha)));
        query_set.insert((
            "prev_bridging_poly".into(),
            ("prev_alpha".into(), prev_alpha),
        ));
        query_set.insert(("curr_bridging_poly".into(), ("gamma".into(), gamma)));
        query_set.insert(("prev_bridging_poly".into(), ("gamma".into(), gamma)));
        query_set.insert(("curr_t_acc_poly".into(), ("beta".into(), beta)));
        query_set.insert(("prev_t_acc_poly".into(), ("beta".into(), beta)));

        // Dlog accumulation poly
        query_set.insert(("prev_bullet_poly".into(), ("gamma".into(), gamma)));

        Ok((query_set, state))
    }
}
