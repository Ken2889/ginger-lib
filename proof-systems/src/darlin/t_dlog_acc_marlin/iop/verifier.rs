#![allow(non_snake_case)]

use crate::darlin::accumulators::t_dlog::DualTDLogItem;
use crate::darlin::t_dlog_acc_marlin::iop::indexer::IndexInfo;
use crate::darlin::t_dlog_acc_marlin::iop::IOP;
use crate::darlin::IPACurve;
use algebra::{get_best_evaluation_domain, DualCycle, EvaluationDomain, Field, FromBits};
use fiat_shamir::FiatShamirRng;
use marlin::iop::Error;
use num_traits::{One, Zero};
use poly_commit::QueryMap;
use r1cs_core::SynthesisError;
use std::collections::BTreeSet;
use std::iter::FromIterator;
use std::marker::PhantomData;

/// State of the IOP verifier
pub struct VerifierState<'a, G1, G2>
where
    G1: IPACurve,
    G2: IPACurve,
    G1: DualCycle<G2>,
{
    /// Domain H.
    pub domain_h: Box<dyn EvaluationDomain<G1::ScalarField>>,
    /// the previous inner-sumcheck accumulator
    pub previous_acc: &'a DualTDLogItem<G2, G1>,

    /// First round verifier message.
    pub first_round_msg: Option<VerifierFirstMsg<G1>>,
    /// Second round verifier message.
    pub second_round_msg: Option<VerifierSecondMsg<G1>>,
    /// Third round verifier message.
    pub third_round_msg: Option<VerifierThirdMsg<G1>>,

    g2: PhantomData<G2>,
}

/// First message of the verifier.
#[derive(Clone)]
pub struct VerifierFirstMsg<G: IPACurve> {
    /// Query for the random polynomial.
    pub alpha: G::ScalarField,
    /// Randomizer for the lincheck for `A`, `B`, and `C`.
    pub eta: G::ScalarField,
}

impl<G: IPACurve> VerifierFirstMsg<G> {
    /// Return a vector with the three randomizers [1, eta, eta^2]
    pub fn get_etas(&self) -> [G::ScalarField; 3] {
        return [G::ScalarField::one(), self.eta, self.eta.square()];
    }
}

/// Second verifier message.
#[derive(Copy, Clone)]
pub struct VerifierSecondMsg<G: IPACurve> {
    /// Query for the second round of polynomials.
    pub beta: G::ScalarField,
}

/// Third verifier message.
#[derive(Copy, Clone)]
pub struct VerifierThirdMsg<G: IPACurve> {
    /// Query for the third round of polynomials.
    pub gamma: G::ScalarField,
    /// Randomizer for the aggregation of circuit polynomials.
    pub lambda: G::ScalarField,
    pub etas: [G::ScalarField; 3],
}

impl<G1, G2> IOP<G1, G2>
where
    G1: IPACurve,
    G2: IPACurve,
    G1: DualCycle<G2>,
{
    /// Preparation of the verifier.
    pub fn verifier_init<'a>(
        index_info: &IndexInfo<G1>,
        previous_acc: &'a DualTDLogItem<G2, G1>,
    ) -> Result<VerifierState<'a, G1, G2>, Error> {
        let num_formatted_variables = index_info.num_inputs + index_info.num_witness;
        let num_constraints = index_info.num_constraints;
        let padded_matrix_dim = std::cmp::max(num_formatted_variables, num_constraints);
        let domain_h = get_best_evaluation_domain::<G1::ScalarField>(padded_matrix_dim)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let state = VerifierState {
            domain_h,
            previous_acc,
            first_round_msg: None,
            second_round_msg: None,
            third_round_msg: None,
            g2: PhantomData,
        };
        Ok(state)
    }
    /// The verifier first round, samples the random challenges `eta` and `alpha` for reducing the R1CS identies
    /// to a sumcheck.
    pub fn verifier_first_round<'a, FS: FiatShamirRng>(
        mut state: VerifierState<'a, G1, G2>,
        fs_rng: &mut FS,
    ) -> Result<(VerifierFirstMsg<G1>, VerifierState<'a, G1, G2>), Error> {
        let chals = fs_rng.get_many_challenges::<128>(2)?;

        let alpha = G1::ScalarField::read_bits(chals[0].to_vec())
            .map_err(|e| Error::Other(e.to_string()))?;

        if state
            .domain_h
            .evaluate_vanishing_polynomial(alpha)
            .is_zero()
        {
            Err(Error::Other(
                "Sampled an alpha challenge belonging to H domain".to_owned(),
            ))?
        }

        let eta = G1::ScalarField::read_bits(chals[1].to_vec())
            .map_err(|e| Error::Other(e.to_string()))?;

        let msg = VerifierFirstMsg { alpha, eta };
        state.first_round_msg = Some(msg.clone());

        Ok((msg, state))
    }

    /// Second round of the verifier, samples the random challenge `beta` for probing
    /// the outer sumcheck identity.
    pub fn verifier_second_round<'a, R: FiatShamirRng>(
        mut state: VerifierState<'a, G1, G2>,
        fs_rng: &mut R,
    ) -> Result<(VerifierSecondMsg<G1>, VerifierState<'a, G1, G2>), Error> {
        let beta = G1::ScalarField::read_bits(fs_rng.get_challenge::<128>()?.to_vec())
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

    /// Third round of the verifier, samples the random challenges `gamma` and `lambda` for the
    /// inner sumcheck aggregation.
    pub fn verifier_third_round<'a, R: FiatShamirRng>(
        mut state: VerifierState<'a, G1, G2>,
        fs_rng: &mut R,
    ) -> Result<(VerifierThirdMsg<G1>, VerifierState<'a, G1, G2>), Error> {
        let chals = fs_rng.get_many_challenges::<128>(2)?;

        let gamma = G1::ScalarField::read_bits(chals[0].to_vec())
            .map_err(|e| Error::Other(e.to_string()))?;

        if state
            .domain_h
            .evaluate_vanishing_polynomial(gamma)
            .is_zero()
        {
            Err(Error::Other(
                "Sampled a gamma challenge belonging to H domain".to_owned(),
            ))?
        }

        let lambda = G1::ScalarField::read_bits(chals[0].to_vec())
            .map_err(|e| Error::Other(e.to_string()))?;

        let verifier_first_msg = state.first_round_msg.as_ref().expect(
            "ProverState should include verifier_first_msg when prover_third_round is called",
        );
        let etas = verifier_first_msg.get_etas();
        let etas_prime = state.previous_acc.non_native[0]
            .t_item
            .succinct_descriptor
            .etas;

        let etas_second = etas
            .iter()
            .zip(etas_prime.iter())
            .map(|(&eta, &eta_prime)| eta + gamma * eta_prime);

        let msg = VerifierThirdMsg {
            gamma,
            lambda,
            etas: array_init::from_iter(etas_second).unwrap(),
        };
        state.third_round_msg = Some(msg);

        Ok((msg, state))
    }

    /// Output the query state and next round state.
    pub fn verifier_query_map<'a, 'b>(
        state: VerifierState<G1, G2>,
    ) -> Result<(QueryMap<'b, G1::ScalarField>, VerifierState<G1, G2>), Error> {
        if state.second_round_msg.is_none() {
            return Err(Error::Other("Second round message is empty".to_owned()));
        }
        let beta = state.second_round_msg.unwrap().beta;
        let alpha = state.first_round_msg.as_ref().unwrap().alpha;
        let prev_alpha = state.previous_acc.non_native[0]
            .t_item
            .succinct_descriptor
            .alpha;
        let gamma = state.third_round_msg.unwrap().gamma;

        let g_h = state.domain_h.group_gen();

        let queries_at_alpha = BTreeSet::from_iter(vec!["curr_bridging_poly".to_string()]);

        let queries_at_beta = BTreeSet::from_iter(vec![
            "x".to_string(),
            "w".to_string(),
            "y_a".to_string(),
            "y_b".to_string(),
            "u_1".to_string(),
            "h_1".to_string(),
            "t".to_string(),
            "curr_t_acc_poly".to_string(),
            "prev_t_acc_poly".to_string(),
        ]);
        let queries_at_gamma = BTreeSet::from_iter(vec![
            "curr_bridging_poly".to_string(),
            "prev_bridging_poly".to_string(),
            "prev_bullet_poly".to_string(),
        ]);
        let queries_at_g_beta = BTreeSet::from_iter(vec!["u_1".to_string()]);
        let queries_at_prev_alpha = BTreeSet::from_iter(vec!["prev_bridging_poly".to_string()]);

        let query_map = {
            let mut map = QueryMap::new();
            map.insert("alpha".to_string(), (alpha, queries_at_alpha));
            map.insert("beta".to_string(), (beta, queries_at_beta));
            map.insert("gamma".to_string(), (gamma, queries_at_gamma));
            map.insert("g * beta".to_string(), (g_h * beta, queries_at_g_beta));
            map.insert(
                "prev_alpha".to_string(),
                (prev_alpha, queries_at_prev_alpha),
            );
            map
        };

        Ok((query_map, state))
    }
}
