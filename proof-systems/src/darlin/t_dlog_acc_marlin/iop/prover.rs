#![allow(non_snake_case)]

use crate::darlin::accumulators::inner_sumcheck::SuccinctInnerSumcheckDescriptor;
use crate::darlin::accumulators::t_dlog::DualTDLogItem;
use crate::darlin::t_dlog_acc_marlin::iop::indexer::Index;
use crate::darlin::t_dlog_acc_marlin::iop::verifier::{
    VerifierFirstMsg, VerifierSecondMsg, VerifierThirdMsg,
};
use crate::darlin::t_dlog_acc_marlin::iop::IOP;
use crate::darlin::EndoMulCurve;
use algebra::{
    get_best_evaluation_domain, DualCycle, EvaluationDomain, Evaluations as EvaluationsOnDomain,
    Field,
};
use bench_utils::{end_timer, start_timer};
use marlin::iop::sparse_linear_algebra::mat_vec_mul;
use marlin::iop::{BoundaryPolynomial, Error, LagrangeKernel};
use num_traits::Zero;
use poly_commit::{LabeledPolynomial, Polynomial};
use r1cs_core::{ConstraintSynthesizer, ConstraintSystem, SynthesisError, SynthesisMode};
use rand_core::RngCore;
use rayon::prelude::*;

const C: usize = poly_commit::degree_correction_for_zk_security();

/// State for the IOP prover.
pub struct ProverState<'a, G1, G2>
where
    G1: EndoMulCurve,
    G2: EndoMulCurve,
    G1: DualCycle<G2>,
{
    formatted_input_assignment: Vec<G1::ScalarField>,
    witness_assignment: Vec<G1::ScalarField>,

    // the polynomial associated to the formatted public input.
    x_poly: LabeledPolynomial<G1::ScalarField>,

    // the witness polynomial w(X), normalized by the vanishing polynomial of
    // the input domain, such that y(X) = x(X) + w(X)*Z_I(X).
    w_poly: Option<LabeledPolynomial<G1::ScalarField>>,
    my_polys: Option<(
        LabeledPolynomial<G1::ScalarField>,
        LabeledPolynomial<G1::ScalarField>,
    )>,

    index: &'a Index<G1>,

    /// the previous accumulator
    acc: &'a DualTDLogItem<G2, G1>,

    /// the random values sent by the verifier in the first round
    verifier_first_msg: Option<VerifierFirstMsg<G1>>,

    /// domain X, sized for the public input
    domain_x: Box<dyn EvaluationDomain<G1::ScalarField>>,

    /// domain H, sized for constraints
    domain_h: Box<dyn EvaluationDomain<G1::ScalarField>>,
}

impl<'a, G1, G2> ProverState<'a, G1, G2>
where
    G1: EndoMulCurve,
    G2: EndoMulCurve,
    G1: DualCycle<G2>,
{
    /// Get the public input.
    pub fn public_input(&self) -> Vec<G1::ScalarField> {
        IOP::<G1, G2>::unformat_public_input(&self.formatted_input_assignment)
    }
    /// Return the variable vector, with input variables and witness variables already indexed
    /// according to the treatment of the input domain `domain_x` as a subdomain of the full
    /// Lagrange domain `domain_h`.
    pub fn full_variable_vector(&self) -> Vec<G1::ScalarField> {
        let domain_x_size = self.domain_x.size();
        let mut padded_public_input = vec![G1::ScalarField::zero(); self.domain_h.size()];
        for (i, el) in self.formatted_input_assignment.iter().enumerate() {
            let idx = self
                .domain_h
                .reindex_by_subdomain(domain_x_size, i)
                .unwrap();
            padded_public_input[idx] = *el;
        }
        for (i, el) in self.witness_assignment.iter().enumerate() {
            let idx = self
                .domain_h
                .reindex_by_subdomain(domain_x_size, i + domain_x_size)
                .unwrap();
            padded_public_input[idx] = *el;
        }
        padded_public_input
    }
}

pub struct ProverInitOracles<G: EndoMulCurve> {
    /// The public input polynomial `x`
    pub x: LabeledPolynomial<G::ScalarField>,
}

impl<G: EndoMulCurve> ProverInitOracles<G> {
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<G::ScalarField>> {
        vec![&self.x].into_iter()
    }
}

/// The first set of prover oracles.
pub struct ProverFirstOracles<G: EndoMulCurve> {
    /// The randomized witness polynomial `w`.
    pub w: LabeledPolynomial<G::ScalarField>,
    /// The randomized y_A(X)= Sum_{z in H} A(X,z)*y(z)
    pub y_a: LabeledPolynomial<G::ScalarField>,
    /// The randomized y_B(X)= Sum_{z in H} B(X,z)*y(z)
    pub y_b: LabeledPolynomial<G::ScalarField>,
}

impl<G: EndoMulCurve> ProverFirstOracles<G> {
    /// Iterate over the polynomials output by the prover in the first round.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<G::ScalarField>> {
        vec![&self.w, &self.y_a, &self.y_b].into_iter()
    }
}

/// The second set of prover oracles.
pub struct ProverSecondOracles<G: EndoMulCurve> {
    /// The boundary polynomial U_1(X) for the outer sumcheck
    pub u_1: LabeledPolynomial<G::ScalarField>,
    /// The quotient polynomial h_1(X) in the outer sumcheck identity.
    pub h_1: LabeledPolynomial<G::ScalarField>,
    /// The circuit polynomial T_eta(alpha, X).
    pub t: LabeledPolynomial<G::ScalarField>,
}

impl<G: EndoMulCurve> ProverSecondOracles<G> {
    /// Iterate over the polynomials output by the prover in the second round.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<G::ScalarField>> {
        vec![&self.u_1, &self.h_1, &self.t].into_iter()
    }
}

/// The third set of prover oracles.
pub struct ProverThirdOracles<G: EndoMulCurve> {
    /// The current bridging polynomial
    pub curr_bridging_poly: LabeledPolynomial<G::ScalarField>,
    /// The previous bridging polynomial
    pub prev_bridging_poly: LabeledPolynomial<G::ScalarField>,
}

impl<G: EndoMulCurve> ProverThirdOracles<G> {
    /// Iterate over the polynomials output by the prover in the third round.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<G::ScalarField>> {
        vec![&self.curr_bridging_poly, &self.prev_bridging_poly].into_iter()
    }
}

/// The fourth set of prover oracles.
pub struct ProverFourthOracles<G: EndoMulCurve> {
    /// The new circuit polynomial
    pub curr_t_acc_poly: LabeledPolynomial<G::ScalarField>,
}

impl<G: EndoMulCurve> ProverFourthOracles<G> {
    /// Iterate over the polynomials output by the prover in the third round.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<G::ScalarField>> {
        vec![&self.curr_t_acc_poly].into_iter()
    }
}

/// The polynomials associated to the accumulators.
pub struct ProverAccumulatorOracles<G: EndoMulCurve> {
    /// The inner sumcheck accumulator polynomial.
    pub prev_t_acc_poly: LabeledPolynomial<G::ScalarField>,
    /// The bullet polynomial of the previous dlog accumulator.
    pub prev_bullet_poly: LabeledPolynomial<G::ScalarField>,
}

impl<G: EndoMulCurve> ProverAccumulatorOracles<G> {
    /// Iterate over the accumulator polynomials.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<G::ScalarField>> {
        vec![&self.prev_t_acc_poly, &self.prev_bullet_poly].into_iter()
    }
}

/* The prover rounds
*/
impl<G1, G2> IOP<G1, G2>
where
    G1: EndoMulCurve,
    G2: EndoMulCurve,
    G1: DualCycle<G2>,
{
    /// Preparation of the prover, computes the witness vector `y`.
    pub fn prover_init<'a, C: ConstraintSynthesizer<G1::ScalarField>>(
        index: &'a Index<G1>,
        c: C,
        acc: &'a DualTDLogItem<G2, G1>,
    ) -> Result<(ProverInitOracles<G1>, ProverState<'a, G1, G2>), Error> {
        let init_time = start_timer!(|| "IOP::Prover::Init");

        let witnesses_time = start_timer!(|| "Compute witnesses");
        let mode = SynthesisMode::Prove {
            construct_matrices: false,
        };
        let mut pcs = ConstraintSystem::new(mode);
        c.generate_constraints(&mut pcs)?;
        end_timer!(witnesses_time);

        let ConstraintSystem {
            input_assignment: formatted_input_assignment,
            aux_assignment: witness_assignment,
            num_constraints,
            ..
        } = pcs;

        let num_input_variables = formatted_input_assignment.len();
        let num_witness_variables = witness_assignment.len();
        if index.index_info.num_constraints != num_constraints
            || num_input_variables != index.index_info.num_inputs
            || num_witness_variables != index.index_info.num_witness
        {
            return Err(Error::InstanceDoesNotMatchIndex);
        }

        let num_formatted_variables = num_input_variables + num_witness_variables;
        let padded_matrix_dim = std::cmp::max(num_formatted_variables, num_constraints);
        let domain_h = get_best_evaluation_domain::<G1::ScalarField>(padded_matrix_dim)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let domain_x = get_best_evaluation_domain::<G1::ScalarField>(num_input_variables)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let x_time = start_timer!(|| "Computing x polynomial and evals");
        let x_poly = EvaluationsOnDomain::from_vec_and_domain(
            formatted_input_assignment.clone(),
            domain_x.clone(),
        )
        .interpolate();
        let x_poly = LabeledPolynomial::new("x".to_string(), x_poly, false);

        end_timer!(x_time);

        let prover_state = ProverState {
            formatted_input_assignment,
            witness_assignment,
            x_poly: x_poly.clone(),
            w_poly: None,
            my_polys: None,
            index,
            verifier_first_msg: None,
            acc,
            domain_h,
            domain_x,
        };

        let oracles = ProverInitOracles { x: x_poly };

        end_timer!(init_time);

        Ok((oracles, prover_state))
    }

    /// Prover first round of the algebraic oracle proof, the initial round in [HGB].
    /// Determines the oracles for the witness-related polynomials
    ///   `w(X)`, `y_A(X)` and `y_B(X)`
    /// [HGB]: https://eprint.iacr.org/2021/930
    pub fn prover_first_round<'a, R: RngCore>(
        mut state: ProverState<'a, G1, G2>,
        zk: bool,
        rng: &mut R,
    ) -> Result<(ProverFirstOracles<G1>, ProverState<'a, G1, G2>), Error> {
        let round_time = start_timer!(|| "IOP::Prover::FirstRound");
        let domain_h = &state.domain_h;
        let domain_x = &state.domain_x;

        let x_time = start_timer!(|| "Computing x polynomial evaluations");
        // Evaluate the input polynomial x(X) over H.
        let x_evals = domain_h.fft(&state.x_poly.polynomial());
        end_timer!(x_time);

        /* Compute the normalized witness polynomial w(X) which allows easy
        combination with the input polynomial,
            y(X) = x(X) + z_I(X)* w(X) mod (X^n-1).
        */
        let ratio = domain_h.size() / domain_x.size();

        let mut w_extended = state.witness_assignment.clone();
        w_extended.extend(vec![
            G1::ScalarField::zero();
            domain_h.size()
                - domain_x.size()
                - state.witness_assignment.len()
        ]);

        let w_poly_time = start_timer!(|| "Computing w polynomial");

        // Compute the domain evaluations of w(X) - x(X) on H \ I by from
        // the witness vector w and x, and set it zero on the input domain I.
        // TODO: Let us use reindex_by_subdomain.
        let w_poly_evals = (0..domain_h.size())
            .into_iter()
            .map(|k| {
                // The input domain I is a subgroup of H, with corresponding indices
                // as multiples of `ratio`.
                if k % ratio == 0 {
                    G1::ScalarField::zero()
                } else {
                    // The mapping of the witness vector to values on H.
                    w_extended[k - (k / ratio) - 1] - &x_evals[k]
                }
            })
            .collect();

        // Maximum degree of w_poly before dividing by the vanishing polynomial Z_I(X)
        // of the input domain I is equal to
        //       |H| - 1,  if non-zk
        //       |H| + C,  if zk
        // which can be summarized as:
        //       deg(w) <= |H| - 1 + zk * (1 + C)
        // with zk = 1 / 0, and C the correction given by poly-commit.
        let w_poly = {
            let w = EvaluationsOnDomain::from_vec_and_domain(w_poly_evals, domain_h.clone())
                .interpolate();
            if zk {
                let mut randomization_poly = Polynomial::rand(C, rng);
                randomization_poly = randomization_poly.mul_by_vanishing_poly(domain_h.size());
                let w = &w + &randomization_poly;

                w
            } else {
                w
            }
        };
        let (w_poly, remainder) = w_poly.divide_by_vanishing_poly(&domain_x).unwrap();
        assert!(remainder.is_zero());
        // w_poly is divisible by Z_I(X) because we set w = 0 on I.
        end_timer!(w_poly_time);

        // For M=A,B, compute domain evaluations of y_M(X) = Sum_{z in H} M(X,z)*y(z)
        // over H
        let variable_vector = state.full_variable_vector();

        let eval_y_a_time = start_timer!(|| "Evaluating y_A");
        let y_a = mat_vec_mul(&state.index.a, &variable_vector);
        end_timer!(eval_y_a_time);

        let eval_y_b_time = start_timer!(|| "Evaluating y_B");
        let y_b = mat_vec_mul(&state.index.b, &variable_vector);
        end_timer!(eval_y_b_time);

        // For M=A,B compute the optionally randomized y_M^(X) from the domain evaluations
        let y_a_poly_time = start_timer!(|| "Computing y_A polynomial");
        // Note that we do not re-index y_a by the input domain.
        // (See the comment for `fn arithmetize_matrix`)
        let y_a_poly = {
            let y_a = EvaluationsOnDomain::from_vec_and_domain(y_a, domain_h.clone()).interpolate();
            if zk {
                let mut randomization_poly = Polynomial::rand(C, rng);
                randomization_poly = randomization_poly.mul_by_vanishing_poly(domain_h.size());
                let y_a = &y_a + &randomization_poly;

                y_a
            } else {
                y_a
            }
        };
        end_timer!(y_a_poly_time);

        let y_b_poly_time = start_timer!(|| "Computing y_B polynomial");
        let y_b_poly = {
            let y_b = EvaluationsOnDomain::from_vec_and_domain(y_b, domain_h.clone()).interpolate();
            if zk {
                let mut randomization_poly = Polynomial::rand(C, rng);
                randomization_poly = randomization_poly.mul_by_vanishing_poly(domain_h.size());
                let y_b = &y_b + &randomization_poly;

                y_b
            } else {
                y_b
            }
        };
        end_timer!(y_b_poly_time);

        assert!(w_poly.degree() <= domain_h.size() - 1 + zk as usize * (1 + C) - domain_x.size());
        assert!(y_a_poly.degree() <= domain_h.size() - 1 + zk as usize * (1 + C));
        assert!(y_b_poly.degree() <= domain_h.size() - 1 + zk as usize * (1 + C));

        let w = LabeledPolynomial::new("w".to_string(), w_poly, zk);
        let y_a = LabeledPolynomial::new("y_a".to_string(), y_a_poly, zk);
        let y_b = LabeledPolynomial::new("y_b".to_string(), y_b_poly, zk);

        let oracles = ProverFirstOracles {
            w: w.clone(),
            y_a: y_a.clone(),
            y_b: y_b.clone(),
        };

        state.w_poly = Some(w);
        state.my_polys = Some((y_a, y_b));
        end_timer!(round_time);

        Ok((oracles, state))
    }

    /// Returns the ratio of the sizes of `domain` and `subdomain` or an Error if
    /// `subdomain` is not a subdomain of `domain`.
    fn get_subdomain_step(
        domain: &Box<dyn EvaluationDomain<G1::ScalarField>>,
        subdomain: &Box<dyn EvaluationDomain<G1::ScalarField>>,
    ) -> Result<usize, Error> {
        if domain.size() % subdomain.size() != 0 {
            Err(Error::Other(
                "domain size not divisible by subdomain size".to_owned(),
            ))?
        }
        let step = domain.size() / subdomain.size();
        if subdomain.group_gen() != domain.group_gen().pow(&[step as u64]) {
            Err(Error::Other(
                "domain and subdomain have inconsistent generators".to_owned(),
            ))?
        }
        Ok(step)
    }

    /// Prover second round of the algebraic oracle proof, the "outer sumcheck" that
    /// results from batching and reducing the R1CS identities.
    /// Determines the oracles for `T(alpha, X)`, `U_1(X)` and `h_1(X)`.
    // Note: the outer sumcheck identity is
    //      T(alpha,X) * y(X) - L_H(X,alpha) * y_eta(X) = U_1(gX) - U_1(X) + h_1(X) * (X^n-1),
    // with
    //      y(X) = x(X) + (X^l-1) * w(X)
    //      y_eta(X) = y_A(X) + eta * y_B(X) + eta^2 * y_A(X) * y_B(X)
    // Even though `T(alpha,X)` can be computed from public data, the prover still provides a
    // commitment for it in order to make inner-sumcheck aggregation possible.
    pub fn prover_second_round<'a, R: RngCore>(
        ver_message: &VerifierFirstMsg<G1>,
        mut state: ProverState<'a, G1, G2>,
        zk: bool,
        rng: &mut R,
    ) -> Result<(ProverSecondOracles<G1>, ProverState<'a, G1, G2>), Error> {
        let round_time = start_timer!(|| "IOP::Prover::SecondRound");

        let domain_h = &state.domain_h;

        let alpha = ver_message.alpha;
        let eta = &ver_message.get_etas();

        let summed_y_m_poly_time = start_timer!(|| "Compute y_m poly");
        let (y_a_poly, y_b_poly) = match state.my_polys {
            Some(ref v) => v,
            None => return Err(Error::Other("mz_polys are empty".to_owned())),
        };

        let y_c_poly = y_a_poly.polynomial() * y_b_poly.polynomial();

        let mut summed_y_m_coeffs = y_c_poly.coeffs;
        // Note: Can't combine these two loops, because y_c_poly has 2x the degree
        // of y_a_poly and y_b_poly, so the second loop gets truncated due to
        // the `zip`s.
        summed_y_m_coeffs.par_iter_mut().for_each(|c| *c *= eta[2]);

        // We cannot combine y_a and y_b iterators too, because in some exceptional
        // cases with no zk, they may differ in degree.
        summed_y_m_coeffs
            .par_iter_mut()
            .zip(&y_a_poly.polynomial().coeffs)
            .for_each(|(c, a)| *c += eta[0] * a);
        summed_y_m_coeffs
            .par_iter_mut()
            .zip(&y_b_poly.polynomial().coeffs)
            .for_each(|(c, b)| *c += eta[1] * b);

        let summed_y_m_poly = Polynomial::from_coefficients_vec(summed_y_m_coeffs);
        end_timer!(summed_y_m_poly_time);

        let l_x_alpha_evals_time = start_timer!(|| "Compute l_x_alpha evals");
        let l_x_alpha_evals_on_h = domain_h.domain_eval_lagrange_kernel(alpha)?;
        end_timer!(l_x_alpha_evals_time);

        let l_x_alpha_poly_time = start_timer!(|| "Compute l_x_alpha poly");
        let l_x_alpha_poly =
            Polynomial::from_coefficients_vec(domain_h.ifft(&l_x_alpha_evals_on_h));
        end_timer!(l_x_alpha_poly_time);

        let t_poly_time = start_timer!(|| "Compute t poly");
        // TODO: why not keep the domain evals of T also?
        // It might be more efficient to compute the domain evals of the outer_poly
        // by using the domains evals of its components (which are already present anyway)
        let t_evals_on_h = marlin::IOP::calculate_t(
            vec![&state.index.a, &state.index.b, &state.index.c].into_iter(),
            eta,
            domain_h.clone(),
            &l_x_alpha_evals_on_h,
        )?;
        let t_poly =
            EvaluationsOnDomain::from_vec_and_domain(t_evals_on_h.clone(), domain_h.clone())
                .interpolate();
        end_timer!(t_poly_time);

        assert!(t_poly.degree() < domain_h.size());

        let y_poly_time = start_timer!(|| "Compute y poly");

        let domain_x =
            get_best_evaluation_domain::<G1::ScalarField>(state.formatted_input_assignment.len())
                .ok_or(SynthesisError::PolynomialDegreeTooLarge)
                .unwrap();
        let x_poly = EvaluationsOnDomain::from_vec_and_domain(
            state.formatted_input_assignment.clone(),
            domain_x.clone(),
        )
        .interpolate();
        let w_poly = match state.w_poly {
            Some(ref v) => v,
            None => return Err(Error::Other("w_poly is empty".to_owned())),
        };

        // Complete state polynomial
        //      y_poly (X) = x(X) + v_X(X) * w^(X),
        // with w(X) = 0 on X.
        // We have
        //      deg w^(X) = |H| - 1 + zk * (1 + C) - |X|
        // and hence
        //      deg (y_poly) = max(|X| - 1,  |X| + |H| - 1 + zk * (1 + C) - |X|) =
        //                  =  |H| - 1 + zk * (1 + C)
        // with zk = 1 / 0, and C as given by poly-commit.
        let mut y_poly = w_poly.polynomial().mul_by_vanishing_poly(domain_x.size());
        y_poly
            .coeffs
            .par_iter_mut()
            .zip(&x_poly.coeffs)
            .for_each(|(y, x)| *y += x);
        assert!(y_poly.degree() <= domain_h.size() - 1 + zk as usize * (1 + C));

        end_timer!(y_poly_time);

        let outer_poly_time = start_timer!(|| "Compute outer sumcheck poly");

        let domain_b_size = *[
            l_x_alpha_poly.degree() + summed_y_m_poly.degree(),
            t_poly.degree() + y_poly.degree(),
        ]
        .iter()
        .max()
        .unwrap()
            + 1;
        let domain_b = get_best_evaluation_domain::<G1::ScalarField>(domain_b_size)
            .expect("field is not smooth enough to construct domain");
        let l_x_alpha_evals = l_x_alpha_poly.evaluate_over_domain_by_ref(domain_b.clone());
        let summed_y_m_evals = summed_y_m_poly.evaluate_over_domain_by_ref(domain_b.clone());
        let y_poly_evals = y_poly.evaluate_over_domain_by_ref(domain_b.clone());
        let mut t_poly_evals = t_poly.evaluate_over_domain_by_ref(domain_b.clone());

        t_poly_evals
            .evals
            .par_iter_mut()
            .zip(&y_poly_evals.evals)
            .zip(&l_x_alpha_evals.evals)
            .zip(&summed_y_m_evals.evals)
            .for_each(|(((a, &b), &c), &d)| {
                *a *= b;
                *a -= c * d;
            });

        let outer_poly = t_poly_evals.interpolate_by_ref();
        end_timer!(outer_poly_time);

        let u_1_time = start_timer!(|| "Compute u_1 poly");

        let step = Self::get_subdomain_step(&domain_b, &domain_h)?;

        let outer_poly_evals_on_H = EvaluationsOnDomain::from_vec_and_domain(
            t_poly_evals
                .evals
                .clone()
                .into_iter()
                .step_by(step)
                .collect(),
            domain_h.clone(),
        );
        let u_1 = {
            // compute U_1(X)
            let u_1_t = BoundaryPolynomial::from_coboundary_polynomial_evals(outer_poly_evals_on_H)
                .map_err(|e| {
                    end_timer!(u_1_time);
                    end_timer!(round_time);
                    e
                })?
                .polynomial();

            if zk {
                // The boundary polynomial is queried one time more than the other witness-related
                // polynomials.
                let mut randomization_poly = Polynomial::rand(1 + C, rng);
                randomization_poly = randomization_poly.mul_by_vanishing_poly(domain_h.size());

                // Add the randomization polynomial to u_1
                let u_1 = &u_1_t + &randomization_poly;
                u_1
            } else {
                u_1_t
            }
        };

        end_timer!(u_1_time);

        let u_1_g_time = start_timer!(|| "Compute u_1_g poly");
        let u_1_g = {
            // u_1 has higher degree with respect to |H| due to randomization;
            // therefore, when constructing u_1_g we have to take care of the
            // higher powers of g. So the g vector will be:
            // (1, g, g^2,...., g^n-1, 1, g, ..., g^((deg(z1) - 1) - |H|)
            let size_diff = u_1.coeffs.len() as i32 - domain_h.size() as i32;

            let mut g_s = domain_h.elements().collect::<Vec<G1::ScalarField>>();
            g_s.append(&mut g_s[..size_diff as usize].to_vec());

            let mut u_1_g = u_1.clone();
            u_1_g
                .coeffs
                .par_iter_mut()
                .zip(g_s)
                .for_each(|(a, b)| *a *= b);
            u_1_g
        };
        end_timer!(u_1_g_time);

        // h1(X) = (outer_poly(X) + u1(X) - u1(g*X)) / v_H(X)
        // deg h_1(X) = deg(outer_poly(X)) - deg(v_H)
        //      = deg(l_x_alpha) + deg(y_a) + deg(y_b) - |H|
        //
        // deg h_1(X) <= |H| - 1 + 2 * (|H| - 1 + zk * (1 + C)) - |H| =
        //          = 2 * |H| - 3 + 2 * zk * (1 + C)
        // with zk = 1 / 0, and C as given by poly-commit.
        let h_1_time = start_timer!(|| "Compute h_1 poly");

        let mut h_1 = &outer_poly + &(&u_1 - &u_1_g);
        h_1 = match h_1.divide_by_vanishing_poly(domain_h) {
            Some(v) => v.0,
            None => {
                return Err(Error::Other(
                    "Division by vanishing poly failed for h_1".to_owned(),
                ))
            }
        };
        end_timer!(h_1_time);

        assert!(h_1.degree() <= 2 * domain_h.size() - 3 + 2 * zk as usize * (1 + C));

        let oracles = ProverSecondOracles {
            u_1: LabeledPolynomial::new("u_1".into(), u_1, zk),
            h_1: LabeledPolynomial::new("h_1".into(), h_1, zk),
            t: LabeledPolynomial::new("t".into(), t_poly, false),
        };

        state.w_poly = None;
        state.verifier_first_msg = Some(ver_message.clone());
        end_timer!(round_time);

        Ok((oracles, state))
    }

    /// Prover third round of the algebraic oracle proof.
    /// It is the first round of the inner-sumcheck aggregation.
    pub fn prover_third_round<'a>(
        ver_message: &VerifierSecondMsg<G1>,
        state: ProverState<'a, G1, G2>,
    ) -> Result<(ProverThirdOracles<G1>, ProverState<'a, G1, G2>), Error> {
        let round_time = start_timer!(|| "IOP::Prover::ThirdRound");

        let ProverState { index, .. } = state;

        let verifier_first_msg = state.verifier_first_msg.as_ref().expect(
            "ProverState should include verifier_first_msg when prover_third_round is called",
        );
        let eta = &verifier_first_msg.get_etas();

        let beta = ver_message.beta;

        let l_x_beta_evals_time = start_timer!(|| "Compute l_x_beta evals");
        let l_x_beta_evals_on_h = state.domain_h.domain_eval_lagrange_kernel(beta)?;
        end_timer!(l_x_beta_evals_time);

        let curr_bridging_poly_time = start_timer!(|| "Compute curr_bridging_poly");
        let m_a = mat_vec_mul(&index.a, l_x_beta_evals_on_h.as_slice());
        let m_b = mat_vec_mul(&index.b, l_x_beta_evals_on_h.as_slice());
        let m_c = mat_vec_mul(&index.c, l_x_beta_evals_on_h.as_slice());

        let curr_bridging_poly_on_h: Vec<_> = m_a
            .iter()
            .zip(&m_b)
            .zip(&m_c)
            .map(|((a, b), c)| eta[0] * a + eta[1] * b + eta[2] * c)
            .collect();
        let curr_bridging_poly = EvaluationsOnDomain::from_vec_and_domain(
            curr_bridging_poly_on_h.clone(),
            state.domain_h.clone(),
        )
        .interpolate();
        end_timer!(curr_bridging_poly_time);

        let prev_bridging_poly_time = start_timer!(|| "Compute prev_bridging_poly");

        let eta = &state.acc.non_native[0].t_item.succinct_descriptor.etas;

        let prev_bridging_poly_on_h: Vec<_> = m_a
            .iter()
            .zip(&m_b)
            .zip(&m_c)
            .map(|((a, b), c)| eta[0] * a + eta[1] * b + eta[2] * c)
            .collect();
        let prev_bridging_poly = EvaluationsOnDomain::from_vec_and_domain(
            prev_bridging_poly_on_h.clone(),
            state.domain_h.clone(),
        )
        .interpolate();
        end_timer!(prev_bridging_poly_time);

        let oracles = ProverThirdOracles {
            curr_bridging_poly: LabeledPolynomial::new(
                "curr_bridging_poly".into(),
                curr_bridging_poly,
                false,
            ),
            prev_bridging_poly: LabeledPolynomial::new(
                "prev_bridging_poly".into(),
                prev_bridging_poly,
                false,
            ),
        };

        end_timer!(round_time);

        Ok((oracles, state))
    }

    /// Prover fourth round of the algebraic oracle proof.
    /// It is the second round of the inner-sumcheck aggregation.
    pub fn prover_fourth_round<'a>(
        ver_message: &VerifierThirdMsg<G1>,
        state: ProverState<'a, G1, G2>,
    ) -> Result<(ProverFourthOracles<G1>, ProverState<'a, G1, G2>), Error> {
        let round_time = start_timer!(|| "IOP::Prover::FourthRound");
        let etas = ver_message.etas;
        let gamma = ver_message.gamma;

        let curr_t_acc_poly_time = start_timer!(|| "Compute curr_t_acc_poly");

        let curr_t_acc_succinct_descriptor = SuccinctInnerSumcheckDescriptor {
            alpha: gamma,
            etas: etas,
        };

        let curr_t_acc_poly = curr_t_acc_succinct_descriptor
            .expand(state.index)
            .map_err(|err| Error::Other(err.to_string()))?;

        end_timer!(curr_t_acc_poly_time);

        let oracles = ProverFourthOracles {
            curr_t_acc_poly: LabeledPolynomial::new(
                "curr_t_acc_poly".into(),
                curr_t_acc_poly,
                false,
            ),
        };

        end_timer!(round_time);

        Ok((oracles, state))
    }
}
