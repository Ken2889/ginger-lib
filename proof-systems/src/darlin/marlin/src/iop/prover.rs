#![allow(non_snake_case)]

use crate::iop::indexer::*;
use crate::iop::verifier::*;
use crate::iop::*;

use crate::iop::sparse_linear_algebra::{mat_vec_mul, SparseMatrix};
use crate::{ToString, Vec};
use algebra::PrimeField;
use algebra::{get_best_evaluation_domain, EvaluationDomain, Evaluations as EvaluationsOnDomain};
use poly_commit::{LabeledPolynomial, Polynomial};
use r1cs_core::{ConstraintSynthesizer, ConstraintSystem, SynthesisMode};
use rand_core::RngCore;

/// State for the IOP prover.
pub struct ProverState<'a, F: PrimeField> {
    formatted_input_assignment: Vec<F>,
    witness_assignment: Vec<F>,

    // the polynomial associated to the formatted public input.
    x_poly: LabeledPolynomial<F>,

    // the witness polynomial w(X), normalized by the vanishing polynomial of
    // the input domain, such that y(X) = x(X) + w(X)*Z_I(X).
    w_poly: Option<LabeledPolynomial<F>>,
    // the witness polynomials y_a(X) and y_b(X).
    y_m_polys: Option<(LabeledPolynomial<F>, LabeledPolynomial<F>)>,

    index: &'a Index<F>,

    /// the random values sent by the verifier in the first round
    verifier_first_msg: Option<VerifierFirstMsg<F>>,

    /// domain X, sized for the public input
    domain_x: Box<dyn EvaluationDomain<F>>,

    /// domain H, sized for constraints
    domain_h: Box<dyn EvaluationDomain<F>>,

    /// domain K, sized for matrix nonzero elements
    domain_k: Box<dyn EvaluationDomain<F>>,

    /// domain B, for the precomputations of the inner sumcheck
    domain_b: Box<dyn EvaluationDomain<F>>,
}

impl<'a, F: PrimeField> ProverState<'a, F> {
    /// Get the public input.
    pub fn public_input(&self) -> Vec<F> {
        IOP::unformat_public_input(&self.formatted_input_assignment)
    }
    /// Return the variable vector, with input variables and witness variables already indexed
    /// according to the treatment of the input domain `domain_x` as a subdomain of the full
    /// Lagrange domain `domain_h`.
    pub fn full_variable_vector(&self) -> Vec<F> {
        let domain_x_size = self.domain_x.size();
        let mut padded_public_input = vec![F::zero(); self.domain_h.size()];
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

/// The "oracle" output by prover during initialization.
pub struct ProverInitOracle<F: Field> {
    /// The public input polynomial `x`
    pub x: LabeledPolynomial<F>,
}

impl<F: Field> ProverInitOracle<F> {
    /// Iterate over the polynomials output by the prover during initialization.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        std::iter::once(&self.x)
    }
}

/// The first set of prover oracles.
pub struct ProverFirstOracles<F: PrimeField> {
    /// The randomized witness polynomial `w`.
    pub w: LabeledPolynomial<F>,
    /// The randomized y_A(X)= Sum_{z in H} A(X,z)*y(z)
    pub y_a: LabeledPolynomial<F>,
    /// The randomized y_B(X)= Sum_{z in H} B(X,z)*y(z)
    pub y_b: LabeledPolynomial<F>,
}

impl<F: PrimeField> ProverFirstOracles<F> {
    /// Iterate over the polynomials output by the prover in the first round.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        vec![&self.w, &self.y_a, &self.y_b].into_iter()
    }
}

/// The second set of prover oracles.
pub struct ProverSecondOracles<F: PrimeField> {
    /// The boundary polynomial U_1(X) for the outer sumcheck
    pub u_1: LabeledPolynomial<F>,
    /// The quotient polynomial h_1(X) in the outer sumcheck identity.
    pub h_1: LabeledPolynomial<F>,
}

impl<F: PrimeField> ProverSecondOracles<F> {
    /// Iterate over the polynomials output by the prover in the second round.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        vec![&self.u_1, &self.h_1].into_iter()
    }
}

/// The third set of prover oracles.
pub struct ProverThirdOracles<F: PrimeField> {
    /// The boundary polynomial U_2(X) for the inner sumcheck.
    pub u_2: LabeledPolynomial<F>,
    /// The quotient polynomial h_2(X) in the inner sumcheck identity.
    pub h_2: LabeledPolynomial<F>,
}

impl<F: PrimeField> ProverThirdOracles<F> {
    /// Iterate over the polynomials output by the prover in the third round.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        vec![&self.u_2, &self.h_2].into_iter()
    }
}

/* The prover rounds
*/
impl<F: PrimeField> IOP<F> {
    /// Preparation of the prover, computes the witness vector `y`.
    pub fn prover_init<'a, C: ConstraintSynthesizer<F>>(
        index: &'a Index<F>,
        c: C,
    ) -> Result<(ProverInitOracle<F>, ProverState<'a, F>), Error> {
        let init_time = start_timer!(|| "IOP::Prover::Init");

        let witnesses_time = start_timer!(|| "Compute witnesses");
        let mode = SynthesisMode::Prove {
            construct_matrices: false,
        };
        let mut pcs = ConstraintSystem::new(mode);
        c.generate_constraints(&mut pcs)?;
        end_timer!(witnesses_time);

        let num_non_zero = index.index_info.num_non_zero;

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

        let (domain_h, domain_k, domain_x, domain_b) = Self::build_domains(
            num_witness_variables,
            num_input_variables,
            num_constraints,
            num_non_zero,
        )?;

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
            y_m_polys: None,
            index,
            verifier_first_msg: None,
            domain_h,
            domain_k,
            domain_x,
            domain_b,
        };

        let oracles = ProverInitOracle { x: x_poly };

        end_timer!(init_time);

        Ok((oracles, prover_state))
    }

    /// Prover first round of the algebraic oracle proof, the initial round in [HGB].
    /// Determines the oracles for the witness-related polynomials
    /// `w(X)`, `y_A(X)` and `y_B(X)`.
    ///
    /// [HGB]: https://eprint.iacr.org/2021/930
    pub fn prover_first_round<'a, R: RngCore>(
        mut state: ProverState<'a, F>,
        zk: bool,
        rng: &mut R,
    ) -> Result<(ProverFirstOracles<F>, ProverState<'a, F>), Error> {
        let round_time = start_timer!(|| "IOP::Prover::FirstRound");
        let domain_h = &state.domain_h;
        let domain_x = &state.domain_x;

        let x_time = start_timer!(|| "Computing x polynomial evaluations");
        // Evaluate the input polynomial x(X) over H.
        let x_evals = domain_h.fft(&state.x_poly);
        end_timer!(x_time);

        /* Compute the normalized witness polynomial w(X) which allows easy
        combination with the input polynomial,
            y(X) = x(X) + z_I(X)* w(X) mod (X^n-1).
        */
        let ratio = Self::get_subdomain_step(domain_h, domain_x)?;

        let mut w_extended = state.witness_assignment.clone();
        w_extended.extend(vec![
            F::zero();
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
                    F::zero()
                } else {
                    // The mapping of the witness vector to values on H.
                    w_extended[k - (k / ratio) - 1] - &x_evals[k]
                }
            })
            .collect();

        // Degree of w_poly before dividing by the vanishing polynomial Z_I(X)
        // of the input domain I is equal to
        //      max(|H| - 1 , |H| + (zk - 1) * 1) = |H| + (zk - 1) * 1
        let w_poly = {
            let w = EvaluationsOnDomain::from_vec_and_domain(w_poly_evals, domain_h.clone())
                .interpolate();
            if zk {
                let mut randomization_poly = Polynomial::rand(0, rng);
                randomization_poly = randomization_poly.mul_by_vanishing_poly(domain_h.size());
                let w = &w + &randomization_poly;

                w
            } else {
                w
            }
        };
        let (w_poly, remainder) = w_poly.divide_by_vanishing_poly(&domain_x).unwrap();
        assert!(remainder.is_zero()); // w_poly is divisible by Z_I(X) because we set w = 0 on I.
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
                let mut randomization_poly = Polynomial::rand(0, rng);
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
                let mut randomization_poly = Polynomial::rand(0, rng);
                randomization_poly = randomization_poly.mul_by_vanishing_poly(domain_h.size());
                let y_b = &y_b + &randomization_poly;

                y_b
            } else {
                y_b
            }
        };
        end_timer!(y_b_poly_time);

        assert!(w_poly.degree() <= domain_h.size() - domain_x.size() + zk as usize - 1);
        assert!(y_a_poly.degree() <= domain_h.size() + zk as usize - 1);
        assert!(y_b_poly.degree() <= domain_h.size() + zk as usize - 1);

        let w = LabeledPolynomial::new("w".to_string(), w_poly, zk);
        let y_a = LabeledPolynomial::new("y_a".to_string(), y_a_poly, zk);
        let y_b = LabeledPolynomial::new("y_b".to_string(), y_b_poly, zk);

        let oracles = ProverFirstOracles {
            w: w.clone(),
            y_a: y_a.clone(),
            y_b: y_b.clone(),
        };

        state.w_poly = Some(w);
        state.y_m_polys = Some((y_a, y_b));
        end_timer!(round_time);

        Ok((oracles, state))
    }

    /// Given the Lagrange representation M(X,Y) for the R1CS matrices M=A,B,C,
    /// batching challenges eta_M, M=A,B,C, and L_H(alpha,Y) over H, computes
    /// the evaluations over H of the circuit polynomial
    ///     t(X) = Sum_{M} eta_M * M(alpha, X)
    /// with
    ///     M(alpha, X) = Sum_{z in H} L(alpha,z) * M(z,X)
    fn calculate_t<'a>(
        matrices: impl Iterator<Item = &'a SparseMatrix<F>>,
        matrix_randomizers: &[F],
        domain_h: Box<dyn EvaluationDomain<F>>,
        l_x_alpha_on_h: &Vec<F>,
    ) -> Result<Vec<F>, Error> {
        let mut t_evals_on_h = vec![F::zero(); domain_h.size()];
        for (matrix, eta) in matrices.zip(matrix_randomizers) {
            for (r, row) in matrix.iter().enumerate() {
                for (coeff, c) in row.iter() {
                    t_evals_on_h[*c] += *eta * coeff * l_x_alpha_on_h[r];
                }
            }
        }
        Ok(t_evals_on_h)
    }

    /// Returns the ratio of the sizes of `domain` and `subdomain` or an Error if
    /// `subdomain` is not a subdomain of `domain`.
    fn get_subdomain_step(
        domain: &Box<dyn EvaluationDomain<F>>,
        subdomain: &Box<dyn EvaluationDomain<F>>,
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
    /// Determines the oracles for `U_1(X)` and `h_1(X)`.
    // Note: the outer sumcheck identity is
    //      T(alpha,X) * y(X) - L_H(X,alpha) * y_eta(X) = U_1(gX) - U_1(X) + h_1(X) * (X^n-1),
    // with
    //      y(X) = x(X) + (X^l-1) * w(X)
    //      y_eta(X) = y_A(X) + eta * y_B(X) + eta^2 * y_A(X) * y_B(X)
    // Since `T(alpha,X)` could be computed from public data, the prover does not provide a
    // commitment for it.
    pub fn prover_second_round<'a, R: RngCore>(
        ver_message: &VerifierFirstMsg<F>,
        mut state: ProverState<'a, F>,
        zk: bool,
        rng: &mut R,
    ) -> Result<(ProverSecondOracles<F>, ProverState<'a, F>), Error> {
        let round_time = start_timer!(|| "IOP::Prover::SecondRound");

        let domain_h = &state.domain_h;

        let alpha = ver_message.alpha;
        let (eta_a, eta_b, eta_c) = ver_message.get_etas();
        // In the following we exploit the fact that eta_a == 1 to avoid unnecessary
        // multiplications.
        assert_eq!(eta_a, F::one());

        let summed_y_m_poly_time = start_timer!(|| "Compute y_m poly");
        let (y_a_poly, y_b_poly) = match state.y_m_polys {
            Some(ref v) => v,
            None => return Err(Error::Other("y_m_polys are empty".to_owned())),
        };

        // Performed via FFT using a domain of size = deg(y_a) + deg(y_b) + 1
        let y_c_poly = y_a_poly.polynomial() * y_b_poly.polynomial();

        let mut summed_y_m_coeffs = y_c_poly.coeffs;
        // Note: Can't combine these two loops, because y_c_poly has 2x the degree
        // of y_a_poly and y_b_poly, so the second loop gets truncated due to
        // the `zip`s.
        summed_y_m_coeffs.par_iter_mut().for_each(|c| *c *= &eta_c);

        // We cannot combine y_a and y_b iterators too, because in some exceptional
        // cases with no zk, they may differ in degree.
        summed_y_m_coeffs
            .par_iter_mut()
            .zip(&y_a_poly.polynomial().coeffs)
            .for_each(|(c, a)| *c += a);
        summed_y_m_coeffs
            .par_iter_mut()
            .zip(&y_b_poly.polynomial().coeffs)
            .for_each(|(c, b)| *c += &(eta_b * b));

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
        let t_evals_on_h = Self::calculate_t(
            vec![&state.index.a, &state.index.b, &state.index.c].into_iter(),
            &[eta_a, eta_b, eta_c],
            domain_h.clone(),
            &l_x_alpha_evals_on_h,
        )?;
        let t_poly =
            EvaluationsOnDomain::from_vec_and_domain(t_evals_on_h.clone(), domain_h.clone())
                .interpolate();
        end_timer!(t_poly_time);

        assert!(t_poly.degree() < domain_h.size());

        let y_poly_time = start_timer!(|| "Compute y poly");

        let x_poly = &state.x_poly;

        let w_poly = match state.w_poly {
            Some(ref v) => v,
            None => return Err(Error::Other("w_poly is empty".to_owned())),
        };

        // Complete state polynomial
        //      y_poly (X) = x(X) + v_X(X) * w^(X),
        // with w(X) = 0 on X.
        // We have
        //      deg w^(X) = |H| + (zk - 1) * 1 - |X|
        // and hence
        //      deg (y_poly) = max(|X| - 1,  |X| + |H| + (zk - 1) * 1 - |X|) =
        //                  =  |H| - 1 + zk
        // with zk = 1 / 0.
        let mut y_poly = w_poly
            .polynomial()
            .mul_by_vanishing_poly(state.domain_x.size());
        y_poly
            .coeffs
            .par_iter_mut()
            .zip(&x_poly.coeffs)
            .for_each(|(y, x)| *y += x);
        assert!(y_poly.degree() <= domain_h.size() + zk as usize - 1);

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
        let domain_b = get_best_evaluation_domain::<F>(domain_b_size)
            .expect("field is not smooth enough to construct domain");
        // TODO: can we reuse the domain evals over H here, instead of recomputing?
        // For example, by coset FFT?
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
                let mut randomization_poly = Polynomial::rand(1, rng);
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
            // (1, g, g^2,...., g^n-1, 1, g, ..., g^((deg(u_1) - 1) - |H|)
            let size_diff = u_1.coeffs.len() as i32 - domain_h.size() as i32;

            let mut g_s = domain_h.elements().collect::<Vec<F>>();
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
        // deg h_1(X) <= |H|-1 + 2*(|H|-1 + zk) - |H| =
        //          = 2*|H| - 3 + 2*zk
        // with zk = 1 / 0.
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

        assert!(h_1.degree() <= 2 * domain_h.size() - 3 + 2 * zk as usize);

        let oracles = ProverSecondOracles {
            u_1: LabeledPolynomial::new("u_1".into(), u_1, zk),
            h_1: LabeledPolynomial::new("h_1".into(), h_1, zk),
        };

        state.w_poly = None;
        state.verifier_first_msg = Some(*ver_message);
        end_timer!(round_time);

        Ok((oracles, state))
    }

    /// Prover third round of the algebraic oracle proof, the "inner sumcheck".
    /// Determines the oracles for `U_2(X)` and `h_2(X)`.
    // Note: the inner sumcheck identity is
    //      a(X) = b(X)*(T(alpha,beta)/m + U_2(gX) - U_2(X)) + h_2(X)*(X^m-1),
    // with
    //      b(X) = Product_{M=A,B,C} (alpha - row_M(X)) * (beta - col_M(X)),
    //      a(X) = (beta^n-1)*(alpha^n-1)/n^2 * Sum_{M=A,B,C} eta_M * val.row.col_M(X) * p_M(X),
    // where
    //      p_M(X) = prod_{N!=M} (alpha - row_N(X)) * (beta - col_N(X))
    //             = prod_{N!=M} (alpha*beta - alpha * col_N(X) - beta * row_N(X) + row.col_N(X)).
    pub fn prover_third_round<'a>(
        ver_message: &VerifierSecondMsg<F>,
        prover_state: ProverState<'a, F>,
    ) -> Result<ProverThirdOracles<F>, Error> {
        let round_time = start_timer!(|| "IOP::Prover::ThirdRound");

        let ProverState {
            index,
            verifier_first_msg,
            domain_h,
            domain_k,
            domain_b,
            ..
        } = prover_state;

        let verifier_first_msg = verifier_first_msg.expect(
            "ProverState should include verifier_first_msg when prover_third_round is called",
        );

        let alpha = verifier_first_msg.alpha;
        let beta = ver_message.beta;

        let (scaled_eta_a, scaled_eta_b, scaled_eta_c) = {
            let (eta_a, eta_b, eta_c) = verifier_first_msg.get_etas();
            let scale_factor = domain_h.evaluate_vanishing_polynomial(alpha)
                * domain_h.evaluate_vanishing_polynomial(beta)
                * domain_h.size_inv().square();
            (
                eta_a * scale_factor,
                eta_b * scale_factor,
                eta_c * scale_factor,
            )
        };

        let (a_arith, b_arith, c_arith) = (&index.a_arith, &index.b_arith, &index.c_arith);

        let denom_eval_time = start_timer!(|| "Computing denominator evals on domain B");
        let compute_denom_evals_on_b = |m_arith: &MatrixArithmetization<F>| -> Vec<F> {
            m_arith
                .evals_on_domain_b
                .row
                .evals
                .par_iter()
                .zip(&m_arith.evals_on_domain_b.col.evals)
                .zip(&m_arith.evals_on_domain_b.row_col.evals)
                .map(|((&r, c), rc)| alpha * beta - beta * r - alpha * c + rc)
                .collect()
        };
        let a_denom_evals_on_b = compute_denom_evals_on_b(a_arith);
        let b_denom_evals_on_b = compute_denom_evals_on_b(b_arith);
        let c_denom_evals_on_b = compute_denom_evals_on_b(c_arith);
        end_timer!(denom_eval_time);

        let scale_val_row_col_time =
            start_timer!(|| "Scaling val.row.col evals on domain B by scaled_eta");
        let compute_scaled_val_row_col =
            |m_arith: &MatrixArithmetization<F>, scaled_eta_m| -> Vec<F> {
                m_arith
                    .evals_on_domain_b
                    .val_row_col
                    .evals
                    .par_iter()
                    .map(|m_val_row_col| scaled_eta_m * m_val_row_col)
                    .collect()
            };
        let a_scaled_val_row_col_on_b = compute_scaled_val_row_col(a_arith, scaled_eta_a);
        let b_scaled_val_row_col_on_b = compute_scaled_val_row_col(b_arith, scaled_eta_b);
        let c_scaled_val_row_col_on_b = compute_scaled_val_row_col(c_arith, scaled_eta_c);
        end_timer!(scale_val_row_col_time);

        /* Compute the domain evals of
            p(X) =  (alpha^n-1)(beta^n-1)/n^2 * sum_{M=A,B,C} eta_M * val.row.col_M(X) / (alpha-row_M(X))(beta-col_M(X))
        */
        let p_evals_time = start_timer!(|| "Computing p evals on K");

        // Compute the evaluations of the inverses of the denominators over the indexer domain `K`
        // by reusing the already computed evaluations of the denominators over the domain `B` and
        // performing a batch inversion.
        let step = Self::get_subdomain_step(&domain_b, &domain_k)?;

        let compute_inverse_denom_evals_on_k = |m_denom_evals_on_b: &Vec<F>| -> Vec<F> {
            let mut result: Vec<_> = m_denom_evals_on_b
                .par_iter()
                .step_by(step)
                .cloned()
                .collect();
            algebra::batch_inversion(&mut result);
            result
        };
        let a_denom_inv_evals_on_k = compute_inverse_denom_evals_on_k(&a_denom_evals_on_b);
        let b_denom_inv_evals_on_k = compute_inverse_denom_evals_on_k(&b_denom_evals_on_b);
        let c_denom_inv_evals_on_k = compute_inverse_denom_evals_on_k(&c_denom_evals_on_b);

        let p_evals_on_k: Vec<_> = a_scaled_val_row_col_on_b
            .par_iter()
            .zip(&b_scaled_val_row_col_on_b)
            .zip(&c_scaled_val_row_col_on_b)
            .step_by(step)
            .zip(&a_denom_inv_evals_on_k)
            .zip(&b_denom_inv_evals_on_k)
            .zip(&c_denom_inv_evals_on_k)
            .map(
                |(((((&a_eta_vrc, &b_eta_vrc), &c_eta_vrc), a_den_inv), b_den_inv), c_den_inv)| {
                    a_eta_vrc * a_den_inv + b_eta_vrc * b_den_inv + c_eta_vrc * c_den_inv
                },
            )
            .collect();
        end_timer!(p_evals_time);

        /* Compute the boundary polynomial U_2(X) for p(X) - T(alpha,beta)/|K|.
         */
        let u_2_time = start_timer!(|| "Compute u_2 poly");
        let (u_2, normalized_v) = BoundaryPolynomial::from_non_coboundary_polynomial_evals(
            EvaluationsOnDomain::from_vec_and_domain(p_evals_on_k, domain_k.clone()),
        )
        .map_err(|e| {
            end_timer!(u_2_time);
            end_timer!(round_time);
            e
        })?;

        let u_2 = u_2.polynomial();
        end_timer!(u_2_time);

        assert!(u_2.degree() <= domain_k.size() - 1);

        // Compute the shifted boundary polynomial U_2(gX)
        let u_2_g_time = start_timer!(|| "Compute u_2_g poly");
        let u_2_g = {
            let mut u_2_g = u_2.clone();
            let g_s = domain_k.elements().collect::<Vec<F>>();
            u_2_g
                .coeffs
                .par_iter_mut()
                .zip(g_s)
                .for_each(|(a, b)| *a *= b);
            u_2_g
        };
        end_timer!(u_2_g_time);

        assert!(u_2_g.degree() <= domain_k.size() - 1);

        /* Compute the quotient polynomial h_2(X) for the inner sumcheck identity.
         */

        let a_evals_time = start_timer!(|| "Computing a evals on domain B");
        let a_evals_on_b: Vec<_> = a_scaled_val_row_col_on_b
            .par_iter()
            .zip(&b_scaled_val_row_col_on_b)
            .zip(&c_scaled_val_row_col_on_b)
            .zip(&a_denom_evals_on_b)
            .zip(&b_denom_evals_on_b)
            .zip(&c_denom_evals_on_b)
            .map(
                |(((((&a_eta_vrc, &b_eta_vrc), &c_eta_vrc), a_den), b_den), c_den)| {
                    a_eta_vrc * b_den * c_den
                        + b_eta_vrc * a_den * c_den
                        + c_eta_vrc * a_den * b_den
                },
            )
            .collect();
        end_timer!(a_evals_time);

        let b_evals_time = start_timer!(|| "Computing b evals on domain B");
        let b_evals_on_b: Vec<_> = a_denom_evals_on_b
            .par_iter()
            .zip(&b_denom_evals_on_b)
            .zip(&c_denom_evals_on_b)
            .map(|((&a_den, b_den), c_den)| a_den * b_den * c_den)
            .collect();
        end_timer!(b_evals_time);

        let h_2_poly_time = start_timer!(|| "Computing h_2 poly");
        let mut f_poly = &u_2_g - &u_2;
        f_poly.coeffs[0] += normalized_v;
        // We  use domain evaluations only for computing
        //      a_poly_evals - b_poly_evals * f_poly_evals
        // over the larger domain B of size 4*|K|, and then do a single FFT.
        // For that we need to compute the domain eval of f_poly over 4*|K|
        let f_evals_on_b = f_poly.evaluate_over_domain_by_ref(domain_b.clone()).evals;

        let inner_poly_evals: Vec<_> = a_evals_on_b
            .par_iter()
            .zip(&b_evals_on_b)
            .zip(&f_evals_on_b)
            .map(|((&a, &b), f)| a - b * f)
            .collect();
        let inner_poly =
            EvaluationsOnDomain::from_vec_and_domain(inner_poly_evals, domain_b.clone())
                .interpolate();
        let h_2 = match inner_poly.divide_by_vanishing_poly(&domain_k) {
            Some(v) => v.0,
            None => {
                return Err(Error::Other(
                    "Division by vanishing poly failed for h_2".to_owned(),
                ))
            }
        };
        end_timer!(h_2_poly_time);

        assert!(h_2.degree() <= 3 * domain_k.size() - 4);

        let oracles = ProverThirdOracles {
            u_2: LabeledPolynomial::new("u_2".to_string(), u_2, false),
            h_2: LabeledPolynomial::new("h_2".to_string(), h_2, false),
        };
        end_timer!(round_time);

        Ok(oracles)
    }
}
