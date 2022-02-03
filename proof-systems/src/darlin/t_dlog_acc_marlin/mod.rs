use crate::darlin::accumulators::dlog::{DLogItem, DualDLogItem};
use crate::darlin::t_dlog_acc_marlin::data_structures::{
    DualSumcheckItem, Proof, ProverKey, SumcheckItem, UniversalSRS, VerifierKey, PC,
};
use crate::darlin::t_dlog_acc_marlin::iop::IOP;
use algebra::{
    get_best_evaluation_domain, to_bytes, Curve, DensePolynomial,
    Evaluations as EvaluationsOnDomain, Field, Group, GroupVec, ToBytes,
};
use digest::Digest;
use marlin::iop::Error::VerificationEquationFailed;
use marlin::iop::LagrangeKernel;
use marlin::Error;
use poly_commit::fiat_shamir_rng::{FiatShamirRng, FiatShamirRngSeed};
use poly_commit::optional_rng::OptionalRng;
use poly_commit::{
    evaluate_query_set, evaluate_query_set_to_vec, Evaluations, LabeledCommitment,
    LabeledPolynomial, LabeledRandomness, PCVerifierKey, PolynomialCommitment,
};
use r1cs_core::ConstraintSynthesizer;
use rand::RngCore;
use std::marker::PhantomData;

pub mod data_structures;
pub mod iop;
#[cfg(test)]
mod test;

/// A helper struct to bundle the Coboundary Marlin functions for setup, prove and
/// verify.
///
/// Coboundary Marlin is an argument for satifiability of an R1CS over a prime
/// field `F` and uses a polynomial commitment scheme `PC` for
/// polynomials over that field.
pub struct Marlin<G1: Curve, G2: Curve, D: Digest>(
    #[doc(hidden)] PhantomData<G1>,
    #[doc(hidden)] PhantomData<G2>,
    #[doc(hidden)] PhantomData<D>,
);

pub struct VerificationResult<F: Field> {
    pub bullet_poly: DensePolynomial<F>,
    pub t_acc_poly: DensePolynomial<F>,
}

impl<G1: Curve, G2: Curve, D: Digest + 'static> Marlin<G1, G2, D> {
    /// The personalization string for this protocol. Used to personalize the
    /// Fiat-Shamir rng.
    pub const PROTOCOL_NAME: &'static [u8] = b"COBOUNDARY-MARLIN-2021";

    /// Generate the universal prover and verifier keys for the
    /// argument system.
    pub fn universal_setup(
        num_constraints: usize,
        num_variables: usize,
        zk: bool,
    ) -> Result<UniversalSRS<G1, PC<G1, D>>, Error<<PC<G1, D> as PolynomialCommitment<G1>>::Error>>
    {
        let max_degree = IOP::<G1, G2>::max_degree(num_constraints, num_variables, zk)?;
        let setup_time = start_timer!(|| {
            format!(
            "Marlin::UniversalSetup with max_degree {}, computed for a maximum of {} constraints, {} vars",
            max_degree, num_constraints, num_variables,
        )
        });

        let srs = PC::<G1, D>::setup(max_degree).map_err(Error::from_pc_err);
        end_timer!(setup_time);
        srs
    }

    /// The circuit-specific setup. Given a circuit `c` and a committer_key of the polynomial
    /// commitment scheme, generate the key material for the circuit. The latter is split into
    /// a prover key and a verifier key.
    pub fn circuit_specific_setup<C: ConstraintSynthesizer<G1::ScalarField>>(
        committer_key: &<PC<G1, D> as PolynomialCommitment<G1>>::CommitterKey,
        c: C,
    ) -> Result<
        (ProverKey<G1, G2, D>, VerifierKey<G1, G2, D>),
        Error<<PC<G1, D> as PolynomialCommitment<G1>>::Error>,
    > {
        let index_time = start_timer!(|| "Marlin::Index");

        let index = IOP::<G1, G2>::index(c)?;

        end_timer!(index_time);

        let commit_time = start_timer!(|| "Commit to index polynomials");

        let (index_comms, index_comm_rands): (_, _) =
            <PC<G1, D> as PolynomialCommitment<G1>>::commit_vec(committer_key, index.iter(), None)
                .map_err(Error::from_pc_err)?;
        end_timer!(commit_time);

        let index_comms = index_comms
            .into_iter()
            .map(|c| c.commitment().clone())
            .collect();

        // Compute the commitments of the Lagrange polynomials over the input domain.
        // They are included into the verifier key in order to help the verifier check that the
        // polynomial behind the commitment of the input poly provided by the prover is indeed the
        // input poly.
        let domain_x = get_best_evaluation_domain(index.index_info.num_inputs).unwrap();
        let lagrange_comms: Vec<_> = domain_x
            .elements()
            .into_iter()
            .map(|y| domain_x.slice_lagrange_kernel(y))
            .map(|poly| {
                <PC<G1, D> as PolynomialCommitment<G1>>::commit(committer_key, &poly, false, None)
                    .unwrap()
                    .0
            })
            .collect();

        let index_vk = VerifierKey {
            index,
            index_comms,
            lagrange_comms,
        };

        let index_pk = ProverKey {
            index_vk: index_vk.clone(),
            index_comm_rands,
        };

        Ok((index_pk, index_vk))
    }

    fn fiat_shamir_rng_init(
        pc_vk: &<PC<G1, D> as PolynomialCommitment<G1>>::VerifierKey,
        index_vk: &VerifierKey<G1, G2, D>,
        public_input: &Vec<G1::ScalarField>,
        inner_sumcheck_acc: &DualSumcheckItem<G2, G1>,
        dlog_acc: &DualDLogItem<G2, G1>,
    ) -> Result<<PC<G1, D> as PolynomialCommitment<G1>>::RandomOracle, poly_commit::error::Error>
    {
        let fs_rng_init_seed = {
            let mut seed_builder =
                <<PC<G1, D> as PolynomialCommitment<G1>>::RandomOracle as FiatShamirRng>::Seed::new(
                );
            seed_builder.add_bytes(&Self::PROTOCOL_NAME)?;
            seed_builder.add_bytes(&PCVerifierKey::get_hash(pc_vk))?;
            seed_builder.add_bytes(inner_sumcheck_acc)?;
            seed_builder.add_bytes(dlog_acc)?;

            // NOTE: As both vk and public input use constant length encoding of field elements,
            // we can simply apply add_bytes to achieve a one-to-one serialization.
            seed_builder.add_bytes(index_vk)?;
            seed_builder.add_bytes(public_input)?;

            seed_builder.finalize()
        };
        let fs_rng =
            <PC<G1, D> as PolynomialCommitment<G1>>::RandomOracle::from_seed(fs_rng_init_seed);
        Ok(fs_rng)
    }

    /// Produce a zkSNARK asserting given a constraint system `c` over a prime order field `F`
    pub fn prove<C: ConstraintSynthesizer<G1::ScalarField>>(
        index_pk: &ProverKey<G1, G2, D>,
        pc_pk: &<PC<G1, D> as PolynomialCommitment<G1>>::CommitterKey,
        c: C,
        previous_inner_sumcheck_acc: &DualSumcheckItem<G2, G1>,
        previous_dlog_acc: &DualDLogItem<G2, G1>,
        previous_inner_sumcheck_poly: &DensePolynomial<G1::ScalarField>,
        previous_bullet_poly: &DensePolynomial<G1::ScalarField>,
        zk: bool,
        zk_rng: Option<&mut dyn RngCore>,
    ) -> Result<
        (
            Proof<G1, G2, D>,
            DualSumcheckItem<G1, G2>,
            DualDLogItem<G1, G2>,
        ),
        Error<<PC<G1, D> as PolynomialCommitment<G1>>::Error>,
    > {
        if zk_rng.is_some() && !zk || zk_rng.is_none() && zk {
            return Err(Error::Other("If ZK is enabled, a RNG must be passed (and viceversa); conversely, if ZK is disabled, a RNG must NOT be passed (and viceversa)".to_owned()));
        }

        let zk_rng = &mut OptionalRng(zk_rng);
        let prover_time = start_timer!(|| "Marlin::Prover");

        let prover_init_state =
            IOP::prover_init(&index_pk.index_vk.index, c, previous_inner_sumcheck_acc)?;
        let public_input = prover_init_state.public_input();

        let verifier_init_state = IOP::verifier_init(
            &index_pk.index_vk.index.index_info,
            previous_inner_sumcheck_acc,
        )?;

        let mut fs_rng = Self::fiat_shamir_rng_init(
            pc_pk,
            &index_pk.index_vk,
            &public_input,
            previous_inner_sumcheck_acc,
            previous_dlog_acc,
        )
        .map_err(Error::from_pc_err)?;

        /*  First round of the compiled and Fiat-Shamir transformed oracle proof
         */

        let (prover_first_oracles, prover_state) =
            IOP::prover_first_round(prover_init_state, zk, zk_rng).map_err(|e| {
                end_timer!(prover_time);
                e
            })?;

        let first_round_comm_time = start_timer!(|| "Committing to first round polys");
        let (first_comms, first_comm_rands) = <PC<G1, D> as PolynomialCommitment<G1>>::commit_vec(
            pc_pk,
            prover_first_oracles.iter(),
            Some(zk_rng),
        )
        .map_err(Error::from_pc_err)?;
        end_timer!(first_round_comm_time);

        // absorb the prove oracles by the Fiat-Shamir rng
        fs_rng.absorb(&to_bytes![first_comms].unwrap());

        let (verifier_first_msg, verifier_state) =
            IOP::verifier_first_round(verifier_init_state, &mut fs_rng)?;

        /*  Second round of the compiled and Fiat-Shamir transformed oracle proof
         */

        let (prover_second_oracles, prover_state) =
            IOP::prover_second_round(&verifier_first_msg, prover_state, zk, zk_rng).map_err(
                |e| {
                    end_timer!(prover_time);
                    e
                },
            )?;

        let second_round_comm_time = start_timer!(|| "Committing to second round polys");
        let (second_comms, second_comm_rands) =
            <PC<G1, D> as PolynomialCommitment<G1>>::commit_vec(
                pc_pk,
                prover_second_oracles.iter(),
                Some(zk_rng),
            )
            .map_err(Error::from_pc_err)?;
        end_timer!(second_round_comm_time);

        // absorb the prove oracles by the Fiat-Shamir rng
        fs_rng.absorb(&to_bytes![second_comms].unwrap());

        let (verifier_second_msg, verifier_state) =
            IOP::verifier_second_round(verifier_state, &mut fs_rng)?;

        /*  Third round of the compiled and Fiat-Shamir transformed oracle proof
         */

        let (prover_third_oracles, prover_state) =
            IOP::prover_third_round(&verifier_second_msg, prover_state).map_err(|e| {
                end_timer!(prover_time);
                e
            })?;

        let third_round_comm_time = start_timer!(|| "Committing to third round polys");
        let (third_comms, third_comm_rands) = <PC<G1, D> as PolynomialCommitment<G1>>::commit_vec(
            pc_pk,
            prover_third_oracles.iter(),
            Some(zk_rng),
        )
        .map_err(Error::from_pc_err)?;
        end_timer!(third_round_comm_time);

        // absorb the prove oracles by the Fiat-Shamir rng
        fs_rng.absorb(&to_bytes![third_comms].unwrap());

        let (verifier_third_msg, verifier_state) =
            IOP::verifier_third_round(verifier_state, &mut fs_rng)?;

        /*  Fourth round of the compiled and Fiat-Shamir transformed oracle proof
         */

        let (prover_fourth_oracles, _) =
            IOP::prover_fourth_round(&verifier_third_msg, prover_state).map_err(|e| {
                end_timer!(prover_time);
                e
            })?;

        let fourth_round_comm_time = start_timer!(|| "Committing to fourth round polys");
        let (fourth_comms, fourth_comm_rands) =
            <PC<G1, D> as PolynomialCommitment<G1>>::commit_vec(
                pc_pk,
                prover_fourth_oracles.iter(),
                Some(zk_rng),
            )
            .map_err(Error::from_pc_err)?;
        end_timer!(fourth_round_comm_time);

        // absorb the prove oracles by the Fiat-Shamir rng
        fs_rng.absorb(&to_bytes![fourth_comms].unwrap());

        let prover_accumulator_oracles = vec![
            LabeledPolynomial::new(
                "prev_t_acc_poly".to_string(),
                previous_inner_sumcheck_poly.clone(),
                false,
            ),
            LabeledPolynomial::new(
                "prev_bullet_poly".to_string(),
                previous_bullet_poly.clone(),
                false,
            ),
        ];
        let accumulator_comms = vec![
            LabeledCommitment::new(
                "prev_t_acc_poly".to_string(),
                previous_inner_sumcheck_acc.1.c.clone(),
            ),
            LabeledCommitment::new(
                "prev_bullet_poly".to_string(),
                previous_dlog_acc.1[0].g_final.clone(),
            ),
        ];
        let accumulator_comm_rands = vec![
            LabeledRandomness::new(
                "prev_t_acc_poly".to_string(),
                <PC<G1, D> as PolynomialCommitment<G1>>::Randomness::zero(),
            ),
            LabeledRandomness::new(
                "prev_bullet_poly".to_string(),
                <PC<G1, D> as PolynomialCommitment<G1>>::Randomness::zero(),
            ),
        ];

        // Gather prover polynomials in one vector.
        let polynomials: Vec<_> = prover_first_oracles
            .iter()
            .chain(prover_second_oracles.iter())
            .chain(prover_third_oracles.iter())
            .chain(prover_fourth_oracles.iter())
            .chain(prover_accumulator_oracles.iter())
            .collect();

        // Gather commitments in one vector.
        #[rustfmt::skip]
        let commitments = vec![
            first_comms.iter().map(|p| p.commitment().clone()).collect(),
            second_comms.iter().map(|p| p.commitment().clone()).collect(),
            third_comms.iter().map(|p| p.commitment().clone()).collect(),
            fourth_comms.iter().map(|p| p.commitment().clone()).collect(),
        ];

        let labeled_comms: Vec<_> = index_pk
            .index_vk
            .iter()
            .cloned()
            .zip(&IOP::<G1, G2>::INDEXER_POLYNOMIALS)
            .map(|(c, l)| LabeledCommitment::new(l.to_string(), c))
            .chain(first_comms.iter().cloned())
            .chain(second_comms.iter().cloned())
            .chain(third_comms.iter().cloned())
            .chain(fourth_comms.iter().cloned())
            .chain(accumulator_comms.iter().cloned())
            .collect();

        // Gather commitment randomness together.
        let comm_rands: Vec<
            LabeledRandomness<<PC<G1, D> as PolynomialCommitment<G1>>::Randomness>,
        > = index_pk
            .index_comm_rands
            .clone()
            .into_iter()
            .chain(first_comm_rands)
            .chain(second_comm_rands)
            .chain(third_comm_rands)
            .chain(fourth_comm_rands)
            .chain(accumulator_comm_rands)
            .collect();

        // Set up the IOP verifier's query set.
        let (query_set, _) = IOP::verifier_query_set(verifier_state)?;

        // Compute the queried values
        let eval_time = start_timer!(|| "Evaluating polynomials over query set");

        let mut evaluations = evaluate_query_set_to_vec(polynomials.clone(), &query_set);

        evaluations.sort_by(|a, b| a.0.cmp(&b.0));
        let evaluations = evaluations
            .into_iter()
            .map(|x| x.1)
            .collect::<Vec<G1::ScalarField>>();
        end_timer!(eval_time);

        // absorb the evalution claims.
        fs_rng.absorb(&evaluations);

        // Saving the rng state for later recomputing the challenges
        let fs_rng_state = fs_rng.get_state().clone();

        /* The non-interactive batch evaluation proof for the polynomial commitment scheme,
        We pass the Fiat-Shamir rng.
        */

        let opening_time = start_timer!(|| "Compute opening proof");
        let pc_proof = PC::multi_point_multi_poly_open(
            pc_pk,
            polynomials.clone(),
            &labeled_comms,
            &query_set,
            &mut fs_rng,
            &comm_rands,
            Some(zk_rng),
        )
        .map_err(Error::from_pc_err)?;
        end_timer!(opening_time);

        let accumulated_sumcheck_acc = SumcheckItem {
            alpha: verifier_third_msg.gamma,
            eta: verifier_first_msg
                .eta
                .iter()
                .zip(previous_inner_sumcheck_acc.1.eta.iter())
                .map(|(&eta, &eta_prime)| eta + verifier_third_msg.lambda * eta_prime)
                .collect(),
            c: fourth_comms[0].commitment().clone(),
        };
        let new_inner_sumcheck_acc = DualSumcheckItem(
            accumulated_sumcheck_acc,
            previous_inner_sumcheck_acc.0.clone(),
        );

        let succinct_verifier_state = PC::<G1, D>::batch_succinct_verify(
            pc_pk,
            vec![labeled_comms.as_slice()],
            vec![&query_set],
            // TODO: we evaluate polynomials a further (third...) time. Can we do
            //       better by reusing evaluations?
            vec![&evaluate_query_set(polynomials.clone(), &query_set)],
            vec![&pc_proof],
            vec![&fs_rng_state],
        )
        .map_err(Error::from_pc_err)?;

        let accumulated_dlog_acc = DLogItem {
            g_final: GroupVec::new(vec![succinct_verifier_state[0].final_comm_key]),
            xi_s: succinct_verifier_state[0].check_poly.clone(),
        };

        let new_dlog_acc =
            DualDLogItem::<G1, G2>(vec![accumulated_dlog_acc], previous_dlog_acc.0.clone());

        let proof = Proof::new(commitments, evaluations, pc_proof);

        end_timer!(prover_time);

        proof.print_size_info();
        Ok((proof, new_inner_sumcheck_acc, new_dlog_acc))
    }

    /// Fully verify a proof as produced by `fn prove()`.
    /// Besides the proof itself the function needs as input the previous accumulators in order to
    /// initialize the Fiat-Shamir rng, and the current accumulators in order to check them.
    pub fn verify(
        index_vk_g1: &VerifierKey<G1, G2, D>,
        index_vk_g2: &VerifierKey<G2, G1, D>,
        pc_vk_g1: &<PC<G1, D> as PolynomialCommitment<G1>>::VerifierKey,
        pc_vk_g2: &<PC<G2, D> as PolynomialCommitment<G2>>::VerifierKey,
        public_input: &[G1::ScalarField],
        prev_inner_sumcheck_acc: &DualSumcheckItem<G2, G1>,
        prev_dlog_acc: &DualDLogItem<G2, G1>,
        curr_inner_sumcheck_acc: &DualSumcheckItem<G1, G2>,
        curr_dlog_acc: &DualDLogItem<G1, G2>,
        proof: &Proof<G1, G2, D>,
    ) -> Result<bool, Error<<PC<G1, D> as PolynomialCommitment<G1>>::Error>> {
        let verifier_time = start_timer!(|| "Marlin Verifier");
        let succinct_check = Self::succinct_verify(
            pc_vk_g1,
            index_vk_g1,
            public_input,
            prev_inner_sumcheck_acc,
            prev_dlog_acc,
            curr_inner_sumcheck_acc,
            curr_dlog_acc,
            proof,
        );
        if succinct_check.is_err() {
            end_timer!(verifier_time);
            eprintln!("IOP Verification failed: {:?}", succinct_check.err());
            return Ok(false);
        }

        let hard_check = Self::hard_verify(
            pc_vk_g1,
            pc_vk_g2,
            index_vk_g1,
            index_vk_g2,
            curr_inner_sumcheck_acc,
            curr_dlog_acc,
        );
        if hard_check.is_err() {
            end_timer!(verifier_time);
            eprintln!("IOP Verification failed: {:?}", hard_check.err());
            return Ok(false);
        }

        end_timer!(verifier_time);
        Ok(true)
    }

    /// Succinctly verify a proof as produced by `fn prove()`.
    /// Does perform the IOP verification, checks the succinct part of the polynomial opening proof,
    /// and checks that the current accumulators are coherent with the previous ones and the proof
    /// itself.
    pub fn succinct_verify<'a>(
        pc_vk: &<PC<G1, D> as PolynomialCommitment<G1>>::VerifierKey,
        index_vk: &VerifierKey<G1, G2, D>,
        public_input: &[G1::ScalarField],
        prev_inner_sumcheck_acc: &DualSumcheckItem<G2, G1>,
        prev_dlog_acc: &DualDLogItem<G2, G1>,
        curr_inner_sumcheck_acc: &DualSumcheckItem<G1, G2>,
        curr_dlog_acc: &DualDLogItem<G1, G2>,
        proof: &Proof<G1, G2, D>,
    ) -> Result<(), Error<<PC<G1, D> as PolynomialCommitment<G1>>::Error>> {
        let iop_verification_time = start_timer!(|| "Verify Sumcheck equations");

        let public_input = public_input.to_vec();

        let verifier_init_state =
            IOP::verifier_init(&index_vk.index.index_info, prev_inner_sumcheck_acc)?;

        let mut fs_rng = Self::fiat_shamir_rng_init(
            pc_vk,
            index_vk,
            &public_input,
            prev_inner_sumcheck_acc,
            prev_dlog_acc,
        )
        .map_err(Error::from_pc_err)?;

        /*  First round of the compiled and Fiat-Shamir transformed oracle proof
         */
        let first_comms = &proof.commitments[0];
        fs_rng.absorb(&to_bytes![first_comms].unwrap());

        let (_, verifier_state) = IOP::verifier_first_round(verifier_init_state, &mut fs_rng)?;

        /*  Second round of the compiled and Fiat-Shamir transformed oracle proof-
        The verification of the outer sumcheck equation is postponed to below
        */
        let second_comms = &proof.commitments[1];
        fs_rng.absorb(&to_bytes![second_comms].unwrap());

        let (_, verifier_state) = IOP::verifier_second_round(verifier_state, &mut fs_rng)?;

        /*  Third round of the compiled and Fiat-Shamir transformed oracle proof
         */
        let third_comms = &proof.commitments[2];
        fs_rng.absorb(&to_bytes![third_comms].unwrap());

        let (_, verifier_state) = IOP::verifier_third_round(verifier_state, &mut fs_rng)?;

        /*  Fourth round of the compiled and Fiat-Shamir transformed oracle proof
         */
        let fourth_comms = &proof.commitments[3];
        fs_rng.absorb(&to_bytes![fourth_comms].unwrap());

        let accumulator_comms = &vec![
            prev_inner_sumcheck_acc.1.c.clone(),
            prev_dlog_acc.1[0].g_final.clone(),
        ];

        // Gather commitments in one vector.
        let commitments: Vec<_> = first_comms
            .into_iter()
            .chain(second_comms)
            .chain(third_comms)
            .chain(fourth_comms)
            .chain(accumulator_comms)
            .cloned()
            .zip(IOP::<G1, G2>::polynomial_labels())
            .map(|(c, l)| LabeledCommitment::new(l, c))
            .collect();

        // Check sumchecks equations
        let (query_set, verifier_state) = IOP::verifier_query_set(verifier_state)?;

        let mut evaluations = Evaluations::new();
        let mut evaluation_labels = Vec::new();
        for (poly_label, (point_label, point)) in query_set.iter().cloned() {
            evaluation_labels.push(((poly_label, point_label), point));
        }

        evaluation_labels.sort_by(|a, b| a.0.cmp(&b.0));
        for (q, eval) in evaluation_labels.into_iter().zip(&proof.evaluations) {
            evaluations.insert(((q.0).0, q.1), *eval);
        }

        // Check that the polynomial behind the commitment of the `x` poly from the first round is
        // indeed the (formatted) input polynomial.
        // This is done by performing a MSM between the `lagrange_comms` and the (formatted) input
        // poly and comparing the result with the aforementioned commitment.
        let x_poly_comm = index_vk
            .lagrange_comms
            .iter()
            .zip(IOP::<G1, G2>::format_public_input(&public_input).iter())
            .map(|(g, x)| g[0] * x)
            .reduce(|a, b| a + b)
            .expect("public input should include at least one element");

        if x_poly_comm != first_comms[0][0] {
            end_timer!(iop_verification_time);
            return Err(Error::Other(
                "Public input not coherent with commitment of x poly inside proof".to_string(),
            ));
        }

        let result = IOP::verify_outer_sumcheck(&public_input, &evaluations, &verifier_state);

        if result.is_err() {
            end_timer!(iop_verification_time);
            return Err(Error::IOPError(result.unwrap_err()));
        }

        let result = IOP::verify_inner_sumcheck_aggregation(&evaluations, &verifier_state);

        if result.is_err() {
            end_timer!(iop_verification_time);
            return Err(Error::IOPError(result.unwrap_err()));
        }

        fs_rng.absorb(&proof.evaluations);

        // Perform succinct verification of opening proof
        let result =
            <PC<G1, D> as PolynomialCommitment<G1>>::succinct_multi_point_multi_poly_verify(
                pc_vk,
                &commitments,
                &query_set,
                &evaluations,
                &proof.pc_proof,
                &mut fs_rng,
            );

        if result.is_err() {
            end_timer!(iop_verification_time);
            return Err(Error::PolynomialCommitmentError(result.unwrap_err()));
        }

        let opening_result = result.unwrap();
        if opening_result.is_none() {
            return Err(Error::PolynomialCommitmentError(
                poly_commit::Error::FailedSuccinctCheck,
            ));
        }

        let dlog_verifier_state = opening_result.unwrap();

        if curr_dlog_acc.1 != prev_dlog_acc.0
            || curr_dlog_acc.0[0].xi_s != dlog_verifier_state.check_poly
            || curr_dlog_acc.0[0].g_final[0] != dlog_verifier_state.final_comm_key
        {
            end_timer!(iop_verification_time);
            return Err(Error::IOPError(VerificationEquationFailed(
                "New dlog accumulator is not valid".to_owned(),
            )));
        }

        let mut eta = verifier_state.first_round_msg.unwrap().eta;
        for (eta, eta_prime) in eta.iter_mut().zip(prev_inner_sumcheck_acc.1.eta.iter()) {
            *eta += verifier_state.third_round_msg.unwrap().lambda * eta_prime;
        }

        if curr_inner_sumcheck_acc.1 != prev_inner_sumcheck_acc.0
            || curr_inner_sumcheck_acc.0.alpha != verifier_state.third_round_msg.unwrap().gamma
            || curr_inner_sumcheck_acc.0.eta != eta
            || curr_inner_sumcheck_acc.0.c != fourth_comms[0]
        {
            end_timer!(iop_verification_time);
            return Err(Error::IOPError(VerificationEquationFailed(
                "New inner sumcheck accumulator is not valid".to_owned(),
            )));
        }

        end_timer!(iop_verification_time);

        Ok(())
    }

    /// Perform the full check of both the inner-sumcheck and dlog accumulators.
    /// If succesful, return the polynomials associated to the accumulators.
    pub fn hard_verify(
        pc_vk_g1: &<PC<G1, D> as PolynomialCommitment<G1>>::VerifierKey,
        pc_vk_g2: &<PC<G2, D> as PolynomialCommitment<G2>>::VerifierKey,
        index_vk_g1: &VerifierKey<G1, G2, D>,
        index_vk_g2: &VerifierKey<G2, G1, D>,
        inner_sumcheck_acc: &DualSumcheckItem<G1, G2>,
        dlog_acc: &DualDLogItem<G1, G2>,
    ) -> Result<
        Option<(
            VerificationResult<G1::ScalarField>,
            VerificationResult<G2::ScalarField>,
        )>,
        Error<<PC<G1, D> as PolynomialCommitment<G1>>::Error>,
    > {
        let check_dlog_g1 = Self::check_dlog_item(pc_vk_g1, &dlog_acc.0[0])?;
        let check_inner_sumcheck_g1 =
            Self::check_inner_sumcheck_item(pc_vk_g1, index_vk_g1, &inner_sumcheck_acc.0)?;
        if check_dlog_g1.is_none() || check_inner_sumcheck_g1.is_none() {
            return Ok(None);
        }
        let verification_result_g1 = VerificationResult {
            bullet_poly: check_dlog_g1.unwrap(),
            t_acc_poly: check_inner_sumcheck_g1.unwrap(),
        };

        let check_dlog_g2 = Self::check_dlog_item(pc_vk_g2, &dlog_acc.1[0])?;
        let check_inner_sumcheck_g2 =
            Self::check_inner_sumcheck_item(pc_vk_g2, index_vk_g2, &inner_sumcheck_acc.1)?;
        if check_dlog_g2.is_none() || check_inner_sumcheck_g2.is_none() {
            return Ok(None);
        }
        let verification_result_g2 = VerificationResult {
            bullet_poly: check_dlog_g2.unwrap(),
            t_acc_poly: check_inner_sumcheck_g2.unwrap(),
        };

        Ok(Some((verification_result_g1, verification_result_g2)))
    }

    fn check_dlog_item<G: Curve>(
        pc_vk: &<PC<G, D> as PolynomialCommitment<G>>::VerifierKey,
        dlog_item: &DLogItem<G>,
    ) -> Result<
        Option<DensePolynomial<G::ScalarField>>,
        Error<<PC<G, D> as PolynomialCommitment<G>>::Error>,
    > {
        let time = start_timer!(|| "Checking dlog accumulator item");
        let verifier_state = poly_commit::ipa_pc::VerifierState {
            check_poly: dlog_item.xi_s.clone(),
            final_comm_key: dlog_item
                .g_final
                .get_vec()
                .get(0)
                .unwrap_or(&G::zero())
                .clone(),
        };
        let res = <PC<G, D> as PolynomialCommitment<G>>::hard_verify(pc_vk, &verifier_state)
            .map_err(Error::from_pc_err)?
            .map(|verifier_output| verifier_output.bullet_poly);

        end_timer!(time);

        Ok(res)
    }

    fn check_inner_sumcheck_item<Ga: Curve, Gb: Curve>(
        pc_vk: &<PC<Ga, D> as PolynomialCommitment<Ga>>::VerifierKey,
        index_vk: &VerifierKey<Ga, Gb, D>,
        inner_sumcheck_item: &SumcheckItem<Ga>,
    ) -> Result<
        Option<DensePolynomial<Ga::ScalarField>>,
        Error<<PC<Ga, D> as PolynomialCommitment<Ga>>::Error>,
    > {
        let time = start_timer!(|| "Checking inner sumcheck accumulator item");
        let num_inputs = index_vk.index.index_info.num_inputs;
        let num_witness = index_vk.index.index_info.num_witness;
        let num_constraints = index_vk.index.index_info.num_constraints;

        let domain_x = get_best_evaluation_domain::<Ga::ScalarField>(num_inputs).unwrap();
        let domain_h = get_best_evaluation_domain::<Ga::ScalarField>(std::cmp::max(
            num_constraints,
            num_inputs + num_witness,
        ))
        .unwrap();

        let alpha = inner_sumcheck_item.alpha;
        let l_x_alpha_evals_on_h = domain_h.domain_eval_lagrange_kernel(alpha)?;

        let t_evals_on_h = IOP::<Ga, Gb>::calculate_t(
            vec![&index_vk.index.a, &index_vk.index.b, &index_vk.index.c].into_iter(),
            &inner_sumcheck_item.eta,
            &domain_x,
            domain_h.clone(),
            &l_x_alpha_evals_on_h,
        )?;
        let t_poly =
            EvaluationsOnDomain::from_vec_and_domain(t_evals_on_h.clone(), domain_h.clone())
                .interpolate();

        let t_comm = <PC<Ga, D> as PolynomialCommitment<Ga>>::commit(&pc_vk, &t_poly, false, None)
            .map_err(Error::from_pc_err)?;

        if t_comm.0 != inner_sumcheck_item.c {
            end_timer!(time);
            return Err(Error::IOPError(VerificationEquationFailed(
                "Hard check of inner sumcheck accumulator failed".to_owned(),
            )));
        }

        end_timer!(time);
        Ok(Some(t_poly))
    }
}
