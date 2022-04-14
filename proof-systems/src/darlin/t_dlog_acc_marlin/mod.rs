use crate::darlin::accumulators::dlog::{DLogItem, DualDLogItem};
use crate::darlin::t_dlog_acc_marlin::data_structures::{
    DualSumcheckItem, Proof, ProverKey, SumcheckItem, VerifierKey, PC,
};
use crate::darlin::t_dlog_acc_marlin::iop::IOP;
use crate::darlin::IPACurve;
use algebra::CanonicalSerialize;
use algebra::{
    get_best_evaluation_domain, serialize_no_metadata, DensePolynomial,
    Evaluations as EvaluationsOnDomain, Group, GroupVec, ToConstraintField,
};
use bench_utils::{end_timer, start_timer};
use digest::Digest;
use fiat_shamir::{FiatShamirRng, FiatShamirRngSeed};
use marlin::iop::Error::VerificationEquationFailed;
use marlin::iop::LagrangeKernel;
use marlin::Error;
use num_traits::Zero;
use poly_commit::ipa_pc::CommitterKey;
use poly_commit::optional_rng::OptionalRng;
use poly_commit::{
    evaluate_query_map_to_vec, Evaluations, LabeledCommitment, LabeledPolynomial,
    LabeledRandomness, PCKey, PolynomialCommitment,
};
use r1cs_core::ConstraintSynthesizer;
use rand::RngCore;
use std::marker::PhantomData;

pub mod data_structures;
pub mod iop;
#[cfg(test)]
mod test;

/// A helper struct to bundle the t-dlog accumulator Marlin functions for setup, prove and
/// verify.
pub struct TDLogAccMarlin<G1: IPACurve, G2: IPACurve, FS: FiatShamirRng, D: Digest>(
    #[doc(hidden)] PhantomData<G1>,
    #[doc(hidden)] PhantomData<G2>,
    #[doc(hidden)] PhantomData<FS>,
    #[doc(hidden)] PhantomData<D>,
);

impl<G1, G2, FS, D> TDLogAccMarlin<G1, G2, FS, D>
where
    G1: IPACurve<BaseField = <G2 as Group>::ScalarField>
        + ToConstraintField<<G2 as Group>::ScalarField>,
    G2: IPACurve<BaseField = <G1 as Group>::ScalarField>
        + ToConstraintField<<G1 as Group>::ScalarField>,
    FS: FiatShamirRng + 'static,
    D: Digest,
{
    /// The personalization string for this protocol. Used to personalize the
    /// Fiat-Shamir rng.
    pub const PROTOCOL_NAME: &'static [u8] = b"T-DLOG-ACC-MARLIN-2022";

    /// Generate the universal prover and verifier keys for the
    /// argument system.
    pub fn universal_setup(
        num_constraints: usize,
        num_variables: usize,
        zk: bool,
    ) -> Result<
        (
            CommitterKey<G1>,
            <PC<G1, FS> as PolynomialCommitment<G1>>::VerifierKey,
        ),
        Error<<PC<G1, FS> as PolynomialCommitment<G1>>::Error>,
    > {
        let max_degree = IOP::<G1, G2>::max_degree(num_constraints, num_variables, zk)?;
        let setup_time = start_timer!(|| {
            format!(
            "Marlin::UniversalSetup with max_degree {}, computed for a maximum of {} constraints, {} vars",
            max_degree, num_constraints, num_variables,
        )
        });

        let srs = PC::<G1, FS>::setup::<D>(max_degree).map_err(Error::from_pc_err);
        end_timer!(setup_time);
        srs
    }

    /// The circuit-specific setup. Given a circuit `c` and a committer_key of the polynomial
    /// commitment scheme, generate the key material for the circuit. The latter is split into
    /// a prover key and a verifier key.
    pub fn circuit_specific_setup<C: ConstraintSynthesizer<G1::ScalarField>>(
        committer_key: &<PC<G1, FS> as PolynomialCommitment<G1>>::CommitterKey,
        c: C,
    ) -> Result<
        (ProverKey<G1, G2, FS>, VerifierKey<G1, G2, FS>),
        Error<<PC<G1, FS> as PolynomialCommitment<G1>>::Error>,
    > {
        let index_time = start_timer!(|| "Marlin::Index");

        let index = IOP::<G1, G2>::index(c)?;

        end_timer!(index_time);

        // Compute the commitments of the Lagrange polynomials over the input domain.
        // They are included into the verifier key in order to help the circuit verifier not to
        // perform a lagrange kernel evaluation in non native arithmetic.
        let domain_x = get_best_evaluation_domain(index.index_info.num_inputs).unwrap();
        let lagrange_comms: Vec<_> = domain_x
            .elements()
            .into_iter()
            .map(|y| domain_x.slice_lagrange_kernel(y))
            .map(|poly| {
                <PC<G1, FS> as PolynomialCommitment<G1>>::commit(committer_key, &poly, false, None)
                    .unwrap()
                    .0
            })
            .collect();

        let vk_hash = D::digest(
            &serialize_no_metadata![index.index_info, index.a, index.b, index.c]
                .map_err(|e| Error::Other(format!("Unable to serialize vk elements: {:?}", e)))?,
        )
        .as_ref()
        .to_vec();

        let index_vk = VerifierKey {
            index,
            lagrange_comms,
            vk_hash,
        };

        let index_pk = ProverKey {
            index_vk: index_vk.clone(),
        };

        Ok((index_pk, index_vk))
    }

    fn fiat_shamir_rng_init(
        pc_vk: &<PC<G1, FS> as PolynomialCommitment<G1>>::VerifierKey,
        index_vk: &VerifierKey<G1, G2, FS>,
        x_poly_comm: &<PC<G1, FS> as PolynomialCommitment<G1>>::Commitment,
        inner_sumcheck_acc: &DualSumcheckItem<G2, G1>,
        dlog_acc: &DualDLogItem<G2, G1>,
    ) -> Result<<PC<G1, FS> as PolynomialCommitment<G1>>::RandomOracle, poly_commit::error::Error>
    {
        // initialize the Fiat-Shamir rng.
        let fs_rng_init_seed = {
            let mut seed_builder = FiatShamirRngSeed::new();
            seed_builder
                .add_bytes(&Self::PROTOCOL_NAME)?
                .add_bytes(&pc_vk.get_hash())?;
            seed_builder.finalize()?
        };
        let mut fs_rng =
            <PC<G1, FS> as PolynomialCommitment<G1>>::RandomOracle::from_seed(fs_rng_init_seed)?;
        fs_rng.record(inner_sumcheck_acc.clone())?;
        fs_rng.record(dlog_acc.clone())?;
        fs_rng.record::<G1::BaseField, _>(index_vk.get_hash())?;
        fs_rng.record(x_poly_comm.clone())?;
        Ok(fs_rng)
    }

    /// Produce a zkSNARK which proves both the satisfiability of circuit `c` and the statements of
    /// the previous accumulators `previous_inner_sumcheck_acc` and `previous_dlog_acc`.
    /// Need in input also the polynomials associated to the two accumulators, namely
    /// `previous_inner_sumcheck_poly` and `previous_bullet_poly`.
    /// In typical recursive usage, the accumulators and their respective polynomials are generated
    /// by running the full verifier `fn verify()` on the proof generated by a previous call to
    /// `fn prove()`.
    pub fn prove<C: ConstraintSynthesizer<G1::ScalarField>>(
        index_pk: &ProverKey<G1, G2, FS>,
        pc_pk: &<PC<G1, FS> as PolynomialCommitment<G1>>::CommitterKey,
        c: C,
        previous_inner_sumcheck_acc: &DualSumcheckItem<G2, G1>,
        previous_dlog_acc: &DualDLogItem<G2, G1>,
        previous_inner_sumcheck_poly: &DensePolynomial<G1::ScalarField>,
        previous_bullet_poly: &DensePolynomial<G1::ScalarField>,
        zk: bool,
        zk_rng: Option<&mut dyn RngCore>,
    ) -> Result<Proof<G1, G2, FS>, Error<<PC<G1, FS> as PolynomialCommitment<G1>>::Error>> {
        if zk_rng.is_some() && !zk || zk_rng.is_none() && zk {
            return Err(Error::Other("If ZK is enabled, a RNG must be passed (and viceversa); conversely, if ZK is disabled, a RNG must NOT be passed (and viceversa)".to_owned()));
        }

        let zk_rng = &mut OptionalRng(zk_rng);
        let prover_time = start_timer!(|| "Marlin::Prover");

        let (prover_init_oracles, prover_init_state) =
            IOP::prover_init(&index_pk.index_vk.index, c, previous_inner_sumcheck_acc)?;

        let x_poly_comm_time = start_timer!(|| "Committing to input poly");
        let (init_comms, init_comm_rands) = <PC<G1, FS> as PolynomialCommitment<G1>>::commit_many(
            pc_pk,
            prover_init_oracles.iter(),
            None,
        )
        .map_err(Error::from_pc_err)?;
        end_timer!(x_poly_comm_time);

        let verifier_init_state = IOP::verifier_init(
            &index_pk.index_vk.index.index_info,
            previous_inner_sumcheck_acc,
        )?;

        let mut fs_rng = Self::fiat_shamir_rng_init(
            pc_pk,
            &index_pk.index_vk,
            init_comms[0].commitment(),
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
        let (first_comms, first_comm_rands) =
            <PC<G1, FS> as PolynomialCommitment<G1>>::commit_many(
                pc_pk,
                prover_first_oracles.iter(),
                Some(zk_rng),
            )
            .map_err(Error::from_pc_err)?;
        end_timer!(first_round_comm_time);

        // record the prove oracles by the Fiat-Shamir rng
        fs_rng.record(
            first_comms
                .iter()
                .map(|labeled_comm| labeled_comm.commitment().clone())
                .collect::<Vec<_>>(),
        )?;

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
            <PC<G1, FS> as PolynomialCommitment<G1>>::commit_many(
                pc_pk,
                prover_second_oracles.iter(),
                Some(zk_rng),
            )
            .map_err(Error::from_pc_err)?;
        end_timer!(second_round_comm_time);

        // record the prove oracles by the Fiat-Shamir rng
        fs_rng.record(
            second_comms
                .iter()
                .map(|labeled_comm| labeled_comm.commitment().clone())
                .collect::<Vec<_>>(),
        )?;

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
        let (third_comms, third_comm_rands) =
            <PC<G1, FS> as PolynomialCommitment<G1>>::commit_many(
                pc_pk,
                prover_third_oracles.iter(),
                Some(zk_rng),
            )
            .map_err(Error::from_pc_err)?;
        end_timer!(third_round_comm_time);

        // record the prove oracles by the Fiat-Shamir rng
        fs_rng.record(
            third_comms
                .iter()
                .map(|labeled_comm| labeled_comm.commitment().clone())
                .collect::<Vec<_>>(),
        )?;

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
            <PC<G1, FS> as PolynomialCommitment<G1>>::commit_many(
                pc_pk,
                prover_fourth_oracles.iter(),
                Some(zk_rng),
            )
            .map_err(Error::from_pc_err)?;
        end_timer!(fourth_round_comm_time);

        // record the prover oracles by the Fiat-Shamir rng
        fs_rng.record(
            fourth_comms
                .iter()
                .map(|labeled_comm| labeled_comm.commitment().clone())
                .collect::<Vec<_>>(),
        )?;

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
        let accumulator_comm_rands = vec![
            LabeledRandomness::new(
                "prev_t_acc_poly".to_string(),
                <PC<G1, FS> as PolynomialCommitment<G1>>::Randomness::zero(),
            ),
            LabeledRandomness::new(
                "prev_bullet_poly".to_string(),
                <PC<G1, FS> as PolynomialCommitment<G1>>::Randomness::zero(),
            ),
        ];

        // Gather prover polynomials in one vector.
        let polynomials: Vec<_> = prover_init_oracles
            .iter()
            .chain(prover_first_oracles.iter())
            .chain(prover_second_oracles.iter())
            .chain(prover_third_oracles.iter())
            .chain(prover_fourth_oracles.iter())
            .chain(prover_accumulator_oracles.iter())
            .collect();

        // Gather commitment randomness together.
        let comm_rands: Vec<_> = init_comm_rands
            .into_iter()
            .chain(first_comm_rands)
            .chain(second_comm_rands)
            .chain(third_comm_rands)
            .chain(fourth_comm_rands)
            .chain(accumulator_comm_rands)
            .collect();

        // Gather commitments in one vector.
        // The commitment of the input poly is not included in the proof, because it needs to be
        // recomputed by the verifier anyways.
        #[rustfmt::skip]
            let commitments = vec![
            first_comms.iter().map(|p| p.commitment().clone()).collect(),
            second_comms.iter().map(|p| p.commitment().clone()).collect(),
            third_comms.iter().map(|p| p.commitment().clone()).collect(),
            fourth_comms.iter().map(|p| p.commitment().clone()).collect(),
        ];

        // Set up the IOP verifier's query set.
        let (query_map, _) = IOP::verifier_query_map(verifier_state)?;

        // Compute the queried values
        let eval_time = start_timer!(|| "Evaluating polynomials over query set");

        let mut evaluations = evaluate_query_map_to_vec(polynomials.clone(), &query_map);

        evaluations.sort_by(|a, b| a.0.cmp(&b.0));
        let evaluations = evaluations
            .into_iter()
            .map(|x| x.1)
            .collect::<Vec<G1::ScalarField>>();
        end_timer!(eval_time);

        // record the evalution claims.
        fs_rng.record(evaluations.clone())?;

        /* The non-interactive batch evaluation proof for the polynomial commitment scheme,
        We pass the Fiat-Shamir rng.
        */
        let opening_time = start_timer!(|| "Compute opening proof");
        let pc_proof = PC::multi_point_multi_poly_open(
            pc_pk,
            polynomials.clone(),
            &query_map,
            &mut fs_rng,
            &comm_rands,
            Some(zk_rng),
        )
        .map_err(Error::from_pc_err)?;
        end_timer!(opening_time);

        let proof = Proof::new(commitments, evaluations, pc_proof);

        end_timer!(prover_time);

        proof.print_size_info();
        Ok(proof)
    }

    /// Fully verify a proof as produced by `fn prove()`.
    /// Besides the proof itself the function needs as input the previous accumulators in order to
    /// initialize the Fiat-Shamir rng.
    /// If successful, return the new accumulators and the respective polynomials.
    // TODO: The return type of this function is quite ugly. Maybe we can improve by bundling
    //  together the accumulators and the respective polys
    pub fn verify(
        index_vk_g1: &VerifierKey<G1, G2, FS>,
        index_vk_g2: &VerifierKey<G2, G1, FS>,
        pc_vk_g1: &<PC<G1, FS> as PolynomialCommitment<G1>>::VerifierKey,
        pc_vk_g2: &<PC<G2, FS> as PolynomialCommitment<G2>>::VerifierKey,
        public_input: &[G1::ScalarField],
        prev_inner_sumcheck_acc: &DualSumcheckItem<G2, G1>,
        prev_dlog_acc: &DualDLogItem<G2, G1>,
        proof: &Proof<G1, G2, FS>,
    ) -> Result<
        (
            DualSumcheckItem<G1, G2>,
            (
                DensePolynomial<G1::ScalarField>,
                DensePolynomial<G2::ScalarField>,
            ),
            DualDLogItem<G1, G2>,
            (
                DensePolynomial<G1::ScalarField>,
                DensePolynomial<G2::ScalarField>,
            ),
        ),
        Error<<PC<G1, FS> as PolynomialCommitment<G1>>::Error>,
    > {
        let verifier_time = start_timer!(|| "Marlin Verifier");
        let (inner_sumcheck_acc, dlog_acc) = Self::succinct_verify(
            pc_vk_g1,
            index_vk_g1,
            public_input,
            prev_inner_sumcheck_acc,
            prev_dlog_acc,
            proof,
        )?;

        let (inner_sumcheck_polys, dlog_polys) = Self::hard_verify(
            pc_vk_g1,
            pc_vk_g2,
            index_vk_g1,
            index_vk_g2,
            &inner_sumcheck_acc,
            &dlog_acc,
        )?;

        end_timer!(verifier_time);

        Ok((
            inner_sumcheck_acc,
            inner_sumcheck_polys,
            dlog_acc,
            dlog_polys,
        ))
    }

    /// Succinctly verify a proof as produced by `fn prove()`.
    /// Perform the IOP verification, and check the succinct part of the polynomial opening proof.
    /// If successful, return the new accumulators.
    pub fn succinct_verify<'a>(
        pc_vk: &<PC<G1, FS> as PolynomialCommitment<G1>>::VerifierKey,
        index_vk: &VerifierKey<G1, G2, FS>,
        public_input: &[G1::ScalarField],
        prev_inner_sumcheck_acc: &DualSumcheckItem<G2, G1>,
        prev_dlog_acc: &DualDLogItem<G2, G1>,
        proof: &Proof<G1, G2, FS>,
    ) -> Result<
        (DualSumcheckItem<G1, G2>, DualDLogItem<G1, G2>),
        Error<<PC<G1, FS> as PolynomialCommitment<G1>>::Error>,
    > {
        let iop_verification_time = start_timer!(|| "Verify Sumcheck equations");

        let verifier_init_state =
            IOP::verifier_init(&index_vk.index.index_info, prev_inner_sumcheck_acc)?;

        let x_poly_comm = index_vk
            .lagrange_comms
            .iter()
            .zip(IOP::<G1, G2>::format_public_input(&public_input).iter())
            .map(|(g, x)| g.clone() * x)
            .reduce(|a, b| a + b)
            .expect("public input should include at least one element");

        let mut fs_rng = Self::fiat_shamir_rng_init(
            pc_vk,
            index_vk,
            &x_poly_comm,
            prev_inner_sumcheck_acc,
            prev_dlog_acc,
        )
        .map_err(Error::from_pc_err)?;

        /*  The commitment of the input poly is not included in the proof, because it needs to be
           recomputed by the verifier anyways
        */
        let init_comms = vec![x_poly_comm];

        /*  First round of the compiled and Fiat-Shamir transformed oracle proof
         */
        let first_comms = &proof.commitments[0];
        fs_rng.record(first_comms.clone())?;

        let (_, verifier_state) = IOP::verifier_first_round(verifier_init_state, &mut fs_rng)?;

        /*  Second round of the compiled and Fiat-Shamir transformed oracle proof-
        The verification of the outer sumcheck equation is postponed to below
        */
        let second_comms = &proof.commitments[1];
        fs_rng.record(second_comms.clone())?;

        let (_, verifier_state) = IOP::verifier_second_round(verifier_state, &mut fs_rng)?;

        /*  Third round of the compiled and Fiat-Shamir transformed oracle proof
         */
        let third_comms = &proof.commitments[2];
        fs_rng.record(third_comms.clone())?;

        let (_, verifier_state) = IOP::verifier_third_round(verifier_state, &mut fs_rng)?;

        /*  Fourth round of the compiled and Fiat-Shamir transformed oracle proof
         */
        let fourth_comms = &proof.commitments[3];
        fs_rng.record(fourth_comms.clone())?;

        let accumulator_comms = &vec![
            prev_inner_sumcheck_acc.1.c.clone(),
            GroupVec::new(vec![prev_dlog_acc.1[0].final_comm_key.clone()]),
        ];

        // Gather commitments in one vector.
        let commitments: Vec<_> = init_comms
            .iter()
            .chain(first_comms)
            .chain(second_comms)
            .chain(third_comms)
            .chain(fourth_comms)
            .chain(accumulator_comms)
            .cloned()
            .zip(IOP::<G1, G2>::polynomial_labels())
            .map(|(c, l)| LabeledCommitment::new(l, c))
            .collect();

        // Check sumchecks equations
        let (query_map, verifier_state) = IOP::verifier_query_map(verifier_state)?;

        let mut evaluation_keys = Vec::new();
        for (point_label, (_, poly_set)) in query_map.iter() {
            for poly_label in poly_set {
                evaluation_keys.push((poly_label.clone(), point_label.clone()));
            }
        }
        evaluation_keys.sort();

        let mut evaluations = Evaluations::new();
        for (key, &eval) in evaluation_keys.into_iter().zip(proof.evaluations.iter()) {
            evaluations.insert(key, eval);
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

        let result = IOP::verify_dlog_aggregation(&evaluations, &verifier_state);

        if result.is_err() {
            end_timer!(iop_verification_time);
            return Err(Error::IOPError(result.unwrap_err()));
        }

        fs_rng.record(proof.evaluations.clone())?;

        // Perform succinct verification of opening proof
        let result =
            <PC<G1, FS> as PolynomialCommitment<G1>>::succinct_multi_point_multi_poly_verify(
                pc_vk,
                &commitments,
                &query_map,
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

        let new_dlog_acc = DualDLogItem(vec![dlog_verifier_state], prev_dlog_acc.0.clone());

        let mut eta = verifier_state.first_round_msg.unwrap().get_etas();
        for (eta, eta_prime) in eta.iter_mut().zip(prev_inner_sumcheck_acc.1.eta.iter()) {
            *eta += verifier_state.third_round_msg.unwrap().lambda * eta_prime;
        }

        let new_inner_sumcheck_acc = DualSumcheckItem(
            SumcheckItem {
                alpha: verifier_state.third_round_msg.unwrap().gamma,
                eta,
                c: fourth_comms[0].clone(),
            },
            prev_inner_sumcheck_acc.0.clone(),
        );

        end_timer!(iop_verification_time);

        Ok((new_inner_sumcheck_acc, new_dlog_acc))
    }

    /// Perform the full check of both the inner-sumcheck and dlog accumulators.
    /// If succesful, return the polynomials associated to the accumulators.
    pub fn hard_verify(
        pc_vk_g1: &<PC<G1, FS> as PolynomialCommitment<G1>>::VerifierKey,
        pc_vk_g2: &<PC<G2, FS> as PolynomialCommitment<G2>>::VerifierKey,
        index_vk_g1: &VerifierKey<G1, G2, FS>,
        index_vk_g2: &VerifierKey<G2, G1, FS>,
        inner_sumcheck_acc: &DualSumcheckItem<G1, G2>,
        dlog_acc: &DualDLogItem<G1, G2>,
    ) -> Result<
        (
            (
                DensePolynomial<G1::ScalarField>,
                DensePolynomial<G2::ScalarField>,
            ),
            (
                DensePolynomial<G1::ScalarField>,
                DensePolynomial<G2::ScalarField>,
            ),
        ),
        Error<<PC<G1, FS> as PolynomialCommitment<G1>>::Error>,
    > {
        let dlog_poly_g1 = Self::check_dlog_item(pc_vk_g1, &dlog_acc.0[0])?;
        let inner_sumcheck_poly_g1 =
            Self::check_inner_sumcheck_item(pc_vk_g1, index_vk_g1, &inner_sumcheck_acc.0)?;

        let dlog_poly_g2 = Self::check_dlog_item(pc_vk_g2, &dlog_acc.1[0])?;
        let inner_sumcheck_poly_g2 =
            Self::check_inner_sumcheck_item(pc_vk_g2, index_vk_g2, &inner_sumcheck_acc.1)?;

        let dlog_polys = (dlog_poly_g1, dlog_poly_g2);
        let inner_sumcheck_polys = (inner_sumcheck_poly_g1, inner_sumcheck_poly_g2);

        Ok((inner_sumcheck_polys, dlog_polys))
    }

    fn check_dlog_item<G: IPACurve>(
        pc_vk: &<PC<G, FS> as PolynomialCommitment<G>>::VerifierKey,
        dlog_item: &DLogItem<G>,
    ) -> Result<DensePolynomial<G::ScalarField>, Error<<PC<G, FS> as PolynomialCommitment<G>>::Error>>
    {
        let time = start_timer!(|| "Checking dlog accumulator item");
        let verifier_output = <PC<G, FS> as PolynomialCommitment<G>>::hard_verify(pc_vk, dlog_item)
            .map_err(Error::from_pc_err)?;

        if verifier_output.is_none() {
            end_timer!(time);
            return Err(Error::IOPError(VerificationEquationFailed(
                "Hard check of dlog accumulator failed".to_owned(),
            )));
        }

        let result = verifier_output.unwrap().bullet_poly;
        end_timer!(time);

        Ok(result)
    }

    fn check_inner_sumcheck_item<Ga: IPACurve, Gb: IPACurve>(
        pc_vk: &<PC<Ga, FS> as PolynomialCommitment<Ga>>::VerifierKey,
        index_vk: &VerifierKey<Ga, Gb, FS>,
        inner_sumcheck_item: &SumcheckItem<Ga>,
    ) -> Result<
        DensePolynomial<Ga::ScalarField>,
        Error<<PC<Ga, FS> as PolynomialCommitment<Ga>>::Error>,
    > {
        let time = start_timer!(|| "Checking inner sumcheck accumulator item");

        let t_poly = inner_sumcheck_item.compute_poly(&index_vk.index);
        let t_comm = <PC<Ga, FS> as PolynomialCommitment<Ga>>::commit(&pc_vk, &t_poly, false, None)
            .map_err(Error::from_pc_err)?;

        if t_comm.0 != inner_sumcheck_item.c {
            end_timer!(time);
            return Err(Error::IOPError(VerificationEquationFailed(
                "Hard check of inner sumcheck accumulator failed".to_owned(),
            )));
        }

        end_timer!(time);
        Ok(t_poly)
    }
}
