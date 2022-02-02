use crate::darlin::accumulators::dlog::{DLogItem, DualDLogItem};
use crate::darlin::dlog_acc_marlin::data_structures::{
    DLogAccMarlinProof, DLogAccMarlinProverKey, DLogAccMarlinVerifierKey, PC,
};
use algebra::{to_bytes, Curve, DensePolynomial, Group, GroupVec, ToBytes, ToConstraintField};
use digest::Digest;
use marlin::{Error, Marlin, IOP};
use poly_commit::fiat_shamir_rng::{FiatShamirRng, FiatShamirRngSeed};
use poly_commit::ipa_pc::VerifierState;
use poly_commit::optional_rng::OptionalRng;
use poly_commit::{
    evaluate_query_set, evaluate_query_set_to_vec,
    ipa_pc::{CommitterKey as DLogProverKey, Parameters},
    Evaluations, LabeledCommitment, LabeledPolynomial, LabeledRandomness, PCCommitterKey,
    PolynomialCommitment, QuerySet,
};
use r1cs_core::ConstraintSynthesizer;
use rand::RngCore;
use std::marker::PhantomData;

pub mod data_structures;

pub struct DLogAccMarlin<G1: Curve, G2: Curve, D: Digest>(
    #[doc(hidden)] PhantomData<G1>,
    #[doc(hidden)] PhantomData<G2>,
    #[doc(hidden)] PhantomData<D>,
);

impl<G1: Curve, G2: Curve, D: Digest> DLogAccMarlin<G1, G2, D>
where
    G1: Curve<BaseField = <G2 as Group>::ScalarField>
        + ToConstraintField<<G2 as Group>::ScalarField>,
    G2: Curve<BaseField = <G1 as Group>::ScalarField>
        + ToConstraintField<<G1 as Group>::ScalarField>,
    D: Digest + 'static,
{
    /// The personalization string for this protocol. Used to personalize the
    /// Fiat-Shamir rng.
    pub const PROTOCOL_NAME: &'static [u8] = b"DLOG-ACC-MARLIN-2021";

    /// Generate the universal prover and verifier keys for the
    /// argument system.
    pub fn universal_setup(
        num_constraints: usize,
        num_variables: usize,
        num_non_zero: usize,
        zk: bool,
    ) -> Result<
        (Parameters<G1>, Parameters<G2>),
        Error<<PC<G1, D> as PolynomialCommitment<G1>>::Error>,
    > {
        let srs_g1 = Marlin::<G1, PC<G1, D>, D>::universal_setup(
            num_constraints,
            num_variables,
            num_non_zero,
            zk,
        )?;

        let srs_g2 = Marlin::<G2, PC<G2, D>, D>::universal_setup(
            num_constraints,
            num_variables,
            num_non_zero,
            zk,
        )?;

        Ok((srs_g1, srs_g2))
    }

    /// The circuit-specific setup. Given a circuit `c` and a committer_key of the polynomial
    /// commitment scheme, generate the key material for the circuit. The latter is split into
    /// a prover key and a verifier key.
    pub fn circuit_specific_setup<C: ConstraintSynthesizer<G1::ScalarField>>(
        committer_key: &DLogProverKey<G1>,
        c: C,
    ) -> Result<
        (
            DLogAccMarlinProverKey<G1, D>,
            DLogAccMarlinVerifierKey<G1, D>,
        ),
        Error<<PC<G1, D> as PolynomialCommitment<G1>>::Error>,
    > {
        let res = Marlin::<G1, PC<G1, D>, D>::circuit_specific_setup(committer_key, c)?;
        let res = (
            DLogAccMarlinProverKey(res.0),
            DLogAccMarlinVerifierKey(res.1),
        );
        Ok(res)
    }

    /// Produce a zkSNARK asserting given a constraint system `c` over a prime order field `F`
    pub fn prove<C: ConstraintSynthesizer<G1::ScalarField>>(
        index_pk: &DLogAccMarlinProverKey<G1, D>,
        pc_pk: &DLogProverKey<G1>,
        c: C,
        prev_acc: &DualDLogItem<G2, G1>,
        zk: bool,
        zk_rng: Option<&mut dyn RngCore>,
    ) -> Result<
        (DLogAccMarlinProof<G1, D>, DualDLogItem<G1, G2>),
        Error<<PC<G1, D> as PolynomialCommitment<G1>>::Error>,
    > {
        if zk_rng.is_some() && !zk || zk_rng.is_none() && zk {
            return Err(Error::Other("If ZK is enabled, a RNG must be passed (and viceversa); conversely, if ZK is disabled, a RNG must NOT be passed (and viceversa)".to_owned()));
        }

        let zk_rng = &mut OptionalRng(zk_rng);
        let prover_time = start_timer!(|| "Marlin::Prover");

        // prover precomputations
        let prover_init_state = IOP::prover_init(&index_pk.0.index, c)?;
        let public_input = prover_init_state.public_input();

        // initialise the Fiat-Shamir rng.
        let fs_rng_init_seed = {
            let mut seed_builder =
                <<PC<G1, D> as PolynomialCommitment<G1>>::RandomOracle as FiatShamirRng>::Seed::new(
                );
            seed_builder
                .add_bytes(&Self::PROTOCOL_NAME)
                .map_err(Error::from_pc_err)?;
            seed_builder
                .add_bytes(&pc_pk.get_hash())
                .map_err(Error::from_pc_err)?;
            seed_builder
                .add_bytes(&prev_acc)
                .map_err(Error::from_pc_err)?;

            // NOTE: As both vk and public input use constant length encoding of field elements,
            // we can simply apply add_bytes to achieve a one-to-one serialization.
            seed_builder
                .add_bytes(&index_pk.0.index_vk)
                .map_err(Error::from_pc_err)?;
            seed_builder
                .add_bytes(&public_input)
                .map_err(Error::from_pc_err)?;

            seed_builder.finalize()
        };
        let mut fs_rng =
            <PC<G1, D> as PolynomialCommitment<G1>>::RandomOracle::from_seed(fs_rng_init_seed);

        /*  First round of the compiled and Fiat-Shamir transformed oracle proof
         */

        let (prover_first_oracles, prover_state) =
            IOP::prover_first_round(prover_init_state, zk, zk_rng).map_err(|e| {
                end_timer!(prover_time);
                e
            })?;

        let first_round_comm_time = start_timer!(|| "Committing to first round polys");
        let (first_comms, first_comm_rands) =
            PC::<G1, D>::commit_vec(pc_pk, prover_first_oracles.iter(), Some(zk_rng))
                .map_err(Error::from_pc_err)?;
        end_timer!(first_round_comm_time);

        // absorb the prove oracles by the Fiat-Shamir rng
        fs_rng.absorb(&to_bytes![first_comms].unwrap());

        let (verifier_first_msg, verifier_state) =
            IOP::verifier_first_round(index_pk.0.index_vk.index_info, &mut fs_rng)?;

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
            PC::<G1, D>::commit_vec(pc_pk, prover_second_oracles.iter(), Some(zk_rng))
                .map_err(Error::from_pc_err)?;
        end_timer!(second_round_comm_time);

        // absorb the prove oracles by the Fiat-Shamir rng
        fs_rng.absorb(&to_bytes![second_comms].unwrap());

        let (verifier_second_msg, verifier_state) =
            IOP::verifier_second_round(verifier_state, &mut fs_rng)?;

        /*  Third round of the compiled and Fiat-Shamir transformed oracle proof
         */

        let prover_third_oracles = IOP::prover_third_round(&verifier_second_msg, prover_state)
            .map_err(|e| {
                end_timer!(prover_time);
                e
            })?;

        let third_round_comm_time = start_timer!(|| "Committing to third round polys");
        let (third_comms, third_comm_rands) =
            PC::<G1, D>::commit_vec(pc_pk, prover_third_oracles.iter(), Some(zk_rng))
                .map_err(Error::from_pc_err)?;
        end_timer!(third_round_comm_time);

        // again, absorb the prove oracles by the Fiat-Shamir rng
        fs_rng.absorb(&to_bytes![third_comms].unwrap());

        /* Preparations before entering the batch evaluation proof
         */

        let verifier_state = IOP::verifier_third_round(verifier_state, &mut fs_rng);

        // Gather prover polynomials in one vector.
        let mut polynomials: Vec<_> = index_pk
            .0
            .index
            .iter()
            .chain(prover_first_oracles.iter())
            .chain(prover_second_oracles.iter())
            .chain(prover_third_oracles.iter())
            .collect();

        // Compute bullet polynomial from the xi_s and we add it to the list of polynomials
        let bullet_poly_coeffs = prev_acc.1[0].xi_s.compute_coeffs();
        let bullet_poly = DensePolynomial::from_coefficients_vec(bullet_poly_coeffs);
        let bullet_poly =
            LabeledPolynomial::new("prev bullet poly".to_string(), bullet_poly, false);
        polynomials.push(&bullet_poly);

        // Gather commitments in one vector.
        #[rustfmt::skip]
        let commitments = vec![
            first_comms.iter().map(|p| p.commitment().clone()).collect(),
            second_comms.iter().map(|p| p.commitment().clone()).collect(),
            third_comms.iter().map(|p| p.commitment().clone()).collect(),
        ];
        let mut labeled_comms: Vec<_> = index_pk
            .0
            .index_vk
            .iter()
            .cloned()
            .zip(&IOP::<G1::ScalarField>::INDEXER_POLYNOMIALS)
            .map(|(c, l)| LabeledCommitment::new(l.to_string(), c))
            .chain(first_comms.iter().cloned())
            .chain(second_comms.iter().cloned())
            .chain(third_comms.iter().cloned())
            .collect();

        // Add g_fin to the labeled commitments
        labeled_comms.push(LabeledCommitment::new(
            "prev bullet poly".to_string(),
            prev_acc.1[0].g_final.clone(),
        ));

        // Gather commitment randomness together.
        let mut comm_rands: Vec<
            LabeledRandomness<<PC<G1, D> as PolynomialCommitment<G1>>::Randomness>,
        > = index_pk
            .0
            .index_comm_rands
            .clone()
            .into_iter()
            .chain(first_comm_rands)
            .chain(second_comm_rands)
            .chain(third_comm_rands)
            .collect();

        // Add g_fin randomness (none because is public)
        comm_rands.push(LabeledRandomness::new(
            "prev bullet poly".to_string(),
            <PC<G1, D> as PolynomialCommitment<G1>>::Randomness::zero(),
        ));

        // Set up the IOP verifier's query set.
        let (mut query_set, verifier_state) = IOP::verifier_query_set(verifier_state)?;

        let gamma = verifier_state.gamma.unwrap();
        query_set.insert(("prev bullet poly".into(), ("gamma".into(), gamma)));

        // Compute the queried values
        let eval_time = start_timer!(|| "Evaluating polynomials over query set");

        let mut evaluations = evaluate_query_set_to_vec(polynomials.clone(), &query_set);

        evaluations.sort_by(|a, b| a.0.cmp(&b.0));
        let evaluations = evaluations
            .into_iter()
            .map(|x| x.1)
            .collect::<Vec<G1::ScalarField>>();
        end_timer!(eval_time);

        // TODO: no need to absorb the evaluation of the bullet poly as the full previous acc is
        // already absorbed.
        fs_rng.absorb(&evaluations);

        /* The non-interactive batch evaluation proof for the polynomial commitment scheme,
        We pass the Fiat-Shamir rng.
        */

        let opening_time = start_timer!(|| "Compute opening proof");

        // Saving the rng state for later recomputing the challenges
        let fs_rng_state = fs_rng.get_state().clone();

        // TODO: the evaluation of the bullet poly does not need to be part of the proof.
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

        let verifier_state = PC::<G1, D>::batch_succinct_verify(
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

        let new_acc = DualDLogItem::<G1, G2>(
            // TODO: Opening proof doesn't contain the xi_s, we need to recompute them.
            //       Can we refactor and do better ?
            vec![DLogItem {
                g_final: GroupVec::new(vec![verifier_state[0].final_comm_key]),
                xi_s: verifier_state[0].check_poly.clone(),
            }],
            prev_acc.0.clone(),
        );

        let proof = DLogAccMarlinProof::<G1, D>::new(commitments, evaluations, pc_proof);

        end_timer!(prover_time);

        proof.print_size_info();
        Ok((proof, new_acc))
    }

    // The Fiat-Shamir verifier for the algebraic oracle proof of Coboundary Marlin,
    // without verifying the subsequent batch evaluation proof.
    // Does all the algebraic checks on the claimed values in a proof, and returns
    //     - the commitments, query set and evaluation claims, as well as
    //     - the Fiat-Shamir rng,
    // as needed for the remaining verification of the dlog opening proof.
    fn verify_iop<'a>(
        pc_vk: &<PC<G1, D> as PolynomialCommitment<G1>>::VerifierKey,
        index_vk: &DLogAccMarlinVerifierKey<G1, D>,
        public_input: &[G1::ScalarField],
        proof: &DLogAccMarlinProof<G1, D>,
        acc: &DualDLogItem<G2, G1>,
    ) -> Result<
        (
            QuerySet<'a, G1::ScalarField>,
            Evaluations<'a, G1::ScalarField>,
            Vec<LabeledCommitment<<PC<G1, D> as PolynomialCommitment<G1>>::Commitment>>,
            <PC<G1, D> as PolynomialCommitment<G1>>::RandomOracle,
        ),
        Error<<PC<G1, D> as PolynomialCommitment<G1>>::Error>,
    > {
        let iop_verification_time = start_timer!(|| "Verify Sumcheck equations");

        let public_input = public_input.to_vec();

        let fs_rng_init_seed = {
            let mut seed_builder =
                <<PC<G1, D> as PolynomialCommitment<G1>>::RandomOracle as FiatShamirRng>::Seed::new(
                );
            seed_builder
                .add_bytes(&Self::PROTOCOL_NAME)
                .map_err(Error::from_pc_err)?;
            seed_builder
                .add_bytes(&pc_vk.get_hash())
                .map_err(Error::from_pc_err)?;
            seed_builder.add_bytes(&acc).map_err(Error::from_pc_err)?;
            // TODO: Shall we decompose this further when passing it to the seed builder ?
            seed_builder
                .add_bytes(&index_vk.0)
                .map_err(Error::from_pc_err)?;
            // TODO: Shall we decompose this further when passing it to the seed builder ?
            seed_builder
                .add_bytes(&public_input)
                .map_err(Error::from_pc_err)?;
            seed_builder.finalize()
        };
        let mut fs_rng =
            <PC<G1, D> as PolynomialCommitment<G1>>::RandomOracle::from_seed(fs_rng_init_seed);

        /*  First round of the compiled and Fiat-Shamir transformed oracle proof
         */
        let first_comms = &proof.0.commitments[0];
        fs_rng.absorb(&to_bytes![first_comms].unwrap());

        let (_, verifier_state) = IOP::verifier_first_round(index_vk.0.index_info, &mut fs_rng)?;

        /*  Second round of the compiled and Fiat-Shamir transformed oracle proof-
        The verification of the outer sumcheck equation is postponed to below
        */
        let second_comms = &proof.0.commitments[1];
        fs_rng.absorb(&to_bytes![second_comms].unwrap());

        let (_, verifier_state) = IOP::verifier_second_round(verifier_state, &mut fs_rng)?;

        /*  Third round of the compiled and Fiat-Shamir transformed oracle proof
        The verification of the inner sumcheck equation is postponed to below
        */

        let third_comms = &proof.0.commitments[2];
        fs_rng.absorb(&to_bytes![third_comms].unwrap());

        let verifier_state = IOP::verifier_third_round(verifier_state, &mut fs_rng);

        // Gather commitments in one vector.
        let mut commitments: Vec<_> = index_vk
            .0
            .iter()
            .chain(first_comms)
            .chain(second_comms)
            .chain(third_comms)
            .cloned()
            .zip(IOP::<G1::ScalarField>::polynomial_labels())
            .map(|(c, l)| LabeledCommitment::new(l, c))
            .collect();

        // Add g_fin to the labeled commitments
        commitments.push(LabeledCommitment::new(
            "prev bullet poly".to_string(),
            acc.1[0].g_final.clone(),
        ));

        // Check sumchecks equations
        let (mut query_set, verifier_state) = IOP::verifier_query_set(verifier_state)?;

        let gamma = verifier_state.gamma.unwrap();
        query_set.insert(("prev bullet poly".into(), ("gamma".into(), gamma)));

        let mut evaluations = Evaluations::new();
        let mut evaluation_labels = Vec::new();
        for (poly_label, (point_label, point)) in query_set.iter().cloned() {
            evaluation_labels.push(((poly_label, point_label), point));
        }

        evaluation_labels.sort_by(|a, b| a.0.cmp(&b.0));
        for (q, eval) in evaluation_labels.into_iter().zip(&proof.0.evaluations) {
            evaluations.insert(((q.0).0, q.1), *eval);
        }

        let result = IOP::verify_sumchecks(&public_input, &evaluations, &verifier_state);

        if result.is_err() {
            end_timer!(iop_verification_time);
            return Err(Error::IOPError(result.unwrap_err()));
        }

        end_timer!(iop_verification_time);

        Ok((query_set, evaluations, commitments, fs_rng))
    }

    /// Perform the succinct verification of a proof as produced by `fn prove()`.
    /// If successful, return the succinct-check polynomial and final comm key of the opening proof.
    pub fn succinct_verify(
        pc_vk: &<PC<G1, D> as PolynomialCommitment<G1>>::VerifierKey,
        index_vk: &DLogAccMarlinVerifierKey<G1, D>,
        public_input: &[G1::ScalarField],
        proof: &DLogAccMarlinProof<G1, D>,
        prev_acc: &DualDLogItem<G2, G1>,
        curr_acc: &DualDLogItem<G1, G2>,
    ) -> Result<Option<VerifierState<G1>>, Error<<PC<G1, D> as PolynomialCommitment<G1>>::Error>>
    {
        let verifier_time = start_timer!(|| "Marlin Verifier");

        // The Fiat-Shamir verifier  for the algebraic oracle proof part.
        let iop_result = Self::verify_iop(pc_vk, index_vk, &public_input, proof, prev_acc);

        if iop_result.is_err() {
            end_timer!(verifier_time);
            eprintln!("IOP Verification failed: {:?}", iop_result.err());
            return Ok(None);
        }

        let (query_set, evaluations, commitments, mut fs_rng) = iop_result.unwrap();

        fs_rng.absorb(&proof.0.evaluations);

        // Perform succinct verification of opening proof
        let result =
            <PC<G1, D> as PolynomialCommitment<G1>>::succinct_multi_point_multi_poly_verify(
                pc_vk,
                &commitments,
                &query_set,
                &evaluations,
                &proof.0.pc_proof,
                &mut fs_rng,
            );

        if result.is_err() {
            end_timer!(verifier_time);
            eprintln!("Opening proof Verification failed: {:?}", result.err());
            return Ok(None);
        }

        let opening_result = result.unwrap();
        if opening_result.is_none() {
            return Ok(None);
        }

        let opening_result = opening_result.unwrap();
        let check_poly = &opening_result.check_poly;
        let final_comm_key = opening_result.final_comm_key;

        if check_poly != &curr_acc.0[0].xi_s
            || final_comm_key != curr_acc.0[0].g_final[0]
            || curr_acc.1[0] != prev_acc.0[0]
        {
            return Ok(None);
        }

        end_timer!(verifier_time);
        Ok(Some(opening_result))
    }

    /// Perform the non-succinct part of the verification of a proof as produced by `fn prove()`.
    /// Requires in input the two verifier states produced by previous calls to `succinct_verify()`.
    pub fn hard_verify(
        pc_vk_g1: &<PC<G1, D> as PolynomialCommitment<G1>>::VerifierKey,
        pc_vk_g2: &<PC<G2, D> as PolynomialCommitment<G2>>::VerifierKey,
        verifier_state_g1: &<PC<G1, D> as PolynomialCommitment<G1>>::VerifierState,
        verifier_state_g2: &<PC<G2, D> as PolynomialCommitment<G2>>::VerifierState,
    ) -> Result<bool, Error<poly_commit::Error>> {
        let check_g1 =
            <PC<G1, D> as PolynomialCommitment<G1>>::hard_verify(pc_vk_g1, verifier_state_g1)
                .map_err(Error::from_pc_err)?;
        let check_g2 =
            <PC<G2, D> as PolynomialCommitment<G2>>::hard_verify(pc_vk_g2, verifier_state_g2)
                .map_err(Error::from_pc_err)?;
        Ok(check_g1.is_some() && check_g2.is_some())
    }

    /// Perform the full verification of a proof as produced by `fn prove()`.
    pub fn verify(
        pc_vk_g1: &<PC<G1, D> as PolynomialCommitment<G1>>::VerifierKey,
        pc_vk_g2: &<PC<G2, D> as PolynomialCommitment<G2>>::VerifierKey,
        index_vk: &DLogAccMarlinVerifierKey<G1, D>,
        public_input: &[G1::ScalarField],
        proof: &DLogAccMarlinProof<G1, D>,
        prev_acc: &DualDLogItem<G2, G1>,
        curr_acc: &DualDLogItem<G1, G2>,
    ) -> Result<bool, Error<<PC<G1, D> as PolynomialCommitment<G1>>::Error>> {
        let verifier_state_g1 =
            Self::succinct_verify(pc_vk_g1, index_vk, public_input, proof, prev_acc, curr_acc)?;
        if verifier_state_g1.is_none() {
            return Ok(false);
        }
        let verifier_state_g1 = verifier_state_g1.unwrap();
        let verifier_state_g2 = VerifierState {
            check_poly: curr_acc.1[0].xi_s.clone(),
            final_comm_key: curr_acc.1[0].g_final[0],
        };
        Self::hard_verify(pc_vk_g1, pc_vk_g2, &verifier_state_g1, &verifier_state_g2)
    }
}

#[cfg(test)]
mod test {
    use std::ops::{MulAssign, SubAssign};

    use blake2::Blake2s;
    use digest::Digest;
    use rand::{thread_rng, RngCore};

    use algebra::curves::tweedle::{
        dee::DeeJacobian as TweedleDee, dum::DumJacobian as TweedleDum,
    };
    use algebra::{
        serialize::test_canonical_serialize_deserialize, Curve, Group, SemanticallyValid,
        UniformRand,
    };
    use marlin::Error;
    use poly_commit::{
        ipa_pc::InnerProductArgPC, PCCommitterKey, PCParameters, PolynomialCommitment,
    };
    use r1cs_core::ToConstraintField;

    use crate::darlin::accumulators::dlog::DualDLogItem;
    use crate::darlin::data_structures::FinalDarlinDeferredData;
    use crate::darlin::dlog_acc_marlin::DLogAccMarlin;
    use crate::darlin::tests::final_darlin::TestCircuit;

    fn generate_circuit<G1, G2>(
        num_constraints: usize,
        num_variables: usize,
        c_prev: G1::ScalarField,
        d_prev: G1::ScalarField,
        deferred: &FinalDarlinDeferredData<G1, G2>,
        is_satisfied: bool,
        rng: &mut dyn RngCore,
    ) -> TestCircuit<G1, G2>
    where
        G1: Curve<BaseField = <G2 as Group>::ScalarField>
            + ToConstraintField<<G2 as Group>::ScalarField>,
        G2: Curve<BaseField = <G1 as Group>::ScalarField>
            + ToConstraintField<<G1 as Group>::ScalarField>,
    {
        let a = G1::ScalarField::rand(rng);
        let b = G1::ScalarField::rand(rng);
        let c = {
            if is_satisfied {
                let mut c = a;
                c.mul_assign(&b);
                c.sub_assign(&c_prev);
                c
            } else {
                G1::ScalarField::rand(rng)
            }
        };
        let d = {
            if is_satisfied {
                let mut d = c;
                d.mul_assign(&b);
                d.sub_assign(&d_prev);
                d
            } else {
                G1::ScalarField::rand(rng)
            }
        };

        let circ = TestCircuit {
            a: Some(a),
            b: Some(b),
            c_prev: Some(c_prev),
            d_prev: Some(d_prev),
            c: Some(c),
            d: Some(d),
            deferred: deferred.clone(),
            num_constraints,
            num_variables,
        };
        circ
    }

    fn test_circuit<G1, G2, D>(
        num_samples: usize,
        num_constraints: usize,
        num_variables: usize,
        zk: bool,
    ) where
        G1: Curve<BaseField = <G2 as Group>::ScalarField>
            + ToConstraintField<<G2 as Group>::ScalarField>,
        G2: Curve<BaseField = <G1 as Group>::ScalarField>
            + ToConstraintField<<G1 as Group>::ScalarField>,
        D: Digest + 'static,
    {
        let rng = &mut thread_rng();

        let universal_srs_g1 = InnerProductArgPC::<G1, D>::setup(num_constraints - 1).unwrap();
        let (pc_pk_g1, pc_vk_g1) = universal_srs_g1.trim((num_constraints - 1) / 2).unwrap();
        assert_eq!(pc_pk_g1.get_hash(), universal_srs_g1.get_hash());
        assert_eq!(pc_vk_g1.get_hash(), universal_srs_g1.get_hash());

        let universal_srs_g2 = InnerProductArgPC::<G2, D>::setup(num_constraints - 1).unwrap();
        let (pc_pk_g2, pc_vk_g2) = universal_srs_g2.trim((num_constraints - 1) / 2).unwrap();
        assert_eq!(pc_pk_g2.get_hash(), universal_srs_g2.get_hash());
        assert_eq!(pc_vk_g2.get_hash(), universal_srs_g2.get_hash());

        let universal_srs_g1_fake =
            InnerProductArgPC::<G1, D>::setup_from_seed(num_constraints - 1, b"FAKE PROTOCOL")
                .unwrap();
        let (pc_pk_g1_fake, _) = universal_srs_g1_fake
            .trim((num_constraints - 1) / 2)
            .unwrap();

        let universal_srs_g2_fake =
            InnerProductArgPC::<G2, D>::setup_from_seed(num_constraints - 1, b"FAKE PROTOCOL")
                .unwrap();
        let (pc_pk_g2_fake, _) = universal_srs_g2_fake
            .trim((num_constraints - 1) / 2)
            .unwrap();

        for _ in 0..num_samples {
            /*  Generate both valid and invalid dual dlog accumulators for testing purposes.
             */
            let deferred_a = FinalDarlinDeferredData::<G1, G2>::generate_random::<_, D>(
                rng, &pc_pk_g1, &pc_pk_g2,
            );
            let deferred_b = FinalDarlinDeferredData::<G1, G2>::generate_random::<_, D>(
                rng, &pc_pk_g1, &pc_pk_g2,
            );

            let deferred_good = deferred_a.clone();
            let acc_good = DualDLogItem(
                vec![deferred_a.previous_acc],
                vec![deferred_a.pre_previous_acc],
            );

            let mut deferred_bad_previous = deferred_good.clone();
            deferred_bad_previous.previous_acc.g_final = deferred_b.previous_acc.g_final.clone();
            let acc_bad_previous = DualDLogItem(
                vec![deferred_bad_previous.previous_acc],
                vec![deferred_bad_previous.pre_previous_acc],
            );

            let mut deferred_bad_pre_previous = deferred_good.clone();
            deferred_bad_pre_previous.previous_acc.g_final =
                deferred_b.previous_acc.g_final.clone();
            let acc_bad_pre_previous = DualDLogItem(
                vec![deferred_bad_pre_previous.previous_acc],
                vec![deferred_bad_pre_previous.pre_previous_acc],
            );

            let mut deferred_bad = deferred_good.clone();
            deferred_bad.previous_acc.g_final = deferred_b.previous_acc.g_final.clone();
            deferred_bad.pre_previous_acc.g_final = deferred_b.pre_previous_acc.g_final.clone();
            let acc_bad = DualDLogItem(
                vec![deferred_bad.previous_acc],
                vec![deferred_bad.pre_previous_acc],
            );

            let c_prev = G1::ScalarField::rand(rng);
            let d_prev = G1::ScalarField::rand(rng);

            let circ_satisfied = generate_circuit::<G1, G2>(
                num_constraints,
                num_variables,
                c_prev,
                d_prev,
                &deferred_good,
                true,
                rng,
            );

            let circ_unsatisfied = generate_circuit::<G1, G2>(
                num_constraints,
                num_variables,
                c_prev,
                d_prev,
                &deferred_good,
                false,
                rng,
            );

            let (index_pk, index_vk) = DLogAccMarlin::<G1, G2, D>::circuit_specific_setup(
                &pc_pk_g1,
                circ_satisfied.clone(),
            )
            .unwrap();

            assert!(index_pk.is_valid());
            assert!(index_vk.is_valid());

            println!("Called index");

            test_canonical_serialize_deserialize(true, &index_pk);
            test_canonical_serialize_deserialize(true, &index_vk);

            let proof = DLogAccMarlin::<G1, G2, D>::prove(
                &index_pk,
                &pc_pk_g1,
                circ_satisfied.clone(),
                &acc_good,
                zk,
                if zk { Some(rng) } else { None },
            );

            assert!(proof.is_ok());

            let (proof, acc_new) = proof.unwrap();

            assert!(proof.is_valid());

            println!("Called prover");

            test_canonical_serialize_deserialize(true, &proof);

            // Success verification
            let mut public_inputs = circ_satisfied.deferred.to_field_elements().unwrap();
            public_inputs
                .extend_from_slice(&[circ_satisfied.c.unwrap(), circ_satisfied.d.unwrap()]);
            assert!(DLogAccMarlin::<G1, G2, D>::verify(
                &pc_vk_g1,
                &pc_vk_g2,
                &index_vk,
                &public_inputs,
                &proof,
                &acc_good,
                &acc_new
            )
            .unwrap());

            // Fail verification: wrong public inputs.
            let mut wrong_public_inputs = circ_satisfied.deferred.to_field_elements().unwrap();
            wrong_public_inputs
                .extend_from_slice(&[circ_satisfied.c.unwrap(), circ_satisfied.c.unwrap()]);
            assert!(!DLogAccMarlin::<G1, G2, D>::verify(
                &pc_vk_g1,
                &pc_vk_g2,
                &index_vk,
                &wrong_public_inputs,
                &proof,
                &acc_good,
                &acc_new
            )
            .unwrap());

            // Fail verification: bad previous non-native dlog accumulator.
            assert!(!DLogAccMarlin::<G1, G2, D>::verify(
                &pc_vk_g1,
                &pc_vk_g2,
                &index_vk,
                &public_inputs,
                &proof,
                &acc_bad_previous,
                &acc_new
            )
            .unwrap());

            // Fail verification: bad previous native dlog accumulator.
            assert!(!DLogAccMarlin::<G1, G2, D>::verify(
                &pc_vk_g1,
                &pc_vk_g2,
                &index_vk,
                &public_inputs,
                &proof,
                &acc_bad_pre_previous,
                &acc_new
            )
            .unwrap());

            // Fail verification: bad previous dlog accumulator (both native and non-native).
            assert!(!DLogAccMarlin::<G1, G2, D>::verify(
                &pc_vk_g1,
                &pc_vk_g2,
                &index_vk,
                &public_inputs,
                &proof,
                &acc_bad,
                &acc_new
            )
            .unwrap());

            // Fail verification: generate fake proof with fake polynomial committer keys.
            let deferred_fake = FinalDarlinDeferredData::<G1, G2>::generate_random::<_, D>(
                rng,
                &pc_pk_g1_fake,
                &pc_pk_g2_fake,
            );
            let acc_fake = DualDLogItem(
                vec![deferred_fake.previous_acc],
                vec![deferred_fake.pre_previous_acc],
            );
            let (index_pk_fake, index_vk_fake) =
                DLogAccMarlin::<G1, G2, D>::circuit_specific_setup(
                    &pc_pk_g1_fake,
                    circ_satisfied.clone(),
                )
                .unwrap();
            let result = DLogAccMarlin::<G1, G2, D>::prove(
                &index_pk_fake,
                &pc_pk_g1_fake,
                circ_satisfied.clone(),
                &acc_fake,
                zk,
                if zk { Some(rng) } else { None },
            );
            let (proof_fake, acc_new_fake) = result.unwrap();
            assert!(!DLogAccMarlin::<G1, G2, D>::verify(
                &pc_vk_g1,
                &pc_vk_g2,
                &index_vk_fake,
                &public_inputs,
                &proof_fake,
                &acc_fake,
                &acc_new_fake
            )
            .unwrap());

            // Fail proof creation when witness assignment doesn't satisfy the circuit and check
            // correct error assertion.
            let proof = DLogAccMarlin::<G1, G2, D>::prove(
                &index_pk,
                &pc_pk_g1,
                circ_unsatisfied.clone(),
                &acc_good,
                zk,
                if zk { Some(rng) } else { None },
            );
            assert!(proof.is_err());
            assert!(match proof.unwrap_err() {
                Error::IOPError(marlin::iop::Error::InvalidCoboundaryPolynomial) => true,
                _ => false,
            });
        }
    }

    // Fails with error 'attempt to subtract with overflow'.
    #[test]
    #[ignore]
    fn prove_and_verify_with_tall_matrix() {
        let num_constraints = 100;
        let num_variables = 50;

        test_circuit::<TweedleDee, TweedleDum, Blake2s>(25, num_constraints, num_variables, false);
        println!("DLogAccMarlin No ZK passed");

        test_circuit::<TweedleDee, TweedleDum, Blake2s>(25, num_constraints, num_variables, true);
        println!("DLogAccMarlin ZK passed");
    }

    #[test]
    fn prove_and_verify_with_squat_matrix() {
        let num_constraints = 50;
        let num_variables = 100;

        test_circuit::<TweedleDee, TweedleDum, Blake2s>(25, num_constraints, num_variables, false);
        println!("DLogAccMarlin No ZK passed");

        test_circuit::<TweedleDee, TweedleDum, Blake2s>(25, num_constraints, num_variables, true);
        println!("DLogAccMarlin ZK passed");
    }

    #[test]
    fn prove_and_verify_with_square_matrix() {
        let num_constraints = 100;
        let num_variables = 100;

        test_circuit::<TweedleDee, TweedleDum, Blake2s>(25, num_constraints, num_variables, false);
        println!("DLogAccMarlin No ZK passed");

        test_circuit::<TweedleDee, TweedleDum, Blake2s>(25, num_constraints, num_variables, true);
        println!("DLogAccMarlin ZK passed");
    }
}
