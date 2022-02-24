use crate::{
    Error as PolyError, Evaluations, LabeledCommitmentGadget, LabeledPolynomial, PCParameters,
    Polynomial, PolynomialCommitment, PolynomialCommitmentVerifierGadget, QueryMap,
};
use algebra::{EndoMulCurve, PrimeField, SemanticallyValid, UniformRand};
use blake2::Blake2s;
use fiat_shamir::constraints::FiatShamirRngGadget;
use fiat_shamir::FiatShamirRng;
use r1cs_core::{
    ConstraintSystem, ConstraintSystemAbstract, ConstraintSystemDebugger, SynthesisMode,
};
use r1cs_std::alloc::AllocGadget;
use r1cs_std::fields::nonnative::nonnative_field_gadget::NonNativeFieldGadget;
use r1cs_std::groups::EndoMulCurveGadget;
use rand::{thread_rng, Rng};

#[derive(Copy, Clone, Default)]
struct TestInfo {
    /// number of random instances to be tested
    num_iters: usize,
    /// The degree bound for sampling the supported degree of
    /// the non-extended scheme.
    max_degree: Option<usize>,
    /// The optional maximum degree supported by the non-extended scheme
    /// (i.e. the "segment size")
    supported_degree: Option<usize>,
    /// The number of polynomials
    num_polynomials: usize,
    /// the number of query points
    max_num_queries: usize,
}

pub(crate) fn test_succinct_verify_template<
    ConstraintF: PrimeField,
    G: EndoMulCurve<BaseField = ConstraintF>,
    GG: EndoMulCurveGadget<G, ConstraintF>,
    PC: PolynomialCommitment<G>,
    PCG: PolynomialCommitmentVerifierGadget<ConstraintF, G, GG, PC>,
>() -> Result<(), PCG::Error> {
    let rng = &mut thread_rng();
    const NUM_RUNS: usize = 10;
    for _ in 0..NUM_RUNS {
        let max_degree: usize = rng.gen_range(1..=256);
        let supported_degree: usize = rng.gen_range(1..=max_degree);
        assert!(supported_degree <= max_degree);

        let pp = PC::setup::<Blake2s>(max_degree)?;
        let (ck, vk) = pp.trim(supported_degree)?;
        let poly_degree: usize = rng.gen_range(0..=supported_degree);

        let polynomial = Polynomial::rand(poly_degree, rng);
        let is_hiding: bool = rng.gen();

        let (commitment, randomness) = PC::commit(&ck, &polynomial, is_hiding, Some(rng))?;

        let point = G::ScalarField::rand(rng);
        let value = polynomial.evaluate(point);
        let fs_seed = String::from("TEST_SEED").into_bytes();
        let mut fs_rng =
            PC::RandomOracle::from_seed(fs_seed.clone()).map_err(|err| PolyError::from(err))?;
        let proof = PC::open(
            &ck,
            polynomial,
            point,
            is_hiding,
            randomness,
            &mut fs_rng,
            Some(rng),
        )?;
        // check that verify with primitive succeeds
        let mut fs_rng =
            PC::RandomOracle::from_seed(fs_seed.clone()).map_err(|err| PolyError::from(err))?;
        let v_state = PC::succinct_verify(&vk, &commitment, point, value, &proof, &mut fs_rng)?;
        if v_state.is_none() {
            Err(PolyError::FailedSuccinctCheck)?
        }
        let mut cs = ConstraintSystem::<ConstraintF>::new(SynthesisMode::Debug);
        let vk_gadget = PCG::VerifierKey::alloc(cs.ns(|| "alloc verifier key"), || Ok(vk))?;
        let commitment_gadget =
            PCG::Commitment::alloc(cs.ns(|| "alloc commitment"), || Ok(commitment))?;

        let point_gadget = NonNativeFieldGadget::<G::ScalarField, ConstraintF>::alloc(
            cs.ns(|| "alloc evaluation point"),
            || Ok(point),
        )?;
        let value_gadget = NonNativeFieldGadget::<G::ScalarField, ConstraintF>::alloc(
            cs.ns(|| "alloc polynomial evaluation on point"),
            || Ok(value),
        )?;
        let proof_gadget = PCG::Proof::alloc(cs.ns(|| "alloc opening proof"), || Ok(proof))?;
        let mut fs_gadget = PCG::RandomOracle::init_from_seed(cs.ns(|| "init fs oracle"), fs_seed)?;
        let _v_state_gadget = PCG::succinct_verify(
            cs.ns(|| "succinct-verify"),
            &vk_gadget,
            &commitment_gadget,
            &point_gadget,
            &value_gadget,
            &proof_gadget,
            &mut fs_gadget,
        )?;
        println!("poly degree: {}, is_hiding: {}", poly_degree, is_hiding);
        if !cs.is_satisfied() {
            println!("{:?}", cs.which_is_unsatisfied());
        }
        assert!(cs.is_satisfied());
    }
    Ok(())
}

fn test_multi_point_multi_poly_verify<
    ConstraintF: PrimeField,
    G: EndoMulCurve<BaseField = ConstraintF>,
    GG: EndoMulCurveGadget<G, ConstraintF>,
    PC: PolynomialCommitment<G>,
    PCG: PolynomialCommitmentVerifierGadget<ConstraintF, G, GG, PC>,
>(
    test_conf: TestInfo,
) -> Result<(), PCG::Error> {
    let rng = &mut thread_rng();
    for _ in 0..test_conf.num_iters {
        let mut cs = ConstraintSystem::<ConstraintF>::new(SynthesisMode::Debug);
        let max_degree = test_conf.max_degree.unwrap_or(rng.gen_range(1..=256));
        let supported_degree = test_conf
            .supported_degree
            .unwrap_or(rng.gen_range(1..=max_degree));
        assert!(supported_degree <= max_degree);

        let max_num_polynomials = test_conf.num_polynomials;
        let num_polynomials = rng.gen_range(1..=max_num_polynomials);
        let max_num_points = test_conf.max_num_queries;
        let num_points = rng.gen_range(1..=max_num_points);

        let mut polynomials = Vec::with_capacity(num_polynomials);
        let mut labels = Vec::with_capacity(num_polynomials);
        for i in 0..num_polynomials {
            let label = format!("Test polynomial {}", i);
            labels.push(label.clone());

            let poly_degree: usize = rng.gen_range(0..=supported_degree);
            let polynomial = Polynomial::rand(poly_degree, rng);

            let is_hiding: bool = rng.gen();

            polynomials.push(LabeledPolynomial::new(label, polynomial, is_hiding));
        }

        let pp = PC::setup::<Blake2s>(max_degree)?;
        let (ck, vk) = pp.trim(supported_degree)?;
        let (comms, rands) = PC::commit_vec(&ck, &polynomials, Some(rng))?;

        assert!(comms.is_valid());
        let mut points = QueryMap::new();
        let mut point_gadgets = QueryMap::new();
        let mut values = Evaluations::new();
        let mut value_gadgets = Evaluations::new();
        for i in 0..num_points {
            let point_label = format!("point label {}", i);
            let point = G::ScalarField::rand(rng);
            let point_gadget = NonNativeFieldGadget::<G::ScalarField, ConstraintF>::alloc(
                cs.ns(|| format!("alloc gadget for point {}", i)),
                || Ok(point),
            )?;
            for (j, labeled_poly) in polynomials.iter().enumerate() {
                let label = labeled_poly.label();
                let poly = labeled_poly.polynomial();
                let value = poly.evaluate(point);
                let value_gadget = NonNativeFieldGadget::<G::ScalarField, ConstraintF>::alloc(
                    cs.ns(|| {
                        format!(
                            "alloc gadget for evaluation of point  {} over poly {}",
                            i, j
                        )
                    }),
                    || Ok(value),
                )?;
                points.insert((label.clone(), point_label.clone()), point);
                point_gadgets.insert((label.clone(), point_label.clone()), point_gadget.clone());
                values.insert((label.clone(), point_label.clone()), value);
                value_gadgets.insert((label.clone(), point_label.clone()), value_gadget);
            }
        }

        let fs_seed = String::from("TEST_SEED").into_bytes();
        let mut fs_rng =
            PC::RandomOracle::from_seed(fs_seed.clone()).map_err(|err| PolyError::from(err))?;
        let proof = PC::multi_point_multi_poly_open(
            &ck,
            &polynomials,
            &comms,
            &points,
            &mut fs_rng,
            &rands,
            Some(rng),
        )?;

        let mut fs_rng =
            PC::RandomOracle::from_seed(fs_seed.clone()).map_err(|err| PolyError::from(err))?;
        let v_state = PC::succinct_multi_point_multi_poly_verify(
            &vk,
            &comms,
            &points,
            &values,
            &proof,
            &mut fs_rng,
        )?;
        assert!(v_state.is_some());

        let vk_gadget = PCG::VerifierKey::alloc(cs.ns(|| "alloc verifier key"), || Ok(vk))?;
        let mut labeled_comms = Vec::with_capacity(comms.len());
        for comm in comms {
            let label = comm.label();
            let comm_gadget = PCG::Commitment::alloc(
                cs.ns(|| format!("alloc commitment with label {}", label)),
                || Ok(comm.commitment().clone()),
            )?;
            labeled_comms.push(LabeledCommitmentGadget::new(label.clone(), comm_gadget));
        }
        let proof_gadget =
            PCG::MultiPointProof::alloc(cs.ns(|| "alloc proof gadget"), || Ok(proof))?;
        let mut fs_gadget = PCG::RandomOracle::init_from_seed(cs.ns(|| "init fs oracle"), fs_seed)?;
        let _v_state = PCG::succinct_verify_multi_poly_multi_point(
            cs.ns(|| "verify proof"),
            &vk_gadget,
            labeled_comms.as_slice(),
            &point_gadgets,
            &value_gadgets,
            &proof_gadget,
            &mut fs_gadget,
        )?;
        if !cs.is_satisfied() {
            println!("{:?}", cs.which_is_unsatisfied());
        }
        assert!(cs.is_satisfied());
    }

    Ok(())
}

pub(crate) fn test_single_point_multi_poly_verify<
    ConstraintF: PrimeField,
    G: EndoMulCurve<BaseField = ConstraintF>,
    GG: EndoMulCurveGadget<G, ConstraintF>,
    PC: PolynomialCommitment<G>,
    PCG: PolynomialCommitmentVerifierGadget<ConstraintF, G, GG, PC>,
>() -> Result<(), PCG::Error> {
    let rng = &mut thread_rng();
    const NUM_RUNS: usize = 10;
    for _ in 0..NUM_RUNS {
        let max_degree: usize = rng.gen_range(1..=256);
        let supported_degree: usize = rng.gen_range(1..=max_degree);
        assert!(supported_degree <= max_degree);

        let max_num_polynomials = 4;
        let num_polynomials = rng.gen_range(1..=max_num_polynomials);

        let mut polynomials = Vec::with_capacity(num_polynomials);
        let mut labels = Vec::with_capacity(num_polynomials);
        let mut values = Vec::with_capacity(num_polynomials);
        let point = G::ScalarField::rand(rng);
        for i in 0..num_polynomials {
            let label = format!("Test polynomial {}", i);
            labels.push(label.clone());

            let poly_degree: usize = rng.gen_range(0..=supported_degree);
            let polynomial = Polynomial::rand(poly_degree, rng);

            let is_hiding: bool = rng.gen();
            values.push(polynomial.evaluate(point));
            polynomials.push(LabeledPolynomial::new(label, polynomial, is_hiding));
        }

        let pp = PC::setup::<Blake2s>(max_degree)?;
        let (ck, vk) = pp.trim(supported_degree)?;
        let (comms, rands) = PC::commit_vec(&ck, &polynomials, Some(rng))?;

        // alloc gadgets for polynomial evaluations over the point here as later on they will be moved in succinct verify function
        let mut cs = ConstraintSystem::<ConstraintF>::new(SynthesisMode::Debug);
        let mut value_gadgets = Vec::with_capacity(values.len());
        for (i, value) in values.iter().enumerate() {
            let value_gadget = NonNativeFieldGadget::<G::ScalarField, ConstraintF>::alloc(
                cs.ns(|| format!("alloc value for poly {}", i)),
                || Ok(value.clone()),
            )?;
            value_gadgets.push(value_gadget);
        }

        let fs_seed = String::from("TEST_SEED").into_bytes();
        let mut fs_rng =
            PC::RandomOracle::from_seed(fs_seed.clone()).map_err(|err| PolyError::from(err))?;
        let proof = PC::single_point_multi_poly_open(
            &ck,
            &polynomials,
            &comms,
            point,
            &mut fs_rng,
            &rands,
            Some(rng),
        )?;
        let mut fs_rng =
            PC::RandomOracle::from_seed(fs_seed.clone()).map_err(|err| PolyError::from(err))?;
        let v_state = PC::succinct_single_point_multi_poly_verify(
            &vk,
            &comms,
            point,
            values,
            &proof,
            &mut fs_rng,
        )?;
        if v_state.is_none() {
            Err(PolyError::FailedSuccinctCheck)?
        }

        let vk_gadget = PCG::VerifierKey::alloc(cs.ns(|| "alloc verifier key"), || Ok(vk))?;
        let mut labeled_comms = Vec::with_capacity(comms.len());
        for comm in comms {
            let label = comm.label();
            let comm_gadget = PCG::Commitment::alloc(
                cs.ns(|| format!("alloc commitment with label {}", label)),
                || Ok(comm.commitment().clone()),
            )?;
            labeled_comms.push(LabeledCommitmentGadget::new(label.clone(), comm_gadget));
        }
        let proof_gadget = PCG::Proof::alloc(cs.ns(|| "alloc proof"), || Ok(proof))?;
        let point_gadget = NonNativeFieldGadget::<G::ScalarField, ConstraintF>::alloc(
            cs.ns(|| "alloc point"),
            || Ok(point),
        )?;

        let mut fs_gadget = PCG::RandomOracle::init_from_seed(cs.ns(|| "init fs oracle"), fs_seed)?;
        let _v_state_gadget = PCG::succinct_verify_single_point_multi_poly(
            cs.ns(|| "verify proof"),
            &vk_gadget,
            &labeled_comms,
            &point_gadget,
            &value_gadgets,
            &proof_gadget,
            &mut fs_gadget,
        )?;
        if !cs.is_satisfied() {
            println!("{:?}", cs.which_is_unsatisfied());
        }
        assert!(cs.is_satisfied());
    }

    Ok(())
}

pub(crate) fn multi_poly_multi_point_test<
    ConstraintF: PrimeField,
    G: EndoMulCurve<BaseField = ConstraintF>,
    GG: EndoMulCurveGadget<G, ConstraintF>,
    PC: PolynomialCommitment<G>,
    PCG: PolynomialCommitmentVerifierGadget<ConstraintF, G, GG, PC>,
>() -> Result<(), PCG::Error> {
    test_multi_point_multi_poly_verify::<ConstraintF, G, GG, PC, PCG>(TestInfo {
        num_iters: 5,
        max_degree: None,
        supported_degree: None,
        num_polynomials: 5,
        max_num_queries: 5,
    })
}

pub(crate) fn single_poly_multi_point_test<
    ConstraintF: PrimeField,
    G: EndoMulCurve<BaseField = ConstraintF>,
    GG: EndoMulCurveGadget<G, ConstraintF>,
    PC: PolynomialCommitment<G>,
    PCG: PolynomialCommitmentVerifierGadget<ConstraintF, G, GG, PC>,
>() -> Result<(), PCG::Error> {
    test_multi_point_multi_poly_verify::<ConstraintF, G, GG, PC, PCG>(TestInfo {
        num_iters: 5,
        max_degree: None,
        supported_degree: None,
        num_polynomials: 1,
        max_num_queries: 5,
    })
}
