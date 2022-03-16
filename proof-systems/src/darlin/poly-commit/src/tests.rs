//! Unit tests for linear polynomial commitment schemes and their domain extension.
use crate::*;
use algebra::{serialize::test_canonical_serialize_deserialize, SemanticallyValid, UniformRand};
use fiat_shamir::FiatShamirRngSeed;
use rand::{distributions::Distribution, thread_rng};

fn setup_test_fs_rng<G, PC>() -> PC::RandomOracle
where
    G: Group,
    PC: PolynomialCommitment<G>,
{
    let mut fs_rng_seed_builder = FiatShamirRngSeed::new();
    fs_rng_seed_builder.add_bytes(b"TEST_SEED").unwrap();
    let fs_rng_seed = fs_rng_seed_builder.finalize().unwrap();
    PC::RandomOracle::from_seed(fs_rng_seed).unwrap()
}

#[derive(Copy, Clone, PartialEq)]
pub(crate) enum NegativeType {
    Values,
    Commitments,
    CommitterKey,
    VerifierKey,
}

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
    /// set `true` for testing the domain-extension of a scheme
    segmented: bool,
    negative_type: Option<NegativeType>,
}

pub(crate) trait TestUtils {
    /// Randomize commitment for test purpose
    fn randomize(&mut self);
}

impl<G: Group> TestUtils for LabeledCommitment<G> {
    fn randomize(&mut self) {
        *self = LabeledCommitment::new(
            self.label().clone(),
            self.commitment().clone() * &G::ScalarField::rand(&mut thread_rng()),
        );
    }
}

/// A test function that  sets up `PC` for `supported_degree` (random, if not given)
/// samples `num_polynomials` polynomials of random degree and a symmetric query set
/// of size `max_num_queries`, and verifies MultiPointProofs for these.
fn test_template<G, PC, D>(info: TestInfo) -> Result<(), PC::Error>
where
    G: Group,
    D: Digest,
    PC: PolynomialCommitment<G>,
    PC::CommitterKey: TestUtils,
    PC::VerifierKey: TestUtils,
{
    for _ in 0..info.num_iters {
        let TestInfo {
            max_degree,
            supported_degree,
            num_polynomials,
            max_num_queries,
            segmented,
            negative_type,
            ..
        } = info;

        let rng = &mut thread_rng();
        // sample a random max_degree from 2 up to 64 if not provided
        let max_degree =
            max_degree.unwrap_or(rand::distributions::Uniform::from(2..=64).sample(rng));
        // setup the scheme for max_degree.
        // Later it is trimmed down to `supported_degree`.
        let pp = PC::setup::<D>(max_degree)?;

        test_canonical_serialize_deserialize(true, &pp);

        // sample supported_degree if not defined
        let supported_degree = match supported_degree {
            Some(0) => 0,
            Some(d) => d,
            None => rand::distributions::Uniform::from(1..=max_degree).sample(rng),
        };
        assert!(
            max_degree >= supported_degree,
            "max_degree < supported_degree"
        );
        let mut polynomials = Vec::new();

        // sample the maximum number of segments for domain extended commitments
        // from 5 up to 15.
        let seg_mul = rand::distributions::Uniform::from(5..=15).sample(rng);
        let mut poly_labels = Vec::new();
        println!("Sampled supported degree");

        // sample `max_num_queries` query points
        let num_points_in_query_map =
            rand::distributions::Uniform::from(1..=max_num_queries).sample(rng);
        for i in 0..num_polynomials {
            let poly_label = format!("Test{}", i);
            poly_labels.push(poly_label.clone());

            // sample polynomial of random degree
            let degree;
            if segmented {
                // sample degree from 5*`supported_degree` up to `seg_mul`*`supported_degree`
                degree = if supported_degree > 0 {
                    rand::distributions::Uniform::from(1..=supported_degree).sample(rng)
                } else {
                    0
                } * seg_mul;
            } else {
                // sample degree from 1 up to `supported_degree`
                degree = if supported_degree > 0 {
                    rand::distributions::Uniform::from(1..=supported_degree).sample(rng)
                } else {
                    0
                }
            }
            let poly = Polynomial::rand(degree, rng);
            println!("Poly {} degree: {}", i, degree);

            // random choice for hiding or not
            let is_hiding = if rand::distributions::Uniform::from(0..1).sample(rng) == 1 {
                true
            } else {
                false
            };

            polynomials.push(LabeledPolynomial::new(poly_label, poly, is_hiding))
        }
        println!(
            "supported degree by the non-extended scheme: {:?}",
            supported_degree
        );
        println!("num_points_in_query_map: {:?}", num_points_in_query_map);
        let (mut ck, mut vk) = pp.trim(supported_degree)?;

        if negative_type.is_some() && negative_type.unwrap() == NegativeType::CommitterKey {
            ck.randomize();
        }

        if negative_type.is_some() && negative_type.unwrap() == NegativeType::VerifierKey {
            vk.randomize();
        }

        assert!(ck.is_valid());
        assert!(vk.is_valid());


        test_canonical_serialize_deserialize(true, &ck);
        test_canonical_serialize_deserialize(true, &vk);

        let (mut comms, rands) = PC::commit_vec(&ck, &polynomials, Some(rng))?;
        if negative_type.is_some() && negative_type.unwrap() == NegativeType::Commitments {
            for comm in comms.iter_mut() {
                comm.randomize();
            }
        }

        assert!(comms.is_valid());

        // Construct "symmetric" query set from the query points, over which every polynomial
        // is to be queried
        let mut query_map = QueryMap::new();
        let mut values = Evaluations::new();
        for j in 0..num_points_in_query_map {
            let point = G::ScalarField::rand(rng);
            let point_label = format!("{}", j);
            for (i, poly_label) in poly_labels.iter().enumerate() {
                let evaluation_label = (poly_label.clone(), point_label.clone());
                query_map.insert(evaluation_label.clone(), point);
                let value = polynomials[i].evaluate(point);
                if negative_type.is_some() && negative_type.unwrap() == NegativeType::Values {
                    values.insert(evaluation_label, G::ScalarField::rand(rng));
                } else {
                    values.insert(evaluation_label, value);
                }
            }
        }

        let mut fs_rng = setup_test_fs_rng::<G, PC>();

        let proof = PC::multi_point_multi_poly_open(
            &ck,
            &polynomials,
            &comms,
            &query_map,
            &mut fs_rng,
            &rands,
            Some(rng),
        )?;

        assert!(proof.is_valid());

        test_canonical_serialize_deserialize(true, &proof);

        // Assert success using the same key
        let mut fs_rng = setup_test_fs_rng::<G, PC>();
        let verifier_state = PC::succinct_multi_point_multi_poly_verify(
            &vk,
            &comms,
            &query_map,
            &values,
            &proof,
            &mut fs_rng,
        )?;
        if verifier_state.is_none() {
            println!(
                "Failed succinct check with {} polynomials, num_points_in_query_set: {:?}",
                num_polynomials, num_points_in_query_map
            );
            println!("Degree of polynomials:",);
            for poly in polynomials {
                println!("Degree: {:?}", poly.degree());
            }
            return Err(Error::FailedSuccinctCheck.into());
        }

        let verifier_state = verifier_state.unwrap();
        test_canonical_serialize_deserialize(true, &verifier_state);

        let result = PC::hard_verify(&vk, &verifier_state)?;
        if !result {
            println!(
                "Failed with {} polynomials, num_points_in_query_map: {:?}",
                num_polynomials, num_points_in_query_map
            );
            println!("Degree of polynomials:",);
            for poly in polynomials {
                println!("Degree: {:?}", poly.degree());
            }
            return Err(Error::IncorrectProof.into());
        }

        // Assert success using a bigger key
        let bigger_degree = max_degree * 2;
        let pp = PC::setup::<D>(bigger_degree)?;
        let (_, vk) = pp.trim(bigger_degree)?;

        let mut fs_rng = setup_test_fs_rng::<G, PC>();
        assert!(PC::multi_point_multi_poly_verify(
            &vk,
            &comms,
            &query_map,
            &values,
            &proof,
            &mut fs_rng
        )?);
    }
    Ok(())
}

pub(crate) fn constant_poly_test<G, PC, D>(
    negative_type: Option<NegativeType>,
) -> Result<(), PC::Error>
where
    G: Group,
    D: Digest,
    PC: PolynomialCommitment<G>,
    PC::CommitterKey: TestUtils,
    PC::VerifierKey: TestUtils,
{
    let info = TestInfo {
        num_iters: 100,
        max_degree: None,
        supported_degree: Some(0),
        num_polynomials: 1,
        max_num_queries: 1,
        negative_type,
        ..Default::default()
    };
    test_template::<G, PC, D>(info)
}

pub(crate) fn single_poly_test<G, PC, D>(
    negative_type: Option<NegativeType>,
) -> Result<(), PC::Error>
where
    G: Group,
    D: Digest,
    PC: PolynomialCommitment<G>,
    PC::CommitterKey: TestUtils,
    PC::VerifierKey: TestUtils,
{
    let info = TestInfo {
        num_iters: 100,
        max_degree: None,
        supported_degree: None,
        num_polynomials: 1,
        max_num_queries: 1,
        negative_type,
        ..Default::default()
    };
    test_template::<G, PC, D>(info)
}

pub(crate) fn two_poly_four_points_test<G, PC, D>(
    negative_type: Option<NegativeType>,
) -> Result<(), PC::Error>
where
    G: Group,
    D: Digest,
    PC: PolynomialCommitment<G>,
    PC::CommitterKey: TestUtils,
    PC::VerifierKey: TestUtils,
{
    let info = TestInfo {
        num_iters: 1,
        max_degree: Some(1024),
        supported_degree: Some(1024),
        num_polynomials: 2,
        max_num_queries: 4,
        negative_type,
        ..Default::default()
    };
    test_template::<G, PC, D>(info)
}

pub(crate) fn full_end_to_end_test<G, PC, D>(
    negative_type: Option<NegativeType>,
) -> Result<(), PC::Error>
where
    G: Group,
    D: Digest,
    PC: PolynomialCommitment<G>,
    PC::CommitterKey: TestUtils,
    PC::VerifierKey: TestUtils,
{
    let info = TestInfo {
        num_iters: 100,
        max_degree: None,
        supported_degree: None,
        num_polynomials: 10,
        max_num_queries: 5,
        negative_type,
        ..Default::default()
    };
    test_template::<G, PC, D>(info)
}

pub(crate) fn segmented_test<G, PC, D>(negative_type: Option<NegativeType>) -> Result<(), PC::Error>
where
    G: Group,
    D: Digest,
    PC: PolynomialCommitment<G>,
    PC::CommitterKey: TestUtils,
    PC::VerifierKey: TestUtils,
{
    let info = TestInfo {
        num_iters: 100,
        max_degree: None,
        supported_degree: None,
        num_polynomials: 10,
        max_num_queries: 5,
        segmented: true,
        negative_type,
        ..Default::default()
    };
    test_template::<G, PC, D>(info)
}
