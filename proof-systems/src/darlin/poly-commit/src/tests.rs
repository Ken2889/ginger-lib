//! Unit tests for linear polynomial commitment schemes and their domain extension.
use crate::fiat_shamir_rng::FiatShamirRngSeed;
use crate::*;
use algebra::{serialize::test_canonical_serialize_deserialize, SemanticallyValid, UniformRand};
use rand::{distributions::Distribution, thread_rng};

fn setup_test_fs_rng<G, PC>() -> PC::RandomOracle
where
    G: Group,
    PC: PolynomialCommitment<G>,
{
    let mut fs_rng_seed_builder = <PC::RandomOracle as FiatShamirRng>::Seed::new();
    fs_rng_seed_builder.add_bytes(b"TEST_SEED").unwrap();
    let fs_rng_seed = fs_rng_seed_builder.finalize();
    PC::RandomOracle::from_seed(fs_rng_seed)
}

// The vectorial variant of `fn commit()`. Outputs a vector of commitments
// to a set of `polynomials`.
// If `polynomials[i].is_hiding()`, then the `i`-th commitment is hiding.
// Hence `rng` should not be `None` if `polynomials[i].is_hiding() == true`
// for some of the `i`s.
// If for some `i`, `polynomials[i].is_hiding() == false`, then the
// corresponding randomness is `G::ScalarField::empty()`.

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
    segment_size: Option<usize>,
    /// The number of polynomials
    num_polynomials: usize,
    /// the number of query points
    max_num_queries: usize,
    /// set `true` for testing the domain-extension of a scheme
    segmented: bool,
    /// select the particular negative test to perform
    negative_type: Option<NegativeType>,
    /// for PC schemes, like DLOG, supporting proofs verification
    /// with oversized keys
    allow_oversized_keys: bool,
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

/// A test function that  sets up `PC` for `segment_size` (random, if not given)
/// samples `num_polynomials` polynomials of random degree and a symmetric query map
/// of size `max_num_queries`, and verifies MultiPointProofs for these.
fn test_template<G, PC: PolynomialCommitment<G>>(info: TestInfo) -> Result<(), PC::Error>
where
    G: Group,
    PC::CommitterKey: TestUtils,
    PC::VerifierKey: TestUtils,
{
    for _ in 0..info.num_iters {
        let TestInfo {
            max_degree,
            segment_size,
            num_polynomials,
            max_num_queries,
            segmented,
            negative_type,
            allow_oversized_keys,
            ..
        } = info;

        let rng = &mut thread_rng();
        // sample a random max_degree from 2 up to 64 if not provided
        let max_degree =
            max_degree.unwrap_or(rand::distributions::Uniform::from(2..=64).sample(rng));
        // setup the scheme for max_degree.
        // Later it is trimmed down to `segment_size`.
        let (max_ck, max_vk) = PC::setup(max_degree)?;

        test_canonical_serialize_deserialize(true, &max_ck);

        // sample segment_size if not defined
        let segment_size = match segment_size {
            Some(0) => 0,
            Some(d) => d,
            None => rand::distributions::Uniform::from(1..max_degree).sample(rng),
        };
        assert!(max_degree >= segment_size, "max_degree < segment_size");
        let mut polynomials = Vec::new();

        // sample the maximum number of segments for domain extended commitments
        // from 5 up to 15.
        let seg_mul = rand::distributions::Uniform::from(5..=15).sample(rng);
        let mut labels = Vec::new();
        println!("Sampled supported degree");

        // sample `max_num_queries` query points
        let num_points_in_query_map =
            rand::distributions::Uniform::from(1..=max_num_queries).sample(rng);
        for i in 0..num_polynomials {
            let label = format!("Test{}", i);
            labels.push(label.clone());

            // sample polynomial of random degree
            let degree;
            if segmented {
                // sample degree from 5*`segment_size` up to `seg_mul`*`segment_size`
                degree = if segment_size > 0 {
                    rand::distributions::Uniform::from(1..=segment_size).sample(rng)
                } else {
                    0
                } * seg_mul;
            } else {
                // sample degree from 1 up to `segment_size`
                degree = if segment_size > 0 {
                    rand::distributions::Uniform::from(1..=segment_size).sample(rng)
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

            polynomials.push(LabeledPolynomial::new(label, poly, is_hiding))
        }
        println!(
            "supported degree by the non-extended scheme: {:?}",
            segment_size
        );
        println!("num_points_in_query_map: {:?}", num_points_in_query_map);
        let mut ck = max_ck.trim(segment_size)?;
        let mut vk = max_vk.trim(segment_size)?;

        if negative_type.is_some() && negative_type.unwrap() == NegativeType::CommitterKey {
            ck.randomize();
        }

        if negative_type.is_some() && negative_type.unwrap() == NegativeType::VerifierKey {
            vk.randomize();
        }

        assert!(ck.is_valid());
        assert!(vk.is_valid());

        println!("Trimmed");

        test_canonical_serialize_deserialize(true, &ck);
        test_canonical_serialize_deserialize(true, &vk);

        let (mut comms, rands) = {
            let mut labeled_commitments = Vec::new();
            let mut labeled_randomnesses = Vec::new();

            for labeled_polynomial in polynomials.iter() {
                let polynomial = labeled_polynomial.polynomial();
                let label = labeled_polynomial.label();
                let is_hiding = labeled_polynomial.is_hiding();

                let (commitment, randomness) = PC::commit(&ck, polynomial, is_hiding, Some(rng))?;

                let labeled_commitment = LabeledCommitment::new(label.to_string(), commitment);
                let labeled_randomness = LabeledRandomness::new(label.to_string(), randomness);

                labeled_commitments.push(labeled_commitment);
                labeled_randomnesses.push(labeled_randomness);
            }

            (labeled_commitments, labeled_randomnesses)
        };

        if negative_type.is_some() && negative_type.unwrap() == NegativeType::Commitments {
            for comm in comms.iter_mut() {
                comm.randomize();
            }
        }

        assert!(comms.is_valid());

        // Evaluate all polynomials in all points
        let mut query_map = QueryMap::new();
        let mut values = Evaluations::new();
        // let mut point = F::one();
        for i in 0..num_points_in_query_map {
            let point = G::ScalarField::rand(rng);
            let point_label = format!("{}", i);
            query_map.insert(point_label.clone(), (point, labels.iter().cloned().collect()));
            for poly in polynomials.iter() {
                let value = poly.evaluate(point);
                if negative_type.is_some() && negative_type.unwrap() == NegativeType::Values {
                    values.insert((poly.label().clone(), point_label.clone()), G::ScalarField::rand(rng));
                } else {
                    values.insert((poly.label().clone(), point_label.clone()), value);
                }
            }
        }
        println!("Generated query map");

        let mut fs_rng = setup_test_fs_rng::<G, PC>();
        let proof = PC::multi_point_multi_poly_open(
            &ck,
            &polynomials,
            &query_map,
            &mut fs_rng,
            &rands,
            Some(rng),
        )?;

        assert!(proof.is_valid());

        test_canonical_serialize_deserialize(true, &proof);

        let mut fs_rng = setup_test_fs_rng::<G, PC>();
        let result = PC::multi_point_multi_poly_verify(
            &vk,
            &comms,
            &query_map,
            &values,
            &proof,
            &mut fs_rng,
        )?;
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
        if allow_oversized_keys {
            let bigger_degree = max_degree * 2;
            let (_, vk) = PC::setup(bigger_degree)?;
    
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

    }
    Ok(())
}

// TODO: what is the difference to `single_poly_test()`?
pub(crate) fn constant_poly_test<G, PC>(
    negative_type: Option<NegativeType>,
    allow_oversized_keys: bool,
) -> Result<(), PC::Error>
where
    G: Group,
    PC: PolynomialCommitment<G>,
    PC::CommitterKey: TestUtils,
    PC::VerifierKey: TestUtils,
{
    let info = TestInfo {
        num_iters: 100,
        max_degree: None,
        segment_size: None,
        num_polynomials: 1,
        max_num_queries: 1,
        negative_type,
        allow_oversized_keys,
        ..Default::default()
    };
    test_template::<G, PC>(info)
}

pub(crate) fn single_poly_test<G, PC>(
    negative_type: Option<NegativeType>,
    allow_oversized_keys: bool,
) -> Result<(), PC::Error>
where
    G: Group,
    PC: PolynomialCommitment<G>,
    PC::CommitterKey: TestUtils,
    PC::VerifierKey: TestUtils,
{
    let info = TestInfo {
        num_iters: 100,
        max_degree: None,
        segment_size: None,
        num_polynomials: 1,
        max_num_queries: 1,
        negative_type,
        allow_oversized_keys,
        ..Default::default()
    };
    test_template::<G, PC>(info)
}

pub(crate) fn two_poly_four_points_test<G, PC>(
    negative_type: Option<NegativeType>,
    allow_oversized_keys: bool,
) -> Result<(), PC::Error>
where
    G: Group,
    PC: PolynomialCommitment<G>,
    PC::CommitterKey: TestUtils,
    PC::VerifierKey: TestUtils,
{
    let info = TestInfo {
        num_iters: 1,
        max_degree: Some(1024),
        segment_size: Some(1024),
        num_polynomials: 2,
        max_num_queries: 4,
        negative_type,
        allow_oversized_keys,
        ..Default::default()
    };
    test_template::<G, PC>(info)
}

pub(crate) fn full_end_to_end_test<G, PC>(
    negative_type: Option<NegativeType>,
    allow_oversized_keys: bool,
) -> Result<(), PC::Error>
where
    G: Group,
    PC: PolynomialCommitment<G>,
    PC::CommitterKey: TestUtils,
    PC::VerifierKey: TestUtils,
{
    let info = TestInfo {
        num_iters: 100,
        max_degree: None,
        segment_size: None,
        num_polynomials: 10,
        max_num_queries: 5,
        negative_type,
        allow_oversized_keys,
        ..Default::default()
    };
    test_template::<G, PC>(info)
}

pub(crate) fn segmented_test<G, PC>(
    negative_type: Option<NegativeType>,
    allow_oversized_keys: bool,
) -> Result<(), PC::Error>
where
    G: Group,
    PC: PolynomialCommitment<G>,
    PC::CommitterKey: TestUtils,
    PC::VerifierKey: TestUtils,
{
    let info = TestInfo {
        num_iters: 100,
        max_degree: None,
        segment_size: None,
        num_polynomials: 10,
        max_num_queries: 5,
        segmented: true,
        negative_type,
        allow_oversized_keys,
        ..Default::default()
    };
    test_template::<G, PC>(info)
}
