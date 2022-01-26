use algebra::{Curve, DensePolynomial as Polynomial, UniformRand};
use blake2::Blake2s;
use criterion::*;
use digest::Digest;
use poly_commit::fiat_shamir::{FiatShamirRng, FiatShamirRngSeed};
use poly_commit::ipa_pc::{CommitterKey, InnerProductArgPC};
use poly_commit::{LabeledPolynomial, PCParameters, PolynomialCommitment};
use rand::{thread_rng, RngCore};
use rand_xorshift::XorShiftRng;

#[derive(Clone, Default)]
struct BenchInfo {
    max_degree: usize,
    supported_degree: usize,
}

fn generate_ck<G: Curve, D: Digest, R: RngCore>(info: &BenchInfo) -> CommitterKey<G> {
    let BenchInfo {
        max_degree,
        supported_degree,
        ..
    } = info.clone();

    // Generate random params
    let pp = InnerProductArgPC::<G, D>::setup(max_degree).unwrap();
    let (ck, _) = pp.trim(supported_degree).unwrap();

    assert!(
        max_degree >= supported_degree,
        "max_degree < supported_degree"
    );

    ck
}

fn bench_open_proof<G: Curve, D: Digest>(c: &mut Criterion, bench_name: &str, coeffs: usize) {
    let mut group = c.benchmark_group(bench_name);

    let max_degree = coeffs - 1;

    let info = BenchInfo {
        max_degree,
        supported_degree: max_degree,
    };
    let ck = generate_ck::<G, D, XorShiftRng>(&info);

    group.bench_with_input(
        BenchmarkId::from_parameter(max_degree),
        &max_degree,
        |bn, max_degree| {
            bn.iter_batched(
                || {
                    let rng = &mut thread_rng();
                    let mut polynomials = Vec::new();

                    let label = format!("Test");

                    polynomials.push(LabeledPolynomial::new(
                        label,
                        Polynomial::<G::ScalarField>::rand(*max_degree, rng),
                        false,
                    ));

                    let (comms, rands) =
                        InnerProductArgPC::<G, D>::commit_vec(&ck, &polynomials, Some(rng))
                            .unwrap();

                    let point = G::ScalarField::rand(rng);

                    let mut fs_rng_seed_builder =
                        <<InnerProductArgPC<G, D> as PolynomialCommitment<G>>::RandomOracle as FiatShamirRng>::Seed::new();
                    fs_rng_seed_builder.add_bytes(b"BENCH_SEED").unwrap();
                    let fs_rng_seed = fs_rng_seed_builder.finalize();
                    let fs_rng =
                        <InnerProductArgPC::<G, D> as PolynomialCommitment<G>>::RandomOracle::from_seed(fs_rng_seed);

                    (polynomials, comms, point, fs_rng, rands)
                },
                |(polynomials, comms, point, mut fs_rng, rands)| {
                    let rng = &mut thread_rng();
                    InnerProductArgPC::<G, D>::single_point_multi_poly_open(
                        &ck,
                        &polynomials,
                        &comms,
                        point,
                        &mut fs_rng,
                        &rands,
                        Some(rng),
                    )
                    .unwrap();
                },
                BatchSize::PerIteration,
            );
        },
    );
    group.finish();
}

use algebra::curves::tweedle::{dee::DeeJacobian, dum::DumJacobian};

fn bench_open_proof_tweedle_dee(c: &mut Criterion) {
    for n in 16..22 {
        bench_open_proof::<DeeJacobian, Blake2s>(c, "open proof in tweedle-dee, coeffs", 1 << n);
    }
}

fn bench_open_proof_tweedle_dum(c: &mut Criterion) {
    for n in 16..22 {
        bench_open_proof::<DumJacobian, Blake2s>(c, "open proof in tweedle-dum, coeffs", 1 << n);
    }
}

criterion_group!(
name = tweedle_open_proof;
config = Criterion::default().sample_size(10);
targets = bench_open_proof_tweedle_dee, bench_open_proof_tweedle_dum
);

criterion_main!(tweedle_open_proof);
