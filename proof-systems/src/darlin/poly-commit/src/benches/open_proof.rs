use algebra::{fft::DensePolynomial as Polynomial, UniformRand, Curve};
use rand::thread_rng;
use poly_commit::{PolynomialCommitment, PCKey};
use poly_commit::ipa_pc::{InnerProductArgPC, CommitterKey};
use poly_commit::fiat_shamir_rng::{FiatShamirRng, FiatShamirRngSeed};
use digest::Digest;
use criterion::*;
use blake2::Blake2s;
use num_traits::Zero;

#[derive(Clone, Default)]
struct BenchInfo {
    max_degree: usize,
    supported_degree: usize
}

fn generate_ck<G: Curve, D: Digest>(info: &BenchInfo) -> CommitterKey<G> {
    let BenchInfo {
        max_degree,
        supported_degree,
        ..
    } = info.clone();

    // Generate random params
    let (ck, _) = InnerProductArgPC::<G, D>::setup(max_degree).unwrap();
    let ck = ck.trim(
        supported_degree,
    ).unwrap();

    assert!(
        max_degree >= supported_degree,
        "max_degree < supported_degree"
    );
    
    println!("Len: {}", ck.comm_key.len());
    ck
}

fn bench_open_proof<G: Curve, D: Digest>(
    c: &mut Criterion,
    bench_name: &str,
    coeffs: usize,
) {
    let mut group = c.benchmark_group(bench_name);

    let max_degree = coeffs - 1;

    let info = BenchInfo {
        max_degree,
        supported_degree: max_degree
    };
    let ck = generate_ck::<G, D>(&info);

    group.bench_with_input(BenchmarkId::from_parameter(max_degree), &max_degree, |bn, max_degree| {
        bn.iter_batched(
            || {

                let rng = &mut thread_rng();

                let polynomial = Polynomial::<G::ScalarField>::rand(*max_degree, rng);
        
                let point = G::ScalarField::rand(rng);

                let mut fs_rng_seed_builder =
                    <<InnerProductArgPC<G, D> as PolynomialCommitment<G>>::RandomOracle as FiatShamirRng>::Seed::new();
                fs_rng_seed_builder.add_bytes(b"BENCH_SEED").unwrap();
                let fs_rng_seed = fs_rng_seed_builder.finalize();

                let fs_rng =
                    <InnerProductArgPC::<G, D> as PolynomialCommitment<G>>::RandomOracle::from_seed(fs_rng_seed);

                (polynomial, point, fs_rng)
            },
            |(polynomial, point, mut fs_rng)| {
                InnerProductArgPC::<G, D>::open(
                    &ck,
                    polynomial,
                    point,
                    false,
                    G::ScalarField::zero(),
                    &mut fs_rng,
                    None
                ).unwrap();
            },
            BatchSize::PerIteration
        );
    });
    group.finish();
}

use algebra::curves::tweedle::{
        dee::DeeJacobian as TweedleDee,
        dum::DumJacobian as TweedleDum,
    };

fn bench_open_proof_tweedle_dee(c: &mut Criterion) {

    for n in 16..22 {
        bench_open_proof::<TweedleDee, Blake2s>(
            c,
            "open proof in tweedle-dee, coeffs",
            1 << n
        );
    }
}

fn bench_open_proof_tweedle_dum(c: &mut Criterion) {

    for n in 16..22 {
        bench_open_proof::<TweedleDum, Blake2s>(
            c,
            "open proof in tweedle-dum, coeffs",
            1 << n
        );    
    }
}

criterion_group!(
name = tweedle_open_proof;
config = Criterion::default().sample_size(30);
targets = bench_open_proof_tweedle_dee, bench_open_proof_tweedle_dum
);

criterion_main!(tweedle_open_proof);