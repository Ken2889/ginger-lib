use algebra::{fft::DensePolynomial as Polynomial, UniformRand};
use blake2::Blake2s;
use criterion::*;
use digest::Digest;
use fiat_shamir::{FiatShamirRng, FiatShamirRngSeed};
use num_traits::Zero;
use poly_commit::ipa_pc::{CommitterKey, IPACurve, InnerProductArgPC};
use poly_commit::{PCKey, PolynomialCommitment};
use rand::thread_rng;

#[derive(Clone, Default)]
struct BenchInfo {
    max_degree: usize,
    supported_degree: usize,
}

fn generate_ck<G: IPACurve, FS: FiatShamirRng, D: Digest>(info: &BenchInfo) -> CommitterKey<G> {
    let BenchInfo {
        max_degree,
        supported_degree,
        ..
    } = info.clone();

    // Generate random params
    let (ck, _) = InnerProductArgPC::<G, FS>::setup::<D>(max_degree).unwrap();
    let ck = ck.trim(supported_degree).unwrap();

    assert!(
        max_degree >= supported_degree,
        "max_degree < supported_degree"
    );

    println!("Len: {}", ck.comm_key.len());
    ck
}

fn bench_open_proof<G: IPACurve, FS: FiatShamirRng, D: Digest>(
    c: &mut Criterion,
    bench_name: &str,
    coeffs: usize,
) {
    let mut group = c.benchmark_group(bench_name);

    let max_degree = coeffs - 1;

    let info = BenchInfo {
        max_degree,
        supported_degree: max_degree,
    };
    let ck = generate_ck::<G, FS, D>(&info);

    group.bench_with_input(
        BenchmarkId::from_parameter(max_degree),
        &max_degree,
        |bn, max_degree| {
            bn.iter_batched(
                || {
                    let rng = &mut thread_rng();

                    let polynomial = Polynomial::<G::ScalarField>::rand(*max_degree, rng);

                    let point = G::ScalarField::rand(rng);

                    let mut fs_rng_seed_builder = FiatShamirRngSeed::new();
                    fs_rng_seed_builder.add_bytes(b"BENCH_SEED").unwrap();
                    let fs_rng_seed = fs_rng_seed_builder.finalize().unwrap();

                    let fs_rng = FS::from_seed(fs_rng_seed).unwrap();

                    (polynomial, point, fs_rng)
                },
                |(polynomial, point, mut fs_rng)| {
                    InnerProductArgPC::<G, FS>::open(
                        &ck,
                        polynomial,
                        point,
                        false,
                        G::ScalarField::zero(),
                        &mut fs_rng,
                        None,
                    )
                    .unwrap();
                },
                BatchSize::PerIteration,
            );
        },
    );
    group.finish();
}

use algebra::curves::tweedle::{dee::DeeJacobian as TweedleDee, dum::DumJacobian as TweedleDum};

#[cfg(not(feature = "circuit-friendly"))]
mod benches {
    use super::*;
    use fiat_shamir::chacha20::FiatShamirChaChaRng;

    pub(crate) fn bench_open_proof_tweedle_dee(c: &mut Criterion) {
        for n in 16..22 {
            bench_open_proof::<TweedleDee, FiatShamirChaChaRng<Blake2s>, Blake2s>(
                c,
                "open proof in tweedle-dee, coeffs",
                1 << n,
            );
        }
    }

    pub(crate) fn bench_open_proof_tweedle_dum(c: &mut Criterion) {
        for n in 16..22 {
            bench_open_proof::<TweedleDum, FiatShamirChaChaRng<Blake2s>, Blake2s>(
                c,
                "open proof in tweedle-dum, coeffs",
                1 << n,
            );
        }
    }
}

#[cfg(feature = "circuit-friendly")]
mod benches {
    use super::*;
    use fiat_shamir::poseidon::{TweedleFqPoseidonFSRng, TweedleFrPoseidonFSRng};

    pub(crate) fn bench_open_proof_tweedle_dee(c: &mut Criterion) {
        for n in 16..22 {
            bench_open_proof::<TweedleDee, TweedleFqPoseidonFSRng, Blake2s>(
                c,
                "open proof in tweedle-dee, coeffs",
                1 << n,
            );
        }
    }

    pub(crate) fn bench_open_proof_tweedle_dum(c: &mut Criterion) {
        for n in 16..22 {
            bench_open_proof::<TweedleDum, TweedleFrPoseidonFSRng, Blake2s>(
                c,
                "open proof in tweedle-dum, coeffs",
                1 << n,
            );
        }
    }
}

criterion_group!(
    name = single_point_single_poly_open_bench;
    config = Criterion::default().sample_size(10);
    targets = benches::bench_open_proof_tweedle_dee, benches::bench_open_proof_tweedle_dum
);

criterion_main!(single_point_single_poly_open_bench);
