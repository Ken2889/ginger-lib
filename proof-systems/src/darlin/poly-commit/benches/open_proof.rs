use algebra::{DensePolynomial as Polynomial, EndoMulCurve, UniformRand};
use blake2::Blake2s;
use criterion::*;
use digest::Digest;
use fiat_shamir::{FiatShamirRng, FiatShamirRngSeed};
use poly_commit::ipa_pc::{CommitterKey, InnerProductArgPC};
use poly_commit::{LabeledPolynomial, PCParameters, PolynomialCommitment};
use rand::{thread_rng, RngCore};
use rand_xorshift::XorShiftRng;

#[derive(Clone, Default)]
struct BenchInfo {
    max_degree: usize,
    supported_degree: usize,
}

fn generate_ck<G: EndoMulCurve, FS: FiatShamirRng, D: Digest, R: RngCore>(
    info: &BenchInfo,
) -> CommitterKey<G> {
    let BenchInfo {
        max_degree,
        supported_degree,
        ..
    } = info.clone();

    // Generate random params
    let pp = InnerProductArgPC::<G, FS>::setup::<D>(max_degree).unwrap();
    let (ck, _) = pp.trim(supported_degree).unwrap();

    assert!(
        max_degree >= supported_degree,
        "max_degree < supported_degree"
    );

    ck
}

fn bench_open_proof<G: EndoMulCurve, FS: FiatShamirRng, D: Digest>(
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
    let ck = generate_ck::<G, FS, D, XorShiftRng>(&info);

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
                        InnerProductArgPC::<G, FS>::commit_vec(&ck, &polynomials, Some(rng))
                            .unwrap();

                    let point = G::ScalarField::rand(rng);

                    let mut fs_rng_seed_builder = FiatShamirRngSeed::new();
                    fs_rng_seed_builder.add_bytes(b"BENCH_SEED").unwrap();
                    let fs_rng_seed = fs_rng_seed_builder.finalize().unwrap();
                    let fs_rng =
                        <InnerProductArgPC::<G, FS> as PolynomialCommitment<G>>::RandomOracle::from_seed(fs_rng_seed).unwrap();

                    (polynomials, comms, point, fs_rng, rands)
                },
                |(polynomials, comms, point, mut fs_rng, rands)| {
                    let rng = &mut thread_rng();
                    InnerProductArgPC::<G, FS>::single_point_multi_poly_open(
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

#[cfg(not(feature = "circuit-friendly"))]
mod benches {
    use super::*;
    use fiat_shamir::chacha20::FiatShamirChaChaRng;

    pub(crate) fn bench_open_proof_tweedle_dee(c: &mut Criterion) {
        for n in 16..22 {
            bench_open_proof::<DeeJacobian, FiatShamirChaChaRng<Blake2s>, Blake2s>(
                c,
                "open proof in tweedle-dee, chacha fs, coeffs",
                1 << n,
            );
        }
    }

    pub(crate) fn bench_open_proof_tweedle_dum(c: &mut Criterion) {
        for n in 16..22 {
            bench_open_proof::<DumJacobian, FiatShamirChaChaRng<Blake2s>, Blake2s>(
                c,
                "open proof in tweedle-dum, chacha fs, coeffs",
                1 << n,
            );
        }
    }
}

#[cfg(feature = "circuit-friendly")]
mod benches {
    use super::*;
    use fiat_shamir::poseidon::{TweedleFrPoseidonFSRng, TweedleFqPoseidonFSRng};

    pub(crate) fn bench_open_proof_tweedle_dee(c: &mut Criterion) {
        for n in 16..22 {
            bench_open_proof::<DeeJacobian, TweedleFqPoseidonSponge, Blake2s>(
                c,
                "open proof in tweedle-dee, poseidon fs, coeffs",
                1 << n,
            );
        }
    }

    pub(crate) fn bench_open_proof_tweedle_dum(c: &mut Criterion) {
        for n in 16..22 {
            bench_open_proof::<DumJacobian, TweedleFrPoseidonSponge, Blake2s>(
                c,
                "open proof in tweedle-dum, poseidon fs, coeffs",
                1 << n,
            );
        }
    }
}

criterion_group!(
name = tweedle_open_proof;
config = Criterion::default().sample_size(10);
targets = benches::bench_open_proof_tweedle_dee, benches::bench_open_proof_tweedle_dum,
);

criterion_main!(tweedle_open_proof);
