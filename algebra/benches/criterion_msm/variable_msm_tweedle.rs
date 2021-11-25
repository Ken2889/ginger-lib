#[macro_use]
extern crate criterion;

#[macro_use]
extern crate bench_utils;

use criterion::{BatchSize, BenchmarkId, Criterion};

use algebra::msm::VariableBaseMSM;
use algebra::{
    Curve,
    curves::tweedle::dee::DeeJacobian,
    BigInteger256, FromBytes, ToBytes, UniformRand,
};

use std::fs::File;
use std::path::Path;
use std::time::{SystemTime, UNIX_EPOCH};

const DATA_PATH: &str = "./msm_bases_tweedle";

fn save_data(samples: usize) {
    let rng = &mut rand::thread_rng();

    let mut fs = File::create(DATA_PATH).unwrap();

    for _ in 0..samples {
        let elem1: BigInteger256 = BigInteger256::rand(rng);
        let elem2: DeeJacobian = DeeJacobian::rand(rng);
        match elem1.write(&mut fs) {
            Ok(_) => {}
            Err(msg) => {
                panic!("Cannot save coeffs to file: {}", msg)
            }
        }
        match elem2.write(&mut fs) {
            Ok(_) => {}
            Err(msg) => {
                panic!("Cannot save coeffs to file: {}", msg)
            }
        }
    }
}

fn load_data(samples: usize) -> (Vec<BigInteger256>, Vec<DeeJacobian>) {
    if !Path::new(DATA_PATH).exists() {
        save_data(1 << 23);
    }

    let mut fs = File::open(DATA_PATH).unwrap();
    let mut v = Vec::with_capacity(samples);
    let mut g = Vec::with_capacity(samples);

    for _i in 0..samples {
        let elem1 = BigInteger256::read(&mut fs).unwrap();
        let elem2 = DeeJacobian::read(&mut fs).unwrap();
        v.push(elem1);
        g.push(elem2);
    }

    DeeJacobian::batch_normalization(g.as_mut_slice());

    (v, g)
}

fn variable_msm(c: &mut Criterion) {
    let mut group = c.benchmark_group(
        "variable_base_msm_affine-tweedle-variable number of bases = number of scalars",
    );
    let samples = (14..=23).map(|i| 2usize.pow(i)).collect::<Vec<_>>();

    for &samples in samples.iter() {
        group.bench_with_input(
            BenchmarkId::from_parameter(samples),
            &samples,
            |b, _samples| {
                b.iter_batched(
                    || {
                        let (v, g) = load_data(samples);
                        (v, DeeJacobian::batch_into_affine(g.as_slice()))
                    },
                    |(v, g)| {
                        add_to_trace!(
                            || format!("****************{}*******************", samples),
                            || format!(
                                "--->START TIMESTAMP: {:?}",
                                SystemTime::now()
                                    .duration_since(UNIX_EPOCH)
                                    .unwrap()
                                    .as_secs()
                            )
                        );
                        VariableBaseMSM::multi_scalar_mul::<DeeJacobian>(g.as_slice(), v.as_slice()).unwrap();
                        add_to_trace!(
                            || format!("****************{}*******************", samples),
                            || format!(
                                "--->END TIMESTAMP: {:?}",
                                SystemTime::now()
                                    .duration_since(UNIX_EPOCH)
                                    .unwrap()
                                    .as_secs()
                            )
                        );
                    },
                    BatchSize::PerIteration,
                );
            },
        );
    }
}

criterion_group! {
    name = variable_msm_eval_tweedle;
    config = Criterion::default().sample_size(10);
    targets = variable_msm,
}

criterion_main!(variable_msm_eval_tweedle);
