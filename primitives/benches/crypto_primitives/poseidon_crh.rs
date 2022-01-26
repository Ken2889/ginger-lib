use algebra::fields::{tweedle::Fq as tweedleFq, tweedle::Fr as tweedleFr};
use criterion::{criterion_group, criterion_main, Criterion};

use algebra::UniformRand;
use primitives::crh::{poseidon::parameters::*, FieldBasedHash};
use rand::SeedableRng;
use rand_xorshift::XorShiftRng;

fn poseidon_crh_eval_tweedlefr(c: &mut Criterion) {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);
    let samples = 2000;
    let mut h = TweedleFrPoseidonHash::init_constant_length(samples, None);

    c.bench_function("Poseidon CRH Eval for tweedleFr", move |b| {
        b.iter(|| {
            for _ in 0..samples {
                h.update(tweedleFr::rand(&mut rng));
            }
            h.finalize().unwrap();
            h.reset(None);
        })
    });
}

fn poseidon_crh_eval_tweedlefq(c: &mut Criterion) {
    let mut rng = XorShiftRng::seed_from_u64(1231275789u64);
    let samples = 2000;
    let mut h = TweedleFqPoseidonHash::init_constant_length(samples, None);

    c.bench_function("Poseidon CRH Eval for tweedleFq", move |b| {
        b.iter(|| {
            for _ in 0..samples {
                h.update(tweedleFq::rand(&mut rng));
            }
            h.finalize().unwrap();
            h.reset(None);
        })
    });
}

criterion_group! {
    name = crh_poseidon_eval;
    config = Criterion::default().sample_size(20);
    targets = poseidon_crh_eval_tweedlefq, poseidon_crh_eval_tweedlefr,
}

criterion_main!(crh_poseidon_eval);
