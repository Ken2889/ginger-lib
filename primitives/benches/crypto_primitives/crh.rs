#[macro_use]
extern crate criterion;

use algebra::curves::tweedle::{dee::DeeJacobian, dum::DumJacobian};
use criterion::Criterion;
use primitives::crh::{bowe_hopwood::*, FixedLengthCRH};

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct HashWindow;

impl PedersenWindow for HashWindow {
    const WINDOW_SIZE: usize = 63;
    const NUM_WINDOWS: usize = 6;
}

fn pedersen_crh_setup_dee(c: &mut Criterion) {
    c.bench_function("Pedersen CRH Setup", move |b| {
        b.iter(|| {
            let mut rng = &mut rand::thread_rng();
            BoweHopwoodPedersenCRH::<DeeJacobian, HashWindow>::setup(&mut rng).unwrap()
        })
    });
}

fn pedersen_crh_eval_dee(c: &mut Criterion) {
    let mut rng = &mut rand::thread_rng();
    let parameters = BoweHopwoodPedersenCRH::<DeeJacobian, HashWindow>::setup(&mut rng).unwrap();
    let input = vec![5u8; 128];
    c.bench_function("Pedersen CRH Eval", move |b| {
        b.iter(|| {
            BoweHopwoodPedersenCRH::<DeeJacobian, HashWindow>::evaluate(&parameters, &input).unwrap();
        })
    });
}

fn pedersen_crh_setup_dum(c: &mut Criterion) {
    c.bench_function("Pedersen CRH Setup", move |b| {
        b.iter(|| {
            let mut rng = &mut rand::thread_rng();
            BoweHopwoodPedersenCRH::<DumJacobian, HashWindow>::setup(&mut rng).unwrap()
        })
    });
}

fn pedersen_crh_eval_dum(c: &mut Criterion) {
    let mut rng = &mut rand::thread_rng();
    let parameters = BoweHopwoodPedersenCRH::<DumJacobian, HashWindow>::setup(&mut rng).unwrap();
    let input = vec![5u8; 128];
    c.bench_function("Pedersen CRH Eval", move |b| {
        b.iter(|| {
            BoweHopwoodPedersenCRH::<DumJacobian, HashWindow>::evaluate(&parameters, &input).unwrap();
        })
    });
}

criterion_group! {
    name = crh_setup;
    config = Criterion::default().sample_size(20);
    targets = pedersen_crh_setup_dee, pedersen_crh_setup_dum
}

criterion_group! {
    name = crh_eval;
    config = Criterion::default().sample_size(20);
    targets = pedersen_crh_eval_dee, pedersen_crh_eval_dum
}

criterion_main!(crh_setup, crh_eval);
