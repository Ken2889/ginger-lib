use algebra::curves::tweedle::dee::DeeJacobian;
use algebra::fields::tweedle::Fq;
use algebra::UniformRand;
use criterion::Criterion;
use primitives::{
    crh::{bowe_hopwood::BoweHopwoodPedersenCRH, pedersen::PedersenWindow, TweedleFqPoseidonHash},
    vrf::{ecvrf::FieldBasedEcVrf, FieldBasedVrf},
    FixedLengthCRH,
};

#[macro_use]
extern crate criterion;

#[derive(Clone)]
struct TestWindow {}
impl PedersenWindow for TestWindow {
    const WINDOW_SIZE: usize = 42;
    const NUM_WINDOWS: usize = 2;
}

type BHDee = BoweHopwoodPedersenCRH<DeeJacobian, TestWindow>;
type EcVrfDee = FieldBasedEcVrf<Fq, DeeJacobian, TweedleFqPoseidonHash, BHDee>;

fn ecvrf_keygen(c: &mut Criterion) {
    c.bench_function("FieldSchnorrDee: KeyGen", move |b| {
        b.iter(|| {
            let mut rng = &mut rand::thread_rng();
            EcVrfDee::keygen(&mut rng)
        })
    });
}

fn ecvrf_prove(c: &mut Criterion) {
    let mut rng = &mut rand::thread_rng();
    let pp = <BHDee as FixedLengthCRH>::setup(rng).unwrap();
    let (pk, sk) = EcVrfDee::keygen(&mut rng);
    let message = Fq::rand(rng);

    c.bench_function("FieldSchnorrDee: Sign", move |b| {
        b.iter(|| {
            let mut rng = &mut rand::thread_rng();
            EcVrfDee::prove(&mut rng, &pp, &pk, &sk, message).unwrap()
        })
    });
}

fn ecvrf_verify(c: &mut Criterion) {
    let mut rng = &mut rand::thread_rng();
    let pp = <BHDee as FixedLengthCRH>::setup(rng).unwrap();
    let (pk, sk) = EcVrfDee::keygen(&mut rng);
    let message = Fq::rand(rng);
    let proof = EcVrfDee::prove(&mut rng, &pp, &pk, &sk, message).unwrap();

    c.bench_function("FieldSchnorrDee: Proof To Hash", move |b| {
        b.iter(|| EcVrfDee::proof_to_hash(&pp, &pk, message, &proof).unwrap())
    });
}

criterion_group! {
    name = ecvrf;
    config = Criterion::default().sample_size(20);
    targets = ecvrf_keygen, ecvrf_prove, ecvrf_verify
}

criterion_main!(ecvrf);
