#[macro_use]
extern crate criterion;

use algebra::{
    curves::tweedle::dee::DeeJacobian as TweedleDee, fields::tweedle::Fq as TweedleFq,
    UniformRand,
};
use criterion::Criterion;
use primitives::{
    crh::poseidon::tweedle_dum::TweedleFqPoseidonHash,
    signature::{schnorr::*, FieldBasedSignatureScheme},
};

type SchnorrTweedleFq =
    FieldBasedSchnorrSignatureScheme<TweedleFq, TweedleDee, TweedleFqPoseidonHash>;

fn schnorr_signature_keygen(c: &mut Criterion) {
    c.bench_function("FieldSchnorrTweedleDee: KeyGen", move |b| {
        b.iter(|| {
            let mut rng = &mut rand::thread_rng();
            SchnorrTweedleFq::keygen(&mut rng)
        })
    });
}

fn schnorr_signature_sign(c: &mut Criterion) {
    let mut rng = &mut rand::thread_rng();
    let (pk, sk) = SchnorrTweedleFq::keygen(&mut rng);
    let message = TweedleFq::rand(rng);

    c.bench_function("FieldSchnorrTweedleDee: Sign", move |b| {
        b.iter(|| {
            let mut rng = &mut rand::thread_rng();
            SchnorrTweedleFq::sign(&mut rng, &pk, &sk, message).unwrap()
        })
    });
}

fn schnorr_signature_verify(c: &mut Criterion) {
    let mut rng = &mut rand::thread_rng();
    let (pk, sk) = SchnorrTweedleFq::keygen(&mut rng);
    let message = TweedleFq::rand(rng);
    let signature = SchnorrTweedleFq::sign(&mut rng, &pk, &sk, message).unwrap();

    c.bench_function("FieldSchnorrTweedleDee: Verify", move |b| {
        b.iter(|| SchnorrTweedleFq::verify(&pk, message, &signature).unwrap())
    });
}

criterion_group! {
    name = field_based_schnorr_sig;
    config = Criterion::default().sample_size(20);
    targets = schnorr_signature_keygen,
                schnorr_signature_sign, schnorr_signature_verify,
}

criterion_main!(field_based_schnorr_sig);
