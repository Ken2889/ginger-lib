#[macro_use]
extern crate criterion;

mod projective {
    use algebra::curves::tweedle::dee::DeeJacobian as TweedleDee;
    use blake2::Blake2s;
    use criterion::Criterion;
    use primitives::signature::{schnorr::*, SignatureScheme};
    use rand::{self, Rng};

    type TweedleDeeSchnorrSig = SchnorrSignature<TweedleDee, Blake2s>;
    fn schnorr_signature_setup(c: &mut Criterion) {
        c.bench_function("SchnorrTweedleDee: Setup", move |b| {
            b.iter(|| {
                let mut rng = &mut rand::thread_rng();
                TweedleDeeSchnorrSig::setup(&mut rng).unwrap()
            })
        });
    }

    fn schnorr_signature_keygen(c: &mut Criterion) {
        let mut rng = &mut rand::thread_rng();
        let parameters = TweedleDeeSchnorrSig::setup(&mut rng).unwrap();

        c.bench_function("SchnorrTweedleDee: KeyGen", move |b| {
            b.iter(|| {
                let mut rng = &mut rand::thread_rng();
                TweedleDeeSchnorrSig::keygen(&parameters, &mut rng).unwrap()
            })
        });
    }

    fn schnorr_signature_sign(c: &mut Criterion) {
        let mut rng = &mut rand::thread_rng();
        let parameters = TweedleDeeSchnorrSig::setup(&mut rng).unwrap();
        let (_, sk) = TweedleDeeSchnorrSig::keygen(&parameters, &mut rng).unwrap();
        let message = [100u8; 128];

        c.bench_function("SchnorrTweedleDee: Sign", move |b| {
            b.iter(|| {
                let mut rng = &mut rand::thread_rng();
                TweedleDeeSchnorrSig::sign(&parameters, &sk, &message, &mut rng).unwrap()
            })
        });
    }

    fn schnorr_signature_verify(c: &mut Criterion) {
        let mut rng = &mut rand::thread_rng();
        let parameters = TweedleDeeSchnorrSig::setup(&mut rng).unwrap();
        let (pk, sk) = TweedleDeeSchnorrSig::keygen(&parameters, &mut rng).unwrap();
        let message = [100u8; 128];
        let signature = TweedleDeeSchnorrSig::sign(&parameters, &sk, &message, &mut rng).unwrap();

        c.bench_function("SchnorrTweedleDee: Verify", move |b| {
            b.iter(|| TweedleDeeSchnorrSig::verify(&parameters, &pk, &message, &signature).unwrap())
        });
    }

    fn schnorr_signature_randomize_pk(c: &mut Criterion) {
        let mut rng = &mut rand::thread_rng();
        let parameters = TweedleDeeSchnorrSig::setup(&mut rng).unwrap();
        let (pk, _) = TweedleDeeSchnorrSig::keygen(&parameters, &mut rng).unwrap();
        let randomness: [u8; 32] = rng.gen();

        c.bench_function("SchnorrTweedleDee: Randomize PubKey", move |b| {
            b.iter(|| {
                TweedleDeeSchnorrSig::randomize_public_key(&parameters, &pk, &randomness).unwrap()
            })
        });
    }

    fn schnorr_signature_randomize_signature(c: &mut Criterion) {
        let mut rng = &mut rand::thread_rng();
        let parameters = TweedleDeeSchnorrSig::setup(&mut rng).unwrap();
        let (_, sk) = TweedleDeeSchnorrSig::keygen(&parameters, &mut rng).unwrap();
        let randomness: [u8; 32] = rng.gen();
        let message = [100u8; 128];
        let signature = TweedleDeeSchnorrSig::sign(&parameters, &sk, &message, &mut rng).unwrap();

        c.bench_function("SchnorrTweedleDee: Randomize Signature", move |b| {
            b.iter(|| {
                TweedleDeeSchnorrSig::randomize_signature(&parameters, &signature, &randomness)
                    .unwrap()
            })
        });
    }
    criterion_group! {
        name = schnorr_sig_projective;
        config = Criterion::default().sample_size(20);
        targets = schnorr_signature_setup, schnorr_signature_keygen, schnorr_signature_sign,
                  schnorr_signature_verify, schnorr_signature_randomize_pk, schnorr_signature_randomize_signature
    }
}

mod field_impl {
    use algebra::{
        curves::tweedle::dee::DeeJacobian as TweedleDee, fields::tweedle::Fq as TweedleFq,
        UniformRand,
    };
    use criterion::Criterion;
    use primitives::{
        crh::poseidon::tweedle_dum::TweedleFqPoseidonHash,
        signature::{schnorr::field_based_schnorr::*, FieldBasedSignatureScheme},
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
}

use crate::{field_impl::field_based_schnorr_sig, projective::schnorr_sig_projective};
criterion_main!(schnorr_sig_projective, field_based_schnorr_sig);
