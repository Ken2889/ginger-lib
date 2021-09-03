use algebra::{AffineCurve, ToConstraintField, serialize::*};
use poly_commit::{
    PolynomialCommitment,
    ipa_pc::InnerProductArgPC
};
use proof_systems::darlin::{
    tests::{
        get_keys,
        final_darlin::generate_test_data as generate_final_darlin_test_data
    },
    pcd::PCD,
};
use digest::Digest;
use criterion::*;
use rand::SeedableRng;
use blake2::Blake2s;
use proof_systems::darlin::pcd::{GeneralPCD, DualPCDVerifierKey};
use rand_xorshift::XorShiftRng;
use rayon::prelude::*;
use proof_systems::darlin::proof_aggregator::get_accumulators;
use proof_systems::darlin::accumulators::dlog::DLogItemAccumulator;
use proof_systems::darlin::accumulators::ItemAccumulator;

fn bench_succinct_part_batch_verification<G1: AffineCurve, G2: AffineCurve, D: Digest>(
    c: &mut Criterion,
    bench_name: &str,
    segment_size: usize,
    num_constraints: Vec<usize>,
    num_proofs: usize,
)
    where
        G1: AffineCurve<BaseField = <G2 as AffineCurve>::ScalarField> + ToConstraintField<<G2 as AffineCurve>::ScalarField>,
        G2: AffineCurve<BaseField = <G1 as AffineCurve>::ScalarField> + ToConstraintField<<G1 as AffineCurve>::ScalarField>,
{
    let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);
    let mut group = c.benchmark_group(bench_name);

    //Generate DLOG keys
    let params_g1 = InnerProductArgPC::<G1, D>::setup(segment_size - 1).unwrap();
    let params_g2 = InnerProductArgPC::<G2, D>::setup(segment_size - 1).unwrap();
    println!("Key G1 size: {}", params_g1.comm_key.len());
    println!("Key G2 size: {}", params_g2.comm_key.len());

    let (
        _, verifier_key_g1,
        _, verifier_key_g2
    ) = get_keys::<_, _, D>(&params_g1, &params_g2);

    // Generate proofs and bench
    for num_constraints in num_constraints.into_iter() {

        let (final_darlin_pcd, index_vk) = generate_final_darlin_test_data::<G1, G2, D, _>(
            num_constraints - 1,
            segment_size,
            &params_g1,
            &params_g2,
            1,
            rng
        );

        println!("Proof size: {}", final_darlin_pcd[0].final_darlin_proof.serialized_size());
        println!("Vk size: {}", index_vk[0].serialized_size());

        // Collect PCDs and vks
        let pcds = vec![GeneralPCD::FinalDarlin(final_darlin_pcd[0].clone()); num_proofs];
        let vks = vec![index_vk[0].clone(); num_proofs];

        group.bench_with_input(BenchmarkId::from_parameter(num_constraints), &num_constraints, |bn, _num_constraints| {
            bn.iter(|| {
                pcds.as_slice()
                    .into_par_iter()
                    .zip(vks.as_slice())
                    .for_each(|(pcd, vk)| {
                        // recall that we use FinalDarlinVerifierKeys to handle
                        // polymorphic verification of final Darlin/simpleM arlin PCDs
                        let vk = DualPCDVerifierKey::<G1, G2, D>{
                            final_darlin_vk: &vk,
                            dlog_vks: (&verifier_key_g1, &verifier_key_g2)
                        };
                        // No need to trim the vk here to the specific segment size used
                        // to generate the proof for this pcd, as the IPA succinct_check
                        // function doesn't use vk.comm_key at all.
                        pcd.succinct_verify(&vk).unwrap();
                    });
            });
        });
    }
    group.finish();
}

fn bench_hard_part_batch_verification<G1: AffineCurve, G2: AffineCurve, D: Digest>(
    c: &mut Criterion,
    bench_name: &str,
    segment_size: usize,
    num_constraints: Vec<usize>,
    num_proofs: usize,
)
    where
        G1: AffineCurve<BaseField = <G2 as AffineCurve>::ScalarField> + ToConstraintField<<G2 as AffineCurve>::ScalarField>,
        G2: AffineCurve<BaseField = <G1 as AffineCurve>::ScalarField> + ToConstraintField<<G1 as AffineCurve>::ScalarField>,
{
    let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);
    let mut group = c.benchmark_group(bench_name);

    //Generate DLOG keys
    let params_g1 = InnerProductArgPC::<G1, D>::setup(segment_size - 1).unwrap();
    let params_g2 = InnerProductArgPC::<G2, D>::setup(segment_size - 1).unwrap();
    println!("Key G1 size: {}", params_g1.comm_key.len());
    println!("Key G2 size: {}", params_g2.comm_key.len());

    let (
        _, verifier_key_g1,
        _, verifier_key_g2
    ) = get_keys::<_, _, D>(&params_g1, &params_g2);

    // Generate proofs and bench
    for num_constraints in num_constraints.into_iter() {

        let (final_darlin_pcd, index_vk) = generate_final_darlin_test_data::<G1, G2, D, _>(
            num_constraints - 1,
            segment_size,
            &params_g1,
            &params_g2,
            1,
            rng
        );

        println!("Proof size: {}", final_darlin_pcd[0].final_darlin_proof.serialized_size());
        println!("Vk size: {}", index_vk[0].serialized_size());

        // Collect PCDs and vks
        let pcds = vec![GeneralPCD::FinalDarlin(final_darlin_pcd[0].clone()); num_proofs];
        let vks = vec![index_vk[0].clone(); num_proofs];

        // Get accumulators from pcds
        let (accs_g1, accs_g2) = get_accumulators::<G1, G2, D>(&pcds, &vks, &verifier_key_g1, &verifier_key_g2).unwrap();

        group.bench_with_input(BenchmarkId::from_parameter(num_constraints), &num_constraints, |bn, _num_constraints| {
            bn.iter(|| {
                // Verify accumulators (hard part)
                assert!(
                    DLogItemAccumulator::<G1, D>::check_items(
                        &verifier_key_g1, &accs_g1, rng
                    ).unwrap()
                        &&
                    DLogItemAccumulator::<G2, D>::check_items(
                        &verifier_key_g2, &accs_g2, rng
                    ).unwrap()
                );
            });
        });
    }
    group.finish();
}

// We want to bench the  hard part of the batch verifier, varying
// segment_size and circuit size (num_constraints), and measuring
// the time taken, proof size and vk size.
// Segment size: [1 << 14, ... , 1 << 18]
// Num constraints: [1 << 10, ..., 1 << 20]
fn bench_succinct_part_batch_verification_tweedle(c: &mut Criterion) {

    use algebra::curves::tweedle::{
        dee::Affine as TweedleDee,
        dum::Affine as TweedleDum,
    };

    let num_proofs = 100;
    let num_constraints = (10..=20).map(|pow| 1 << pow).collect::<Vec<_>>();

    for log_segment_size in 14..=18 {
        bench_succinct_part_batch_verification::<TweedleDee, TweedleDum, Blake2s>(
            c,
            format!("succinct_part, tweedle-dee, segment_size = 1 << {}, num_constraints", log_segment_size).as_str(),
            1 << log_segment_size,
            num_constraints.clone(),
            num_proofs
        );
    }
}

// We want to bench the hard part of the batch verifier, varying
// segment_size and circuit size (num_constraints), and measuring
// the time taken, proof size and vk size.
// Segment size: [1 << 14, ... , 1 << 18]
// Num constraints: [1 << 10, ..., 1 << 20]
fn bench_hard_part_batch_verification_tweedle(c: &mut Criterion) {

    use algebra::curves::tweedle::{
        dee::Affine as TweedleDee,
        dum::Affine as TweedleDum,
    };

    let num_proofs = 100;
    let num_constraints = (10..=20).map(|pow| 1 << pow).collect::<Vec<_>>();

    for log_segment_size in 14..=18 {
        bench_hard_part_batch_verification::<TweedleDee, TweedleDum, Blake2s>(
            c,
            format!("hard_part, tweedle-dee, segment_size = 1 << {}, num_constraints", log_segment_size).as_str(),
            1 << log_segment_size,
            num_constraints.clone(),
            num_proofs
        );
    }
}

criterion_group!(
name = batch_verification;
config = Criterion::default().sample_size(10);
targets = bench_succinct_part_batch_verification_tweedle, bench_hard_part_batch_verification_tweedle
);

criterion_main!(batch_verification);