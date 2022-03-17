use algebra::{serialize::*, Group, Curve, ToConstraintField};
use blake2::Blake2s;
use criterion::*;
use digest::Digest;
use poly_commit::{ipa_pc::InnerProductArgPC, PolynomialCommitment};
use proof_systems::darlin::accumulators::dlog::DLogItemAccumulator;
use proof_systems::darlin::accumulators::ItemAccumulator;
use proof_systems::darlin::pcd::GeneralPCD;
use proof_systems::darlin::proof_aggregator::batch_verify_proofs;
use proof_systems::darlin::proof_aggregator::get_accumulators;
use proof_systems::darlin::tests::final_darlin::generate_test_data as generate_final_darlin_test_data;
use rand::thread_rng;
use rand::SeedableRng;
use rand_xorshift::XorShiftRng;

fn bench_succinct_part_batch_verification<G1: Curve, G2: Curve, D: Digest + 'static>(
    c: &mut Criterion,
    bench_name: &str,
    segment_size: usize,
    num_constraints: Vec<usize>,
    num_proofs: usize,
) where
    G1: Curve<BaseField = <G2 as Group>::ScalarField>
        + ToConstraintField<<G2 as Group>::ScalarField>,
    G2: Curve<BaseField = <G1 as Group>::ScalarField>
        + ToConstraintField<<G1 as Group>::ScalarField>,
{
    let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);
    let mut group = c.benchmark_group(bench_name);

    //Generate DLOG keys
    let (committer_key_g1, verifier_key_g1) = InnerProductArgPC::<G1, D>::setup(segment_size - 1).unwrap();
    let (committer_key_g2, verifier_key_g2) = InnerProductArgPC::<G2, D>::setup(segment_size - 1).unwrap();

    // Generate proofs and bench
    for num_constraints in num_constraints.into_iter() {
        let (final_darlin_pcd, index_vk) = generate_final_darlin_test_data::<G1, G2, D, _>(
            num_constraints - 1,
            segment_size,
            (&committer_key_g1, &verifier_key_g1),
            (&committer_key_g2, &verifier_key_g2),
            1,
            rng,
        );

        println!(
            "Proof size: {}",
            final_darlin_pcd[0].final_darlin_proof.serialized_size()
        );
        println!("Vk size: {}", index_vk[0].serialized_size());

        // Collect PCDs and vks
        let pcds = vec![GeneralPCD::FinalDarlin(final_darlin_pcd[0].clone()); num_proofs];
        let vks = vec![index_vk[0].clone(); num_proofs];

        group.bench_with_input(
            BenchmarkId::from_parameter(num_constraints),
            &num_constraints,
            |bn, _num_constraints| {
                bn.iter(|| {
                    let _ = get_accumulators::<G1, G2, D>(
                        pcds.as_slice(),
                        vks.as_slice(),
                        &verifier_key_g1,
                        &verifier_key_g2,
                    )
                    .unwrap();
                });
            },
        );
    }
    group.finish();
}

fn bench_hard_part_batch_verification<G1: Curve, G2: Curve, D: Digest + 'static>(
    c: &mut Criterion,
    bench_name: &str,
    segment_size: usize,
    num_constraints: Vec<usize>,
    num_proofs: usize,
) where
    G1: Curve<BaseField = <G2 as Group>::ScalarField>
        + ToConstraintField<<G2 as Group>::ScalarField>,
    G2: Curve<BaseField = <G1 as Group>::ScalarField>
        + ToConstraintField<<G1 as Group>::ScalarField>,
{
    let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);
    let mut group = c.benchmark_group(bench_name);

    //Generate DLOG keys
    let (committer_key_g1, verifier_key_g1) = InnerProductArgPC::<G1, D>::setup(segment_size - 1).unwrap();
    let (committer_key_g2, verifier_key_g2) = InnerProductArgPC::<G2, D>::setup(segment_size - 1).unwrap();

    // Generate proofs and bench
    for num_constraints in num_constraints.into_iter() {
        let (final_darlin_pcd, index_vk) = generate_final_darlin_test_data::<G1, G2, D, _>(
            num_constraints - 1,
            segment_size,
            (&committer_key_g1, &verifier_key_g1),
            (&committer_key_g2, &verifier_key_g2),
            1,
            rng,
        );

        println!(
            "Proof size: {}",
            final_darlin_pcd[0].final_darlin_proof.serialized_size()
        );
        println!("Vk size: {}", index_vk[0].serialized_size());

        // Collect PCDs and vks
        let pcds = vec![GeneralPCD::FinalDarlin(final_darlin_pcd[0].clone()); num_proofs];
        let vks = vec![index_vk[0].clone(); num_proofs];

        // Get accumulators from pcds
        let (accs_g1, accs_g2) =
            get_accumulators::<G1, G2, D>(&pcds, &vks, &verifier_key_g1, &verifier_key_g2).unwrap();

        group.bench_with_input(
            BenchmarkId::from_parameter(num_constraints),
            &num_constraints,
            |bn, _num_constraints| {
                bn.iter(|| {
                    // Verify accumulators (hard part)
                    assert!(
                        DLogItemAccumulator::<G1, D>::check_items(&verifier_key_g1, &accs_g1, rng)
                            .unwrap()
                            && DLogItemAccumulator::<G2, D>::check_items(
                                &verifier_key_g2,
                                &accs_g2,
                                rng
                            )
                            .unwrap()
                    );
                });
            },
        );
    }
    group.finish();
}

fn bench_batch_verification_complete<G1: Curve, G2: Curve, D: Digest + 'static>(
    c: &mut Criterion,
    bench_name: &str,
    segment_size: usize,
    num_constraints: Vec<usize>,
    num_proofs: usize,
) where
    G1: Curve<BaseField = <G2 as Group>::ScalarField>
        + ToConstraintField<<G2 as Group>::ScalarField>,
    G2: Curve<BaseField = <G1 as Group>::ScalarField>
        + ToConstraintField<<G1 as Group>::ScalarField>,
{
    let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);
    let mut group = c.benchmark_group(bench_name);

    //Generate DLOG keys
    let (committer_key_g1, verifier_key_g1) = InnerProductArgPC::<G1, D>::setup(segment_size - 1).unwrap();
    let (committer_key_g2, verifier_key_g2) = InnerProductArgPC::<G2, D>::setup(segment_size - 1).unwrap();

    // Generate proofs and bench
    for num_constraints in num_constraints.into_iter() {
        let (final_darlin_pcd, index_vk) = generate_final_darlin_test_data::<G1, G2, D, _>(
            num_constraints - 1,
            segment_size,
            (&committer_key_g1, &verifier_key_g1),
            (&committer_key_g2, &verifier_key_g2),
            1,
            rng,
        );

        println!(
            "Proof size: {}",
            final_darlin_pcd[0].final_darlin_proof.serialized_size()
        );
        println!("Vk size: {}", index_vk[0].serialized_size());

        // Collect PCDs and vks
        let pcds = vec![GeneralPCD::FinalDarlin(final_darlin_pcd[0].clone()); num_proofs];
        let vks = vec![index_vk[0].clone(); num_proofs];

        group.bench_with_input(
            BenchmarkId::from_parameter(num_constraints),
            &num_constraints,
            |bn, _num_constraints| {
                bn.iter(|| {
                    assert!(batch_verify_proofs::<G1, G2, D, _>(
                        pcds.as_slice(),
                        vks.as_slice(),
                        &verifier_key_g1,
                        &verifier_key_g2,
                        &mut thread_rng()
                    )
                    .unwrap());
                });
            },
        );
    }
    group.finish();
}

// We want to bench the batch verifier, varying
// segment_size and circuit size (num_constraints), and measuring
// the time taken, proof size and vk size.
// Segment size: [1 << 14, ... , 1 << 18]
// Num constraints: [1 << 10, ..., 1 << 20]
fn bench_batch_verification_complete_tweedle(c: &mut Criterion) {
    use algebra::curves::tweedle::{dee::DeeJacobian as TweedleDee, dum::DumJacobian as TweedleDum};

    let num_proofs = 100;
    let num_constraints = (10..=20).map(|pow| 1 << pow).collect::<Vec<_>>();

    for log_segment_size in 14..=18 {
        bench_batch_verification_complete::<TweedleDee, TweedleDum, Blake2s>(
            c,
            format!(
                "tweedle-dee, segment_size = 1 << {}, num_constraints",
                log_segment_size
            )
            .as_str(),
            1 << log_segment_size,
            num_constraints.clone(),
            num_proofs,
        );
    }
}

// We want to bench the  hard part of the batch verifier, varying
// segment_size and circuit size (num_constraints), and measuring
// the time taken, proof size and vk size.
// Segment size: [1 << 14, ... , 1 << 18]
// Num constraints: [1 << 10, ..., 1 << 20]
fn bench_succinct_part_batch_verification_tweedle(c: &mut Criterion) {
    use algebra::curves::tweedle::{dee::DeeJacobian as TweedleDee, dum::DumJacobian as TweedleDum};

    let num_proofs = 100;
    let num_constraints = (10..=20).map(|pow| 1 << pow).collect::<Vec<_>>();

    for log_segment_size in 14..=18 {
        bench_succinct_part_batch_verification::<TweedleDee, TweedleDum, Blake2s>(
            c,
            format!(
                "succinct_part, tweedle-dee, segment_size = 1 << {}, num_constraints",
                log_segment_size
            )
            .as_str(),
            1 << log_segment_size,
            num_constraints.clone(),
            num_proofs,
        );
    }
}

// We want to bench the hard part of the batch verifier, varying
// segment_size and circuit size (num_constraints), and measuring
// the time taken, proof size and vk size.
// Segment size: [1 << 14, ... , 1 << 18]
// Num constraints: [1 << 10, ..., 1 << 20]
fn bench_hard_part_batch_verification_tweedle(c: &mut Criterion) {
    use algebra::curves::tweedle::{dee::DeeJacobian as TweedleDee, dum::DumJacobian as TweedleDum};

    let num_proofs = 100;
    let num_constraints = (10..=20).map(|pow| 1 << pow).collect::<Vec<_>>();

    for log_segment_size in 14..=18 {
        bench_hard_part_batch_verification::<TweedleDee, TweedleDum, Blake2s>(
            c,
            format!(
                "hard_part, tweedle-dee, segment_size = 1 << {}, num_constraints",
                log_segment_size
            )
            .as_str(),
            1 << log_segment_size,
            num_constraints.clone(),
            num_proofs,
        );
    }
}

criterion_group!(
name = batch_verification;
config = Criterion::default().sample_size(10);
targets = bench_batch_verification_complete_tweedle, bench_succinct_part_batch_verification_tweedle, bench_hard_part_batch_verification_tweedle
);

criterion_main!(batch_verification);
