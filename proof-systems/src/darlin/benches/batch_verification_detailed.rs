use algebra::{serialize::*, Group, ToConstraintField};
use blake2::Blake2s;
use criterion::*;
use digest::Digest;
use fiat_shamir::chacha20::FiatShamirChaChaRng;
use fiat_shamir::FiatShamirRng;
use poly_commit::{
    ipa_pc::{IPACurve, InnerProductArgPC},
    PolynomialCommitment,
};
use proof_systems::darlin::accumulators::dlog::DLogAccumulator;
use proof_systems::darlin::accumulators::Accumulator;
use proof_systems::darlin::pcd::GeneralPCD;
use proof_systems::darlin::proof_aggregator::batch_verify_proofs;
use proof_systems::darlin::proof_aggregator::get_accumulators;
use proof_systems::darlin::tests::final_darlin::generate_test_data as generate_final_darlin_test_data;
use rand::thread_rng;
use rand::SeedableRng;
use rand_xorshift::XorShiftRng;

fn bench_succinct_part_batch_verification<
    G1: IPACurve,
    G2: IPACurve,
    D: Digest + 'static,
    FS: FiatShamirRng + 'static,
>(
    c: &mut Criterion,
    bench_name: &str,
    segment_size: usize,
    num_constraints: Vec<usize>,
    num_proofs: usize,
) where
    G1: IPACurve + ToConstraintField<<G1 as Group>::BaseField>,
    G2: IPACurve + ToConstraintField<<G2 as Group>::BaseField>,
    G1: DualCycle<G2>,
{
    let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);
    let mut group = c.benchmark_group(bench_name);

    //Generate DLOG keys
    let (committer_key_g1, verifier_key_g1) =
        InnerProductArgPC::<G1, FS>::setup::<D>(segment_size - 1).unwrap();
    let (committer_key_g2, verifier_key_g2) =
        InnerProductArgPC::<G2, FS>::setup::<D>(segment_size - 1).unwrap();

    // Generate proofs and bench
    for num_constraints in num_constraints.into_iter() {
        let (final_darlin_pcd, index_vk) = generate_final_darlin_test_data::<D, G1, G2, FS, _>(
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
                    let _ = get_accumulators::<G1, G2, FS>(
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

fn bench_hard_part_batch_verification<
    G1: IPACurve,
    G2: IPACurve,
    D: Digest + 'static,
    FS: FiatShamirRng + 'static,
>(
    c: &mut Criterion,
    bench_name: &str,
    segment_size: usize,
    num_constraints: Vec<usize>,
    num_proofs: usize,
) where
    G1: IPACurve + ToConstraintField<<G1 as Group>::BaseField>,
    G2: IPACurve + ToConstraintField<<G2 as Group>::BaseField>,
    G1: DualCycle<G2>,
{
    let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);
    let mut group = c.benchmark_group(bench_name);

    //Generate DLOG keys
    let (committer_key_g1, verifier_key_g1) =
        InnerProductArgPC::<G1, FS>::setup::<D>(segment_size - 1).unwrap();
    let (committer_key_g2, verifier_key_g2) =
        InnerProductArgPC::<G2, FS>::setup::<D>(segment_size - 1).unwrap();

    // Generate proofs and bench
    for num_constraints in num_constraints.into_iter() {
        let (final_darlin_pcd, index_vk) = generate_final_darlin_test_data::<D, G1, G2, FS, _>(
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
            get_accumulators::<G1, G2, FS>(&pcds, &vks, &verifier_key_g1, &verifier_key_g2)
                .unwrap();

        group.bench_with_input(
            BenchmarkId::from_parameter(num_constraints),
            &num_constraints,
            |bn, _num_constraints| {
                bn.iter(|| {
                    // Verify accumulators (hard part)
                    assert!(
                        DLogAccumulator::<G1, FS>::check_items_optimized(
                            &verifier_key_g1,
                            &accs_g1,
                            rng
                        )
                        .unwrap()
                            && DLogAccumulator::<G2, FS>::check_items_optimized(
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

fn bench_batch_verification_complete<
    G1: IPACurve,
    G2: IPACurve,
    D: Digest + 'static,
    FS: FiatShamirRng + 'static,
>(
    c: &mut Criterion,
    bench_name: &str,
    segment_size: usize,
    num_constraints: Vec<usize>,
    num_proofs: usize,
) where
    G1: IPACurve + ToConstraintField<<G1 as Group>::BaseField>,
    G2: IPACurve + ToConstraintField<<G2 as Group>::BaseField>,
    G1: DualCycle<G2>,
{
    let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);
    let mut group = c.benchmark_group(bench_name);

    //Generate DLOG keys
    let (committer_key_g1, verifier_key_g1) =
        InnerProductArgPC::<G1, FS>::setup::<D>(segment_size - 1).unwrap();
    let (committer_key_g2, verifier_key_g2) =
        InnerProductArgPC::<G2, FS>::setup::<D>(segment_size - 1).unwrap();

    // Generate proofs and bench
    for num_constraints in num_constraints.into_iter() {
        let (final_darlin_pcd, index_vk) = generate_final_darlin_test_data::<D, G1, G2, FS, _>(
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
                    assert!(batch_verify_proofs::<G1, G2, FS, _>(
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
    use algebra::curves::tweedle::{
        dee::DeeJacobian as TweedleDee, dum::DumJacobian as TweedleDum,
    };

    let num_proofs = 100;
    let num_constraints = (10..=20).map(|pow| 1 << pow).collect::<Vec<_>>();

    for log_segment_size in 14..=18 {
        bench_batch_verification_complete::<
            TweedleDee,
            TweedleDum,
            Blake2s,
            FiatShamirChaChaRng<Blake2s>,
        >(
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
    use algebra::curves::tweedle::{
        dee::DeeJacobian as TweedleDee, dum::DumJacobian as TweedleDum,
    };

    let num_proofs = 100;
    let num_constraints = (10..=20).map(|pow| 1 << pow).collect::<Vec<_>>();

    for log_segment_size in 14..=18 {
        bench_succinct_part_batch_verification::<
            TweedleDee,
            TweedleDum,
            Blake2s,
            FiatShamirChaChaRng<Blake2s>,
        >(
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
    use algebra::curves::tweedle::{
        dee::DeeJacobian as TweedleDee, dum::DumJacobian as TweedleDum,
    };

    let num_proofs = 100;
    let num_constraints = (10..=20).map(|pow| 1 << pow).collect::<Vec<_>>();

    for log_segment_size in 14..=18 {
        bench_hard_part_batch_verification::<
            TweedleDee,
            TweedleDum,
            Blake2s,
            FiatShamirChaChaRng<Blake2s>,
        >(
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
