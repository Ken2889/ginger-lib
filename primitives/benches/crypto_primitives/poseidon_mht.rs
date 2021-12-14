#[macro_use]
extern crate criterion;

use criterion::{BatchSize, BenchmarkId, Criterion};
use algebra::{UniformRand, fields::tweedle::Fr as FieldElement};
use primitives::{FieldBasedMerkleTree, crh::{TweedleFrPoseidonHash as FieldHash, TweedleFrBatchPoseidonHash as BatchFieldHash}, merkle_tree::{
        TWEEDLE_DEE_MHT_POSEIDON_PARAMETERS as MHT_POSEIDON_PARAMETERS, FieldBasedMerkleTreeParameters,
        BatchFieldBasedMerkleTreeParameters, FieldBasedMerkleTreePrecomputedZeroConstants,
        FieldBasedOptimizedMHT
    }};
use rand::SeedableRng;
use rand_xorshift::XorShiftRng;

#[derive(Clone, Debug)]
struct FieldBasedMerkleTreeParams;
impl FieldBasedMerkleTreeParameters for FieldBasedMerkleTreeParams {
    type Data = FieldElement;
    type H = FieldHash;
    const MERKLE_ARITY: usize = 2;
    const ZERO_NODE_CST: Option<FieldBasedMerkleTreePrecomputedZeroConstants<'static, Self::H>> =
        Some(MHT_POSEIDON_PARAMETERS);
}
impl BatchFieldBasedMerkleTreeParameters for FieldBasedMerkleTreeParams {
    type BH = BatchFieldHash;
}

const BENCH_HEIGHT: usize = 11;

fn _bench_in_memory_optimized_poseidon_mht(
    c: &mut Criterion,
    bench_name: &str,
    num_leaves: usize,
    starting_non_zero_idx: Option<usize>,
) {
    let rng = &mut XorShiftRng::seed_from_u64(1231275789u64);

    c.bench_function(
        bench_name,
        move |b| {
            b.iter_batched(
                || {
                    let mut leaves = Vec::with_capacity(num_leaves);

                    // If starting_non_zero_idx is some, use phantom leaves up to 'starting_non_zero_idx',
                    // and then random leaves up to 'num_leaves'
                    if let Some(idx) = starting_non_zero_idx {
                        leaves.append(&mut (0..idx).map(|_| FieldBasedMerkleTreeParams::ZERO_NODE_CST.unwrap().nodes[0]).collect::<Vec<_>>());
                        leaves.append(&mut (idx..num_leaves).map(|_| FieldElement::rand(rng)).collect::<Vec<_>>());
                    } 
                    // Otherwise just use random leaves up to 'num_leaves'
                    else {
                        leaves.append(&mut (0..num_leaves).map(|_| FieldElement::rand(rng)).collect::<Vec<_>>());
                    };
                    
                    // Create tree
                    let tree = FieldBasedOptimizedMHT::<FieldBasedMerkleTreeParams>::init(
                        BENCH_HEIGHT,
                        num_leaves
                    ).unwrap();
                    (leaves, tree)
                },
                // Bench append and finalize
                |(leaves, mut tree)| {
                    leaves.into_iter().for_each(|leaf| { tree.append(leaf).unwrap(); });
                    tree.finalize_in_place().unwrap();
                },
                BatchSize::PerIteration,
            );
        },
    );
}

/// Let's create a full tree with different processing_step sizes and bench the total time
fn batch_poseidon_mht_tune_processing_step(c: &mut Criterion) {
    let num_leaves = 1 << BENCH_HEIGHT;

    let mut processing_steps = Vec::with_capacity(BENCH_HEIGHT);
    for i in 0..=BENCH_HEIGHT {
        processing_steps.push(1 << i);
    }

    let rng = &mut XorShiftRng::seed_from_u64(1231275789u64);

    let mut group = c.benchmark_group(format!(
        "tune processing_step_size for a tree of height {}",
        BENCH_HEIGHT
    ));

    for processing_step in processing_steps.iter() {
        group.bench_with_input(
            BenchmarkId::from_parameter(processing_step),
            processing_step,
            |b, _processing_step| {
                b.iter_batched(
                    || {
                        // Generate random leaves    
                        let leaves = (0..num_leaves).map(|_| FieldElement::rand(rng)).collect::<Vec<_>>();
                        
                        // Create tree
                        let tree = FieldBasedOptimizedMHT::<FieldBasedMerkleTreeParams>::init(
                            BENCH_HEIGHT,
                            *processing_step
                        ).unwrap();
                        (leaves, tree)
                    },
                    // Bench append and finalize
                    |(leaves, mut tree)| {
                        leaves.into_iter().for_each(|leaf| { tree.append(leaf).unwrap(); });
                        tree.finalize_in_place().unwrap();
                    },
                    BatchSize::PerIteration,
                );
            },
        );
    }
}

fn bench_in_memory_optimized_poseidon_mht(c: &mut Criterion) {
    let num_leaves = 1 << BENCH_HEIGHT;

    _bench_in_memory_optimized_poseidon_mht(c, "Append 1/4 of the total supported leaves", num_leaves/4, None);
    _bench_in_memory_optimized_poseidon_mht(c, "Append 1/2 of the total supported leaves", num_leaves/2, None);
    _bench_in_memory_optimized_poseidon_mht(c, "Append 3/4 of the total supported leaves", 3 * num_leaves/4, None);
    _bench_in_memory_optimized_poseidon_mht(c, "Append the total supported leaves", num_leaves, None);
    _bench_in_memory_optimized_poseidon_mht(c, "Append 2/3 of total supported leaves, but first 1/3 is empty", num_leaves, Some(num_leaves/3));

}

criterion_group! {
    name = in_memory_optimized_poseidon_mht_benches;
    config = Criterion::default().sample_size(100);
    targets = bench_in_memory_optimized_poseidon_mht, batch_poseidon_mht_tune_processing_step
}

criterion_main!(in_memory_optimized_poseidon_mht_benches);
