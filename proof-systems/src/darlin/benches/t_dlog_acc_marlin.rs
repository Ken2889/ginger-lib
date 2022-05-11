use algebra::{
    curves::tweedle::{dee::DeeJacobian, dum::DumJacobian},
    DualCycle, EndoMulCurve, Group,
};
use blake2::Blake2s;

use algebra::PrimeField;
use r1cs_core::{ConstraintSynthesizer, ConstraintSystemAbstract, SynthesisError};

use criterion::{BatchSize, BenchmarkId};
use criterion::{BenchmarkGroup, Criterion};
use r1cs_std::alloc::AllocGadget;
use r1cs_std::eq::EqGadget;
use r1cs_std::fields::fp::FpGadget;
use r1cs_std::fields::FieldGadget;
use r1cs_std::Assignment;

use rand::{rngs::OsRng, thread_rng};

use criterion::measurement::WallTime;
use digest::Digest;
use fiat_shamir::poseidon::TweedleFqPoseidonFSRng;
use fiat_shamir::FiatShamirRng;
use poly_commit::ipa_pc::{CommitterKey, VerifierKey};
use poly_commit::PCKey;
use proof_systems::darlin::accumulators::t_dlog::DualTDLogAccumulator;
use proof_systems::darlin::accumulators::Accumulator;
use proof_systems::darlin::t_dlog_acc_marlin::data_structures::VerifierKey as TDLogAccMarlinVerifierKey;
use proof_systems::darlin::t_dlog_acc_marlin::TDLogAccMarlin;
use rand_core::RngCore;
use std::time::{SystemTime, UNIX_EPOCH};

#[macro_use]
extern crate criterion;

#[macro_use]
extern crate bench_utils;

type G1 = DeeJacobian;
type G2 = DumJacobian;
type FS = TweedleFqPoseidonFSRng;
type D = Blake2s;

pub trait RandomCircuit {
    fn generate_random<R: RngCore>(num_constraints: usize, rng: &mut R) -> Self;
}

/// TestCircuit1c has (almost) full rank R1CS matrices A,B,C such that
///     d = max_{A,B,C} density = 2,
/// and keeps the sythesizer cost low (a single field mul per gate,
/// additions neglected).
#[derive(Clone)]
pub struct TestCircuit1c<F: PrimeField> {
    num_constraints: usize,
    a: Option<F>,
    b: Option<F>,
}

impl<F: PrimeField> RandomCircuit for TestCircuit1c<F> {
    fn generate_random<R: RngCore>(num_constraints: usize, rng: &mut R) -> Self {
        Self {
            num_constraints,
            a: Some(F::rand(rng)),
            b: Some(F::rand(rng)),
        }
    }
}

/// TestCircuit2c has (almost) full rank R1CS matrices A,B,C such that
///     d = max_{A,B,C} density = 1,
/// and demands the synthesizer to compute one field inversion
/// per every second gate.
#[derive(Clone)]
pub struct TestCircuit2c<F: PrimeField> {
    num_constraints: usize,
    a: Option<F>,
    b: Option<F>,
}

impl<F: PrimeField> RandomCircuit for TestCircuit2c<F> {
    fn generate_random<R: RngCore>(num_constraints: usize, rng: &mut R) -> Self {
        Self {
            num_constraints,
            a: Some(F::rand(rng)),
            b: Some(F::rand(rng)),
        }
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for TestCircuit1c<F> {
    fn generate_constraints<CS: ConstraintSystemAbstract<F>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let mut a_k_minus_2 = FpGadget::<F>::alloc_input(cs.ns(|| "alloc a0"), || {
            self.a.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let mut b_k_minus_2 = FpGadget::<F>::alloc(cs.ns(|| "alloc b0"), || {
            self.b.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let zero = FpGadget::<F>::zero(cs.ns(|| "alloc zero"))?;

        a_k_minus_2.enforce_not_equal(cs.ns(|| "a_0 != 0"), &zero)?;
        b_k_minus_2.enforce_not_equal(cs.ns(|| "b_0 != 0"), &zero)?;

        let mut a_k_minus_1 =
            FpGadget::<F>::alloc(cs.ns(|| "alloc a1"), || Ok(F::rand(&mut thread_rng())))?;

        let mut b_k_minus_1 =
            FpGadget::<F>::alloc(cs.ns(|| "alloc b1"), || Ok(F::rand(&mut thread_rng())))?;

        // Quadratic recursion which produces (almost) full rank matrices A,B,C
        // such that d = max_{A,B,C} R1CS density = 2:
        //  a[k] = (a[k-1] + a[k-2]) * (b[k-1] + b[k-2])
        //  b[k] = (b[k-1] + b[k-2]) * (a[k-1] + a[k-2])
        for k in 2..(self.num_constraints - 5) / 2 {
            let a_k = FpGadget::<F>::alloc(cs.ns(|| format!("alloc a_{}", k)), || {
                let term_1 = a_k_minus_1.value.get()? + &a_k_minus_2.value.get()?;
                let term_2 = b_k_minus_1.value.get()? + &b_k_minus_2.value.get()?;
                Ok(term_1 * &term_2)
            })?;

            let b_k = FpGadget::<F>::alloc(cs.ns(|| format!("alloc b_{}", k)), || {
                let term_1 = b_k_minus_1.value.get()? + &b_k_minus_2.value.get()?;
                let term_2 = a_k_minus_1.value.get()? + &a_k_minus_2.value.get()?;
                Ok(term_1 * &term_2)
            })?;

            let a_k_minus_1_plus_a_k_minus_2 =
                a_k_minus_1.add(cs.ns(|| format!("a_{} + a_{}", k - 1, k - 2)), &a_k_minus_2)?;

            let b_k_minus_1_plus_b_k_minus_2 =
                b_k_minus_1.add(cs.ns(|| format!("b_{} + b_{}", k - 1, k - 2)), &b_k_minus_2)?;

            a_k_minus_1_plus_a_k_minus_2.mul_equals(
                cs.ns(|| {
                    format!(
                        "(a_{} + a_{}) * (b_{} + b_{}) = a_{}",
                        k - 1,
                        k - 2,
                        k - 1,
                        k - 2,
                        k
                    )
                }),
                &b_k_minus_1_plus_b_k_minus_2,
                &a_k,
            )?;

            b_k_minus_1_plus_b_k_minus_2.mul_equals(
                cs.ns(|| {
                    format!(
                        "(b_{} + b_{}) * (a_{} + a_{}) = a_{}",
                        k - 1,
                        k - 2,
                        k - 1,
                        k - 2,
                        k
                    )
                }),
                &a_k_minus_1_plus_a_k_minus_2,
                &b_k,
            )?;

            a_k_minus_2 = a_k_minus_1;
            b_k_minus_2 = b_k_minus_1;
            a_k_minus_1 = a_k;
            b_k_minus_1 = b_k;
        }
        Ok(())
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for TestCircuit2c<F> {
    fn generate_constraints<CS: ConstraintSystemAbstract<F>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let mut a_k_minus_2 = FpGadget::<F>::alloc_input(cs.ns(|| "alloc a0"), || {
            self.a.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let mut b_k_minus_2 = FpGadget::<F>::alloc(cs.ns(|| "alloc b0"), || {
            self.b.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let zero = FpGadget::<F>::zero(cs.ns(|| "alloc zero"))?;

        a_k_minus_2.enforce_not_equal(cs.ns(|| "a_0 != 0"), &zero)?;
        b_k_minus_2.enforce_not_equal(cs.ns(|| "b_0 != 0"), &zero)?;

        let mut a_k_minus_1 =
            FpGadget::<F>::alloc(cs.ns(|| "alloc a1"), || Ok(F::rand(&mut thread_rng())))?;

        let mut b_k_minus_1 =
            FpGadget::<F>::alloc(cs.ns(|| "alloc b1"), || Ok(F::rand(&mut thread_rng())))?;

        // Quadratic recursion which produces (almost) full rank matrices A,B,C
        // such that max_{A,B,C} density = 2, and demands one field
        // inversion in every second gate:
        //  a[k-1] + a[k-2] = a[k] * (b[k-1] + b[k-2])      "new a = old a / old b"
        //  b[k] =  (b[k-1] + b[k-2]) * (a[k] + a[k-1])     "new b = old b * old a"
        for k in 2..(self.num_constraints - 5) / 2 {
            let a_k = FpGadget::<F>::alloc(cs.ns(|| format!("alloc a_{}", k)), || {
                let term_1 = a_k_minus_1.value.get()? + &a_k_minus_2.value.get()?;
                let term_2 = b_k_minus_1.value.get()? + &b_k_minus_2.value.get()?;
                Ok(term_1 * &(term_2.inverse().get()?))
            })?;

            let b_k = FpGadget::<F>::alloc(cs.ns(|| format!("alloc b_{}", k)), || {
                let term_1 = b_k_minus_1.value.get()? + &b_k_minus_2.value.get()?;
                let term_2 = a_k_minus_1.value.get()? + &a_k_minus_2.value.get()?;
                Ok(term_1 * &term_2)
            })?;

            let a_k_minus_1_plus_a_k_minus_2 =
                a_k_minus_1.add(cs.ns(|| format!("a_{} + a_{}", k - 1, k - 2)), &a_k_minus_2)?;

            let b_k_minus_1_plus_b_k_minus_2 =
                b_k_minus_1.add(cs.ns(|| format!("b_{} + b_{}", k - 1, k - 2)), &b_k_minus_2)?;

            a_k.mul_equals(
                cs.ns(|| {
                    format!(
                        "a_{} * (b_{} + b_{}) = (a_{} + a_{})",
                        k,
                        k - 1,
                        k - 2,
                        k - 1,
                        k - 2
                    )
                }),
                &b_k_minus_1_plus_b_k_minus_2,
                &a_k_minus_1_plus_a_k_minus_2,
            )?;

            b_k_minus_1_plus_b_k_minus_2.mul_equals(
                cs.ns(|| {
                    format!(
                        "(b_{} + b_{}) * (a_{} + a_{}) = b_{}",
                        k - 1,
                        k - 1,
                        k - 1,
                        k - 1,
                        k
                    )
                }),
                &a_k_minus_1_plus_a_k_minus_2,
                &b_k,
            )?;

            a_k_minus_2 = a_k_minus_1;
            b_k_minus_2 = b_k_minus_1;
            a_k_minus_1 = a_k;
            b_k_minus_1 = b_k;
        }

        Ok(())
    }
}

fn generate_keys<G1, G2, FS, D, CS>(
    num_constraints: usize,
    segment_size: usize,
    circuit: CS,
) -> (
    CommitterKey<G1>,
    VerifierKey<G1>,
    TDLogAccMarlinVerifierKey<G1, G2, FS>,
)
where
    G1: EndoMulCurve,
    G2: EndoMulCurve,
    G1: DualCycle<G2>,
    FS: FiatShamirRng,
    D: Digest,
    CS: ConstraintSynthesizer<G1::ScalarField>,
{
    let (pc_pk, pc_vk) =
        TDLogAccMarlin::<G1, G2, FS, D>::universal_setup(num_constraints, num_constraints, false)
            .unwrap();
    let pc_pk = pc_pk.trim(segment_size).unwrap();
    let pc_vk = pc_vk.trim(segment_size).unwrap();
    let index_vk =
        TDLogAccMarlin::<G1, G2, FS, D>::circuit_specific_setup(&pc_pk, circuit).unwrap();
    (pc_pk, pc_vk, index_vk)
}

fn bench_prover_single_prev_acc_helper<C1, C2>(
    group: &mut BenchmarkGroup<WallTime>,
    num_constraints: usize,
    segment_size: usize,
) where
    C1: ConstraintSynthesizer<<G1 as Group>::ScalarField> + RandomCircuit,
    C2: ConstraintSynthesizer<<G2 as Group>::ScalarField> + RandomCircuit,
{
    let mut rng = OsRng::default();

    let c_g1 = C1::generate_random(num_constraints, &mut rng);
    let (pc_pk_g1, _pc_vk_g1, index_vk_g1) =
        generate_keys::<G1, G2, FS, D, _>(num_constraints, segment_size, c_g1);

    let c_g2 = C2::generate_random(num_constraints, &mut rng);
    let (pc_pk_g2, _pc_vk_g2, index_vk_g2) =
        generate_keys::<G2, G1, FS, D, _>(num_constraints, segment_size, c_g2);

    add_to_trace!(
        || format!("****************{}*******************", num_constraints),
        || format!(
            "--->START TIMESTAMP: {:?}",
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs()
        )
    );

    group.bench_with_input(
        BenchmarkId::from_parameter(num_constraints),
        &num_constraints,
        |bn, _constraints| {
            bn.iter_batched(
                || {
                    let circ = C1::generate_random(num_constraints, &mut rng);

                    let dual_t_dlog_acc = DualTDLogAccumulator::<_, _, FS>::random_item(
                        &(
                            &(&index_vk_g2.index, &pc_pk_g2),
                            &(&index_vk_g1.index, &pc_pk_g1),
                        ),
                        &mut rng,
                    )
                    .unwrap();

                    (circ, dual_t_dlog_acc)
                },
                |(c, dual_t_dlog_acc)| {
                    TDLogAccMarlin::<G1, G2, FS, D>::prove(
                        &index_vk_g1,
                        &pc_pk_g1,
                        c,
                        &dual_t_dlog_acc,
                        false,
                        None,
                    )
                    .unwrap();
                },
                BatchSize::PerIteration,
            );
        },
    );
    add_to_trace!(
        || format!("****************{}*******************", num_constraints),
        || format!(
            "--->END TIMESTAMP: {:?}",
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs()
        )
    );
}

fn bench_prover_trivial_prev_acc_helper<C1, C2>(
    group: &mut BenchmarkGroup<WallTime>,
    num_constraints: usize,
    segment_size: usize,
) where
    C1: ConstraintSynthesizer<<G1 as Group>::ScalarField> + RandomCircuit,
    C2: ConstraintSynthesizer<<G2 as Group>::ScalarField> + RandomCircuit,
{
    let mut rng = OsRng::default();

    let c_g1 = C1::generate_random(num_constraints, &mut rng);
    let (pc_pk_g1, _pc_vk_g1, index_vk_g1) =
        generate_keys::<G1, G2, FS, D, _>(num_constraints, segment_size, c_g1);

    let c_g2 = C2::generate_random(num_constraints, &mut rng);
    let (pc_pk_g2, _pc_vk_g2, index_vk_g2) =
        generate_keys::<G2, G1, FS, D, _>(num_constraints, segment_size, c_g2);

    add_to_trace!(
        || format!("****************{}*******************", num_constraints),
        || format!(
            "--->START TIMESTAMP: {:?}",
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs()
        )
    );

    group.bench_with_input(
        BenchmarkId::from_parameter(num_constraints),
        &num_constraints,
        |bn, _constraints| {
            bn.iter_batched(
                || {
                    let circ = C1::generate_random(num_constraints, &mut rng);

                    let dual_t_dlog_acc = DualTDLogAccumulator::<_, _, FS>::trivial_item(
                        &(&(
                            &(&index_vk_g2.index, &pc_pk_g2),
                            &(&index_vk_g1.index, &pc_pk_g1),
                        )),
                    )
                    .unwrap();

                    (circ, dual_t_dlog_acc)
                },
                |(c, dual_t_dlog_acc)| {
                    TDLogAccMarlin::<G1, G2, FS, D>::prove(
                        &index_vk_g1,
                        &pc_pk_g1,
                        c,
                        &dual_t_dlog_acc,
                        false,
                        None,
                    )
                    .unwrap();
                },
                BatchSize::PerIteration,
            );
        },
    );
    add_to_trace!(
        || format!("****************{}*******************", num_constraints),
        || format!(
            "--->END TIMESTAMP: {:?}",
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs()
        )
    );
}

fn bench_prover_loop<F>(
    group: &mut BenchmarkGroup<WallTime>,
    num_constraints: &[usize],
    segment_size: &[usize],
    func: F,
) where
    F: Fn(&mut BenchmarkGroup<WallTime>, usize, usize),
{
    for (&nc, &ns) in num_constraints.iter().zip(segment_size.iter()) {
        func(group, nc, ns);
    }
}

fn bench_prover(c: &mut Criterion) {
    let num_constraints = (14..=21).map(|i| 2usize.pow(i)).collect::<Vec<_>>();
    let segment_sizes = vec![
        num_constraints.clone(),
        num_constraints.iter().map(|nc| nc / 2).collect::<Vec<_>>(),
    ];
    let segment_sizes_labels = vec!["segment_size full", "segment_size half"];

    for (segment_size, segment_size_label) in segment_sizes.iter().zip(segment_sizes_labels) {
        let mut group = c.benchmark_group(format!(
            "t_dlog_acc_marlin - circuit 1c - 1 prev acc - {} ",
            segment_size_label
        ));
        bench_prover_loop(
            &mut group,
            &num_constraints,
            segment_size,
            bench_prover_single_prev_acc_helper::<
                TestCircuit1c<<G1 as Group>::ScalarField>,
                TestCircuit1c<<G2 as Group>::ScalarField>,
            >,
        );
        group.finish();

        let mut group = c.benchmark_group(format!(
            "t_dlog_acc_marlin - circuit 1c - trivial prev acc - {} ",
            segment_size_label
        ));
        bench_prover_loop(
            &mut group,
            &num_constraints,
            segment_size,
            bench_prover_trivial_prev_acc_helper::<
                TestCircuit1c<<G1 as Group>::ScalarField>,
                TestCircuit1c<<G2 as Group>::ScalarField>,
            >,
        );
        group.finish();

        let mut group = c.benchmark_group(format!(
            "t_dlog_acc_marlin - circuit 2c - 1 prev acc - {} ",
            segment_size_label
        ));
        bench_prover_loop(
            &mut group,
            &num_constraints,
            segment_size,
            bench_prover_single_prev_acc_helper::<
                TestCircuit2c<<G1 as Group>::ScalarField>,
                TestCircuit2c<<G2 as Group>::ScalarField>,
            >,
        );
        group.finish();

        let mut group = c.benchmark_group(format!(
            "t_dlog_acc_marlin - circuit 2c - trivial prev acc - {} ",
            segment_size_label
        ));
        bench_prover_loop(
            &mut group,
            &num_constraints,
            segment_size,
            bench_prover_trivial_prev_acc_helper::<
                TestCircuit2c<<G1 as Group>::ScalarField>,
                TestCircuit2c<<G2 as Group>::ScalarField>,
            >,
        );
        group.finish();
    }
}

criterion_group!(
name = t_dlog_acc_marlin;
config = Criterion::default().sample_size(10);
targets = bench_prover
);

criterion_main!(t_dlog_acc_marlin);
