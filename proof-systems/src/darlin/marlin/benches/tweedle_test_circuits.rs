use algebra::{curves::tweedle::dee::DeeJacobian, UniformRand};
use blake2::{Blake2s, Digest};
use marlin::*;
use poly_commit::PolynomialCommitment;
use poly_commit::chacha20::FiatShamirChaChaRng;
use poly_commit::{ipa_pc::InnerProductArgPC, DomainExtendedPolynomialCommitment, PCParameters};

use algebra::{PrimeField, EndoMulCurve};
use primitives::TweedleFqPoseidonSponge;
use r1cs_core::{ConstraintSynthesizer, ConstraintSystemAbstract, SynthesisError};

use criterion::Criterion;
use criterion::{BatchSize, BenchmarkId};
use r1cs_std::alloc::AllocGadget;
use r1cs_std::eq::EqGadget;
use r1cs_std::fields::fp::FpGadget;
use r1cs_std::fields::FieldGadget;
use r1cs_std::Assignment;

use rand::{rngs::OsRng, thread_rng};

use std::time::{SystemTime, UNIX_EPOCH};

#[macro_use]
extern crate criterion;

#[macro_use]
extern crate bench_utils;

type IPAPCChaCha =
    DomainExtendedPolynomialCommitment<DeeJacobian, InnerProductArgPC<DeeJacobian, FiatShamirChaChaRng<Blake2s>>>;
type IPAPCPoseidon =
    DomainExtendedPolynomialCommitment<DeeJacobian, InnerProductArgPC<DeeJacobian, TweedleFqPoseidonSponge>>;

/// TestCircuit1a has (almost) full rank R1CS matrices A,B,C such that
///     d = max_{A,B,C} density = 1,
/// and keeps the sythesizer cost low (a single field mul per gate).
#[derive(Clone)]
pub struct TestCircuit1a<F: PrimeField> {
    num_constraints: usize,
    /// two public inputs
    a: Option<F>,
    b: Option<F>,
}

/// TestCircuit1b has (almost) full rank R1CS matrices A,B,C such that
///     d = max_{A,B,C} density = 1.5,
/// and keeps the sythesizer cost low (a single field mul per gate,
/// additions neglected).
#[derive(Clone)]
pub struct TestCircuit1b<F: PrimeField> {
    num_constraints: usize,
    a: Option<F>,
    b: Option<F>,
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

/// TestCircuit2a has (almost) full rank R1CS matrices A,B,C such that
///     d = max_{A,B,C} density = 1,
/// and demands the synthesizer to compute one field inversion
/// per every second gate.
#[derive(Clone)]
pub struct TestCircuit2a<F: PrimeField> {
    num_constraints: usize,
    a: Option<F>,
    b: Option<F>,
}

/// TestCircuit2a has (almost) full rank R1CS matrices A,B,C such that
///     d = max_{A,B,C} density = 1.5,
/// and demands the synthesizer to compute one field inversion
/// per every second gate.
#[derive(Clone)]
pub struct TestCircuit2b<F: PrimeField> {
    num_constraints: usize,
    a: Option<F>,
    b: Option<F>,
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

impl<F: PrimeField> ConstraintSynthesizer<F> for TestCircuit1a<F> {
    fn generate_constraints<CS: ConstraintSystemAbstract<F>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let mut a_k_minus_1 = FpGadget::<F>::alloc_input(cs.ns(|| "alloc a"), || {
            self.a.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let mut b_k_minus_1 = FpGadget::<F>::alloc_input(cs.ns(|| "alloc b"), || {
            self.b.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let zero = FpGadget::<F>::zero(cs.ns(|| "alloc zero"))?;

        // enforce both initial values as non-zero
        a_k_minus_1.enforce_not_equal(cs.ns(|| "a_0 != 0"), &zero)?;
        b_k_minus_1.enforce_not_equal(cs.ns(|| "b_0 != 0"), &zero)?;

        // Quadratic recursion which produces (almost) full rank matrices A,B,C
        // of R1CS density d = 1:
        //  a[k] = a[k-1]*b[k-1]
        //  b[k] = b[k-1]*a[k-1]
        for k in 0..(self.num_constraints - 5) / 2 {
            let a_k = FpGadget::<F>::alloc(cs.ns(|| format!("alloc a_{}", k)), || {
                Ok(a_k_minus_1.value.get()? * &b_k_minus_1.value.get()?)
            })?;

            let b_k = FpGadget::<F>::alloc(cs.ns(|| format!("alloc b_{}", k)), || {
                Ok(b_k_minus_1.value.get()? * &a_k_minus_1.value.get()?)
            })?;

            a_k_minus_1.mul_equals(
                cs.ns(|| format!("a_{} * b_{} = a_{}", k - 1, k - 1, k)),
                &b_k_minus_1,
                &a_k,
            )?;

            b_k_minus_1.mul_equals(
                cs.ns(|| format!("b_{} * a_{} = b_{}", k - 1, k - 1, k)),
                &a_k_minus_1,
                &b_k,
            )?;

            a_k_minus_1 = a_k;
            b_k_minus_1 = b_k;
        }

        Ok(())
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for TestCircuit1b<F> {
    fn generate_constraints<CS: ConstraintSystemAbstract<F>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let mut a_k_minus_2 = FpGadget::<F>::alloc_input(cs.ns(|| "alloc a0"), || {
            self.a.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let b_k_minus_2 = FpGadget::<F>::alloc_input(cs.ns(|| "alloc b0"), || {
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
        // such that d = max_{A,B,C} R1CS density  = 1.5:
        //  a[k] = (a[k-1] + a[k-2]) * b[k-1]
        //  b[k] = b[k-1] * (a[k-1] + a[k-2])
        for k in 2..(self.num_constraints - 5) / 2 {
            let a_k = FpGadget::<F>::alloc(cs.ns(|| format!("alloc a_{}", k)), || {
                let term_1 = a_k_minus_1.value.get()? + &a_k_minus_2.value.get()?;
                let term_2 = b_k_minus_1.value.get()?;
                Ok(term_1 * &term_2)
            })?;

            let b_k = FpGadget::<F>::alloc(cs.ns(|| format!("alloc b_{}", k)), || {
                let term_1 = b_k_minus_1.value.get()?;
                let term_2 = a_k_minus_1.value.get()? + &a_k_minus_2.value.get()?;
                Ok(term_1 * &term_2)
            })?;

            let a_k_minus_1_plus_a_k_minus_2 =
                a_k_minus_1.add(cs.ns(|| format!("a_{} + a_{}", k - 1, k - 2)), &a_k_minus_2)?;

            a_k_minus_1_plus_a_k_minus_2.mul_equals(
                cs.ns(|| format!("(a_{} + a_{}) * b_{} = a_{}", k - 1, k - 2, k - 1, k)),
                &b_k_minus_1,
                &a_k,
            )?;

            b_k_minus_1.mul_equals(
                cs.ns(|| format!("b_{} * (a_{} + a_{}) = b_{}", k - 1, k - 1, k - 2, k)),
                &a_k_minus_1_plus_a_k_minus_2,
                &b_k,
            )?;

            a_k_minus_2 = a_k_minus_1;
            //b_k_minus_2 = b_k_minus_1;
            a_k_minus_1 = a_k;
            b_k_minus_1 = b_k;
        }
        Ok(())
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

impl<F: PrimeField> ConstraintSynthesizer<F> for TestCircuit2a<F> {
    fn generate_constraints<CS: ConstraintSystemAbstract<F>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let mut a_k_minus_1 = FpGadget::<F>::alloc_input(cs.ns(|| "alloc a"), || {
            self.a.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let mut b_k_minus_1 = FpGadget::<F>::alloc_input(cs.ns(|| "alloc b"), || {
            self.b.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let zero = FpGadget::<F>::zero(cs.ns(|| "alloc zero"))?;

        a_k_minus_1.enforce_not_equal(cs.ns(|| "a_0 != 0"), &zero)?;
        b_k_minus_1.enforce_not_equal(cs.ns(|| "b_0 != 0"), &zero)?;

        // Quadratic recursion which produces (almost) full rank matrices A,B,C
        // of density d = 1, and demands one field inversion in every
        // second gate:
        //  a[k-1] = a[k] * b[k-1]      "new a = old a / old b"
        //  b[k] = b[k-1] * a[k-1]      "new b = old b * old a"
        for k in 0..(self.num_constraints - 5) / 2 {
            let a_k = FpGadget::<F>::alloc(cs.ns(|| format!("alloc a_{}", k)), || {
                Ok(a_k_minus_1.value.get()? * &b_k_minus_1.value.get()?.inverse().get()?)
            })?;

            let b_k = FpGadget::<F>::alloc(cs.ns(|| format!("alloc b_{}", k)), || {
                Ok(b_k_minus_1.value.get()? * &a_k_minus_1.value.get()?)
            })?;

            a_k.mul_equals(
                cs.ns(|| format!("a_{} * b_{} = a_{}", k, k - 1, k - 1)),
                &b_k_minus_1,
                &a_k_minus_1,
            )?;

            b_k_minus_1.mul_equals(
                cs.ns(|| format!("b_{} * a_{} = b_{}", k - 1, k - 1, k)),
                &a_k_minus_1,
                &b_k,
            )?;

            a_k_minus_1 = a_k;
            b_k_minus_1 = b_k;
        }

        Ok(())
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for TestCircuit2b<F> {
    fn generate_constraints<CS: ConstraintSystemAbstract<F>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let mut a_k_minus_2 = FpGadget::<F>::alloc_input(cs.ns(|| "alloc a0"), || {
            self.a.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let mut b_k_minus_2 = FpGadget::<F>::alloc_input(cs.ns(|| "alloc b0"), || {
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
        // such that max_{A,B,C} density = 1.5, and demands one field
        // inversion in every second gate:
        //  a[k-1] + a[k-2] = a[k] * (b[k-1] + b[k-2])  "new a = old a / old b"
        //  b[k] =    (b[k-1] + b[k-2]) * a[k-1]        "new b = old b * old a"
        for k in 2..(self.num_constraints - 5) / 2 {
            let a_k = FpGadget::<F>::alloc(cs.ns(|| format!("alloc a_{}", k)), || {
                let term_1 = a_k_minus_1.value.get()? + &a_k_minus_2.value.get()?;
                let term_2 = b_k_minus_1.value.get()? + &b_k_minus_2.value.get()?;
                Ok(term_1 * &(term_2.inverse().get()?))
            })?;

            let b_k = FpGadget::<F>::alloc(cs.ns(|| format!("alloc b_{}", k)), || {
                let term_1 = b_k_minus_1.value.get()? + &b_k_minus_2.value.get()?;
                let term_2 = a_k_minus_1.value.get()?;
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
                cs.ns(|| format!("(b_{} + b_{}) * a_{} = b_{}", k - 1, k - 2, k - 1, k)),
                &a_k_minus_1,
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

fn _bench_prover_circuit1a<G: EndoMulCurve, PC: PolynomialCommitment<G>, D: Digest>(c: &mut Criterion, group_name: &str) {
    let mut group = c.benchmark_group(group_name);

    let num_constraints = (14..=22).map(|i| 2usize.pow(i)).collect::<Vec<_>>();

    for &num_constraints in num_constraints.iter() {
        let universal_srs =
            Marlin::<G, PC, D>::universal_setup(num_constraints, num_constraints, num_constraints, false)
                .unwrap();
        let c = TestCircuit1a::<G::ScalarField> {
            num_constraints,
            a: None,
            b: None,
        };

        let (pc_pk, _) = universal_srs.trim(universal_srs.max_degree()).unwrap();
        let (index_pk, _) = Marlin::<G, PC, D>::circuit_specific_setup(&pc_pk, c.clone()).unwrap();

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
                        let mut rng = OsRng::default();
                        let a = G::ScalarField::rand(&mut rng);
                        let b = G::ScalarField::rand(&mut rng);
                        (a, b)
                    },
                    |(a, b)| {
                        let c = TestCircuit1a {
                            num_constraints,
                            a: Some(a),
                            b: Some(b),
                        };

                        Marlin::<G, PC, D>::prove(&index_pk, &pc_pk, c, false, None).unwrap();
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
    group.finish();
}

fn bench_prover_circuit1a(c: &mut Criterion) {
    _bench_prover_circuit1a::<DeeJacobian, IPAPCChaCha, Blake2s>(c, "marlin-tweedle_dee_chacha_fs-test circuit 1a-variable constraints-segment_size=num_constraints");
    _bench_prover_circuit1a::<DeeJacobian, IPAPCPoseidon, Blake2s>(c, "marlin-tweedle_dee_poseidon_fs-test circuit 1a-variable constraints-segment_size=num_constraints");
}

fn _bench_prover_circuit1b<G: EndoMulCurve, PC: PolynomialCommitment<G>, D: Digest>(c: &mut Criterion, group_name: &str) {
    let mut group = c.benchmark_group(group_name);

    let num_constraints = (14..=22).map(|i| 2usize.pow(i)).collect::<Vec<_>>();

    for &num_constraints in num_constraints.iter() {
        let universal_srs =
            Marlin::<G, PC, D>::universal_setup(num_constraints, num_constraints, num_constraints, false)
                .unwrap();
        let c = TestCircuit1b::<G::ScalarField> {
            num_constraints,
            a: None,
            b: None,
        };

        let (pc_pk, _) = universal_srs.trim(universal_srs.max_degree()).unwrap();
        let (index_pk, _) = Marlin::<G, PC, D>::circuit_specific_setup(&pc_pk, c.clone()).unwrap();

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
                        let mut rng = OsRng::default();
                        let a = G::ScalarField::rand(&mut rng);
                        let b = G::ScalarField::rand(&mut rng);
                        (a, b)
                    },
                    |(a, b)| {
                        let c = TestCircuit1b {
                            num_constraints,
                            a: Some(a),
                            b: Some(b),
                        };

                        Marlin::<G, PC, D>::prove(&index_pk, &pc_pk, c, false, None).unwrap();
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
    group.finish();
}

fn bench_prover_circuit1b(c: &mut Criterion) {
    _bench_prover_circuit1b::<DeeJacobian, IPAPCChaCha, Blake2s>(c, "marlin-tweedle_dee_chacha_fs-test circuit 1b-variable constraints-segment_size=num_constraints");
    _bench_prover_circuit1b::<DeeJacobian, IPAPCPoseidon, Blake2s>(c, "marlin-tweedle_dee_poseidon_fs-test circuit 1b-variable constraints-segment_size=num_constraints");
}

fn _bench_prover_circuit1c<G: EndoMulCurve, PC: PolynomialCommitment<G>, D: Digest>(c: &mut Criterion, group_name: &str) {
    let mut group = c.benchmark_group(group_name);

    let num_constraints = (14..=22).map(|i| 2usize.pow(i)).collect::<Vec<_>>();

    for &num_constraints in num_constraints.iter() {
        let universal_srs =
            Marlin::<G, PC, D>::universal_setup(num_constraints, num_constraints, num_constraints, false)
                .unwrap();
        let c = TestCircuit1c::<G::ScalarField> {
            num_constraints,
            a: None,
            b: None,
        };

        let (pc_pk, _) = universal_srs.trim(universal_srs.max_degree()).unwrap();
        let (index_pk, _) = Marlin::<G, PC, D>::circuit_specific_setup(&pc_pk, c.clone()).unwrap();

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
                        let mut rng = OsRng::default();
                        let a = G::ScalarField::rand(&mut rng);
                        let b = G::ScalarField::rand(&mut rng);
                        (a, b)
                    },
                    |(a, b)| {
                        let c = TestCircuit1c {
                            num_constraints,
                            a: Some(a),
                            b: Some(b),
                        };

                        Marlin::<G, PC, D>::prove(&index_pk, &pc_pk, c, false, None).unwrap();
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
    group.finish();
}

fn bench_prover_circuit1c(c: &mut Criterion) {
    _bench_prover_circuit1c::<DeeJacobian, IPAPCChaCha, Blake2s>(c, "marlin-tweedle_dee_chacha_fs-test circuit 1c-variable constraints-segment_size=num_constraints");
    _bench_prover_circuit1c::<DeeJacobian, IPAPCPoseidon, Blake2s>(c, "marlin-tweedle_dee_poseidon_fs-test circuit 1c-variable constraints-segment_size=num_constraints");
}

fn _bench_prover_circuit2a<G: EndoMulCurve, PC: PolynomialCommitment<G>, D: Digest>(c: &mut Criterion, group_name: &str) {
    let mut group = c.benchmark_group(group_name);

    let num_constraints = (14..=22).map(|i| 2usize.pow(i)).collect::<Vec<_>>();

    for &num_constraints in num_constraints.iter() {
        let universal_srs =
            Marlin::<G, PC, D>::universal_setup(num_constraints, num_constraints, num_constraints, false)
                .unwrap();
        let c = TestCircuit2a::<G::ScalarField> {
            num_constraints,
            a: None,
            b: None,
        };

        let (pc_pk, _) = universal_srs.trim(universal_srs.max_degree()).unwrap();
        let (index_pk, _) = Marlin::<G, PC, D>::circuit_specific_setup(&pc_pk, c.clone()).unwrap();

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
                        let mut rng = OsRng::default();
                        let a = G::ScalarField::rand(&mut rng);
                        let b = G::ScalarField::rand(&mut rng);
                        (a, b)
                    },
                    |(a, b)| {
                        let c = TestCircuit2a {
                            num_constraints,
                            a: Some(a),
                            b: Some(b),
                        };

                        Marlin::<G, PC, D>::prove(&index_pk, &pc_pk, c, false, None).unwrap();
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
    group.finish();
}

fn bench_prover_circuit2a(c: &mut Criterion) {
    _bench_prover_circuit2a::<DeeJacobian, IPAPCChaCha, Blake2s>(c, "marlin-tweedle_dee_chacha_fs-test circuit 2a-variable constraints-segment_size=num_constraints");
    _bench_prover_circuit2a::<DeeJacobian, IPAPCPoseidon, Blake2s>(c, "marlin-tweedle_dee_poseidon_fs-test circuit 2a-variable constraints-segment_size=num_constraints");
}

fn _bench_prover_circuit2b<G: EndoMulCurve, PC: PolynomialCommitment<G>, D: Digest>(c: &mut Criterion, group_name: &str) {
    let mut group = c.benchmark_group(group_name);

    let num_constraints = (14..=22).map(|i| 2usize.pow(i)).collect::<Vec<_>>();

    for &num_constraints in num_constraints.iter() {
        let universal_srs =
            Marlin::<G, PC, D>::universal_setup(num_constraints, num_constraints, num_constraints, false)
                .unwrap();
        let c = TestCircuit2b::<G::ScalarField> {
            num_constraints,
            a: None,
            b: None,
        };

        let (pc_pk, _) = universal_srs.trim(universal_srs.max_degree()).unwrap();
        let (index_pk, _) = Marlin::<G, PC, D>::circuit_specific_setup(&pc_pk, c.clone()).unwrap();

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
                        let mut rng = OsRng::default();
                        let a = G::ScalarField::rand(&mut rng);
                        let b = G::ScalarField::rand(&mut rng);
                        (a, b)
                    },
                    |(a, b)| {
                        let c = TestCircuit2b {
                            num_constraints,
                            a: Some(a),
                            b: Some(b),
                        };

                        Marlin::<G, PC, D>::prove(&index_pk, &pc_pk, c, false, None).unwrap();
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
    group.finish();
}

fn bench_prover_circuit2b(c: &mut Criterion) {
    _bench_prover_circuit2b::<DeeJacobian, IPAPCChaCha, Blake2s>(c, "marlin-tweedle_dee_chacha_fs-test circuit 2b-variable constraints-segment_size=num_constraints");
    _bench_prover_circuit2b::<DeeJacobian, IPAPCPoseidon, Blake2s>(c, "marlin-tweedle_dee_poseidon_fs-test circuit 2b-variable constraints-segment_size=num_constraints");
}

fn _bench_prover_circuit2c<G: EndoMulCurve, PC: PolynomialCommitment<G>, D: Digest>(c: &mut Criterion, group_name: &str) {
    let mut group = c.benchmark_group(group_name);

    let num_constraints = (14..=22).map(|i| 2usize.pow(i)).collect::<Vec<_>>();

    for &num_constraints in num_constraints.iter() {
        let universal_srs =
            Marlin::<G, PC, D>::universal_setup(num_constraints, num_constraints, num_constraints, false)
                .unwrap();
        let c = TestCircuit2c::<G::ScalarField> {
            num_constraints,
            a: None,
            b: None,
        };

        let (pc_pk, _) = universal_srs.trim(universal_srs.max_degree()).unwrap();
        let (index_pk, _) = Marlin::<G, PC, D>::circuit_specific_setup(&pc_pk, c.clone()).unwrap();

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
                        let mut rng = OsRng::default();
                        let a = G::ScalarField::rand(&mut rng);
                        let b = G::ScalarField::rand(&mut rng);
                        (a, b)
                    },
                    |(a, b)| {
                        let c = TestCircuit2c {
                            num_constraints,
                            a: Some(a),
                            b: Some(b),
                        };

                        Marlin::<G, PC, D>::prove(&index_pk, &pc_pk, c, false, None).unwrap();
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
    group.finish();
}

fn bench_prover_circuit2c(c: &mut Criterion) {
    _bench_prover_circuit2c::<DeeJacobian, IPAPCChaCha, Blake2s>(c, "marlin-tweedle_dee_chacha_fs-test circuit 2c-variable constraints-segment_size=num_constraints");
    _bench_prover_circuit2c::<DeeJacobian, IPAPCPoseidon, Blake2s>(c, "marlin-tweedle_dee_poseidon_fs-test circuit 2c-variable constraints-segment_size=num_constraints");
}

criterion_group!(
name = tweedle_test_circuits;
config = Criterion::default().sample_size(10);
targets = bench_prover_circuit1a, bench_prover_circuit1b, bench_prover_circuit1c,
          bench_prover_circuit2a, bench_prover_circuit2b, bench_prover_circuit2c,
);

criterion_main!(tweedle_test_circuits);
