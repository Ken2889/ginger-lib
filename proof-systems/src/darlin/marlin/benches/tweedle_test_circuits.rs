use algebra::{curves::tweedle::dee::DeeJacobian};
use blake2::{Blake2s, Digest};
use marlin::*;
use poly_commit::PolynomialCommitment;
use poly_commit::{ipa_pc::InnerProductArgPC, DomainExtendedPolynomialCommitment, PCParameters};

use algebra::{PrimeField, EndoMulCurve};
use r1cs_core::{ConstraintSynthesizer, ConstraintSystemAbstract, SynthesisError};

use criterion::Criterion;
use criterion::{BatchSize, BenchmarkId};
use r1cs_std::alloc::AllocGadget;
use r1cs_std::eq::EqGadget;
use r1cs_std::fields::fp::FpGadget;
use r1cs_std::fields::FieldGadget;
use r1cs_std::Assignment;

use rand::{rngs::OsRng, thread_rng};

use std::fmt::Display;
use std::time::{SystemTime, UNIX_EPOCH};

#[macro_use]
extern crate criterion;

#[macro_use]
extern crate bench_utils;

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

#[derive(Copy, Clone)]
enum CircuitType {
    Circuit1a, Circuit1b, Circuit1c, Circuit2a, Circuit2b, Circuit2c
}

impl CircuitType {
    fn get_variants() -> Vec<Self> {
        vec![
            CircuitType::Circuit1a, CircuitType::Circuit1b, CircuitType::Circuit1c,
            CircuitType::Circuit2a, CircuitType::Circuit2b, CircuitType::Circuit2c,
        ]
    }
}

impl Display for CircuitType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CircuitType::Circuit1a => write!(f, "Circuit1a"),
            CircuitType::Circuit1b => write!(f, "Circuit1b"),
            CircuitType::Circuit1c => write!(f, "Circuit1c"),
            CircuitType::Circuit2a => write!(f, "Circuit2a"),
            CircuitType::Circuit2b => write!(f, "Circuit2b"),
            CircuitType::Circuit2c => write!(f, "Circuit2c"),
        }
    }
}

#[derive(Clone)]
enum TestCircuit<F: PrimeField> {
    Circuit1a(TestCircuit1a<F>),
    Circuit1b(TestCircuit1b<F>),
    Circuit1c(TestCircuit1c<F>),
    Circuit2a(TestCircuit2a<F>),
    Circuit2b(TestCircuit2b<F>),
    Circuit2c(TestCircuit2c<F>),
}

impl<F: PrimeField> TestCircuit<F> {
    pub(crate) fn get_instance_for_setup(num_constraints: usize, circuit_type: CircuitType) -> Self {
        match circuit_type {
            CircuitType::Circuit1a => Self::Circuit1a(TestCircuit1a::<F>{ num_constraints, a: None, b: None }),
            CircuitType::Circuit1b => Self::Circuit1b(TestCircuit1b::<F>{ num_constraints, a: None, b: None }),
            CircuitType::Circuit1c => Self::Circuit1c(TestCircuit1c::<F>{ num_constraints, a: None, b: None }),
            CircuitType::Circuit2a => Self::Circuit2a(TestCircuit2a::<F>{ num_constraints, a: None, b: None }),
            CircuitType::Circuit2b => Self::Circuit2b(TestCircuit2b::<F>{ num_constraints, a: None, b: None }),
            CircuitType::Circuit2c => Self::Circuit2c(TestCircuit2c::<F>{ num_constraints, a: None, b: None }),
        }
    }

    pub(crate) fn get_random_instance(num_constraints: usize, circuit_type: CircuitType) -> Self {
        let rng = &mut OsRng::default();
        let (a, b) = (Some(F::rand(rng)), Some(F::rand(rng)));
        match circuit_type {
            CircuitType::Circuit1a => Self::Circuit1a(TestCircuit1a::<F>{ num_constraints, a, b }),
            CircuitType::Circuit1b => Self::Circuit1b(TestCircuit1b::<F>{ num_constraints, a, b }),
            CircuitType::Circuit1c => Self::Circuit1c(TestCircuit1c::<F>{ num_constraints, a, b }),
            CircuitType::Circuit2a => Self::Circuit2a(TestCircuit2a::<F>{ num_constraints, a, b }),
            CircuitType::Circuit2b => Self::Circuit2b(TestCircuit2b::<F>{ num_constraints, a, b }),
            CircuitType::Circuit2c => Self::Circuit2c(TestCircuit2c::<F>{ num_constraints, a, b }),
        }
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for TestCircuit<F> {
    fn generate_constraints<CS: ConstraintSystemAbstract<F>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        match self {
            TestCircuit::Circuit1a(c) => c.generate_constraints(cs),
            TestCircuit::Circuit1b(c) => c.generate_constraints(cs),
            TestCircuit::Circuit1c(c) => c.generate_constraints(cs),
            TestCircuit::Circuit2a(c) => c.generate_constraints(cs),
            TestCircuit::Circuit2b(c) => c.generate_constraints(cs),
            TestCircuit::Circuit2c(c) => c.generate_constraints(cs),
        }
    }
}

fn bench_prover_circuit<G: EndoMulCurve, PC: PolynomialCommitment<G>, D: Digest>(c: &mut Criterion, circuit_type: CircuitType) {
    let mut group = c.benchmark_group(format!("bench {}", circuit_type).as_str());

    let num_constraints = (14..=22).map(|i| 2usize.pow(i)).collect::<Vec<_>>();

    for &num_constraints in num_constraints.iter() {
        let universal_srs =
            Marlin::<G, PC>::universal_setup::<D>(num_constraints, num_constraints, num_constraints, false)
                .unwrap();
        let c = TestCircuit::<G::ScalarField>::get_instance_for_setup(num_constraints, circuit_type);

        let (pc_pk, _) = universal_srs.trim(universal_srs.max_degree()).unwrap();
        let (index_pk, _) = Marlin::<G, PC>::circuit_specific_setup::<_, D>(&pc_pk, c.clone()).unwrap();

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
                    || TestCircuit::<G::ScalarField>::get_random_instance(num_constraints, circuit_type),
                    |c| {
                        Marlin::<G, PC>::prove(&index_pk, &pc_pk, c, false, None).unwrap();
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


#[cfg(not(feature = "circuit-friendly"))]
mod benches {
    use super::*;
    use poly_commit::chacha20::FiatShamirChaChaRng;

    type IPAPCChaCha =
        DomainExtendedPolynomialCommitment<DeeJacobian, InnerProductArgPC<DeeJacobian, FiatShamirChaChaRng<Blake2s>>>;

    pub(crate) fn bench_prover_circuits(c: &mut Criterion) {
        for circ_type in CircuitType::get_variants() {
            bench_prover_circuit::<DeeJacobian, IPAPCChaCha, Blake2s>(c, circ_type);
        }
    }
}

#[cfg(feature = "circuit-friendly")]
mod benches {
    use super::*;
    use fiat_shamir::poseidon::TweedleFqPoseidonFSRng;

    type IPAPCPoseidon =
        DomainExtendedPolynomialCommitment<DeeJacobian, InnerProductArgPC<DeeJacobian, TweedleFqPoseidonFSRng>>;

    pub(crate) fn bench_prover_circuits(c: &mut Criterion) {
        for circ_type in CircuitType::get_variants() {
            bench_prover_circuit::<DeeJacobian, IPAPCPoseidon, Blake2s>(c, circ_type);
        }
    }
}

criterion_group!(
    name = tweedle_test_circuits;
    config = Criterion::default().sample_size(10);
    targets = benches::bench_prover_circuits
);

criterion_main!(tweedle_test_circuits);
