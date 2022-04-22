use crate::darlin::accumulators::Accumulator;
use crate::darlin::t_dlog_acc_marlin::iop::indexer::Index;
use crate::darlin::t_dlog_acc_marlin::iop::IOP;
use crate::darlin::IPACurve;
use algebra::{PrimeField, UniformRand};
use digest::Digest;
use fiat_shamir::FiatShamirRng;
use itertools::Itertools;
use poly_commit::ipa_pc::{CommitterKey, InnerProductArgPC};
use poly_commit::PolynomialCommitment;
use r1cs_core::{ConstraintSynthesizer, ConstraintSystemAbstract, SynthesisError};
use r1cs_std::alloc::AllocGadget;
use r1cs_std::eq::EqGadget;
use r1cs_std::fields::fp::FpGadget;
use r1cs_std::fields::FieldGadget;
use r1cs_std::Assignment;
use rand::thread_rng;
use rand_core::RngCore;
use std::ops::MulAssign;

#[derive(Copy, Clone)]
struct Circuit<F: PrimeField> {
    num_constraints: usize,
    a: Option<F>,
    b: Option<F>,
}

impl<F: PrimeField> ConstraintSynthesizer<F> for Circuit<F> {
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

pub(super) fn test_check_items<A: Accumulator, R: RngCore>(
    vk: &A::VerifierKey,
    num_items: usize,
    rng: &mut R,
) {
    let (random_items, invalid_items, trivial_items): (Vec<_>, Vec<_>, Vec<_>) = (0..num_items)
        .into_iter()
        .map(|_| {
            (
                A::random_item(vk, rng).unwrap(),
                A::invalid_item(vk, rng).unwrap(),
                A::trivial_item(vk).unwrap(),
            )
        })
        .multiunzip();

    let check_random_items = A::check_items(vk, random_items.as_slice(), rng).unwrap();
    assert!(check_random_items);

    let check_invalid_items = A::check_items(vk, invalid_items.as_slice(), rng).unwrap();
    assert!(!check_invalid_items);

    let check_trivial_items = A::check_items(vk, trivial_items.as_slice(), rng).unwrap();
    assert!(check_trivial_items);
}

pub(super) fn get_committer_key<G: IPACurve, FS: FiatShamirRng, D: Digest>(
    max_degree: usize,
) -> CommitterKey<G> {
    let (_, vk) = InnerProductArgPC::<G, FS>::setup::<D>(max_degree).unwrap();
    vk
}

pub(super) fn get_index<G1: IPACurve, G2: IPACurve, R: RngCore>(
    num_constraints: usize,
    rng: &mut R,
) -> Index<G1> {
    let a = G1::ScalarField::rand(rng);
    let b = G1::ScalarField::rand(rng);
    let mut c = a;
    c.mul_assign(&b);
    let mut d = c;
    d.mul_assign(&b);

    let circ = Circuit {
        a: Some(a),
        b: Some(b),
        num_constraints,
    };

    IOP::<G1, G2>::index(circ).unwrap()
}
