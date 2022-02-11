use algebra::PrimeField;
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use r1cs_std::fields::nonnative::nonnative_field_gadget::NonNativeFieldGadget;
use r1cs_std::fields::FieldGadget;
use std::marker::PhantomData;

pub struct AlgebraForIOP<F: PrimeField, ConstraintF: PrimeField> {
    field: PhantomData<F>,
    constraint_field: PhantomData<ConstraintF>,
}

impl<F: PrimeField, ConstraintF: PrimeField> AlgebraForIOP<F, ConstraintF> {
    pub fn prepare<CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        x: &NonNativeFieldGadget<F, ConstraintF>,
        domain_size: u64,
    ) -> Result<NonNativeFieldGadget<F, ConstraintF>, SynthesisError> {
        x.pow_by_constant(cs, &[domain_size])
    }

    pub fn prepared_eval_vanishing_polynomial<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        x_prepared: &NonNativeFieldGadget<F, ConstraintF>,
    ) -> Result<NonNativeFieldGadget<F, ConstraintF>, SynthesisError> {
        let one = NonNativeFieldGadget::<F, ConstraintF>::one(cs.ns(|| "alloc one"))?;
        let result = x_prepared.sub(cs.ns(|| "x_prepared - one"), &one)?;
        Ok(result)
    }

    pub fn eval_vanishing_polynomial<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        x: &NonNativeFieldGadget<F, ConstraintF>,
        domain_size: u64,
    ) -> Result<NonNativeFieldGadget<F, ConstraintF>, SynthesisError> {
        let x_prepared = Self::prepare(cs.ns(|| "prepare x"), x, domain_size)?;
        Self::prepared_eval_vanishing_polynomial(
            cs.ns(|| "compute eval vanishing poly"),
            &x_prepared,
        )
    }

    pub fn prepared_eval_lagrange_kernel<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        x: &NonNativeFieldGadget<F, ConstraintF>,
        y: &NonNativeFieldGadget<F, ConstraintF>,
        v_at_x: &NonNativeFieldGadget<F, ConstraintF>,
        v_at_y: &NonNativeFieldGadget<F, ConstraintF>,
        domain_size_inv: &F,
    ) -> Result<NonNativeFieldGadget<F, ConstraintF>, SynthesisError> {
        let num_1 = y.mul_without_prereduce(cs.ns(|| "y * v_at_x"), v_at_x)?;
        let num_2 = x
            .negate(cs.ns(|| "-x"))?
            .mul_without_prereduce(cs.ns(|| "-x * v_at_y"), v_at_y)?;
        let numerator = num_1
            .add(cs.ns(|| "y * v_at_x - x * v_at_y"), &num_2)?
            .reduce(cs.ns(|| "reduce(y * v_at_x - x * v_at_y)"))?
            .mul_by_constant(cs.ns(|| "scale(y * v_at_x - x * v_at_y)"), domain_size_inv)?;

        let denominator_inv = x
            .sub(cs.ns(|| "x - y"), y)?
            .inverse(cs.ns(|| "(x - y)^(-1)"))?;

        numerator.mul(cs.ns(|| "num * denominator^(-1)"), &denominator_inv)
    }
}

#[cfg(test)]
mod test {
    use crate::constraints::polynomials::AlgebraForIOP;
    use crate::LagrangeKernel;
    use algebra::{
        fields::tweedle::fq::Fq, fields::tweedle::fr::Fr, get_best_evaluation_domain, UniformRand,
    };
    use r1cs_core::{
        ConstraintSystem, ConstraintSystemAbstract, ConstraintSystemDebugger, SynthesisMode,
    };
    use r1cs_std::alloc::AllocGadget;
    use r1cs_std::eq::EqGadget;
    use r1cs_std::fields::nonnative::nonnative_field_gadget::NonNativeFieldGadget;
    use rand::thread_rng;

    #[test]
    fn eval_vanishing_polynomial() {
        let rng = &mut thread_rng();
        let alpha = Fr::rand(rng);

        let num_coeffs = 100;
        let domain_h = get_best_evaluation_domain::<Fr>(num_coeffs).unwrap();

        let v_h = domain_h.evaluate_vanishing_polynomial(alpha);

        let domain_h_size = domain_h.size() as u64;
        let mut cs = ConstraintSystem::<Fq>::new(SynthesisMode::Debug);
        let alpha_gadget =
            NonNativeFieldGadget::<Fr, Fq>::alloc(cs.ns(|| "alloc alpha"), || Ok(alpha)).unwrap();
        let v_h_gadget =
            NonNativeFieldGadget::<Fr, Fq>::alloc(cs.ns(|| "alloc v_h"), || Ok(v_h)).unwrap();
        let v_h_computed = AlgebraForIOP::eval_vanishing_polynomial(
            cs.ns(|| "compute v_h"),
            &alpha_gadget,
            domain_h_size,
        )
        .unwrap();
        v_h_gadget
            .enforce_equal(cs.ns(|| "enforce v_h == v_h_computed"), &v_h_computed)
            .unwrap();

        assert!(cs.is_satisfied())
    }

    #[test]
    fn eval_lagrange_kernel() {
        let rng = &mut thread_rng();
        let alpha = Fr::rand(rng);
        let beta = Fr::rand(rng);

        let num_coeffs = 100;
        let domain_h = get_best_evaluation_domain::<Fr>(num_coeffs).unwrap();

        let l_h = domain_h.eval_lagrange_kernel(alpha, beta);

        let domain_h_size = domain_h.size() as u64;
        let domain_h_size_inv = domain_h.size_inv();
        let mut cs = ConstraintSystem::<Fq>::new(SynthesisMode::Debug);
        let l_h_gadget =
            NonNativeFieldGadget::<Fr, Fq>::alloc(cs.ns(|| "alloc l_h"), || Ok(l_h)).unwrap();
        let alpha_gadget =
            NonNativeFieldGadget::<Fr, Fq>::alloc(cs.ns(|| "alloc alpha"), || Ok(alpha)).unwrap();
        let beta_gadget =
            NonNativeFieldGadget::<Fr, Fq>::alloc(cs.ns(|| "alloc beta"), || Ok(beta)).unwrap();
        let v_h_alpha_gadget = AlgebraForIOP::eval_vanishing_polynomial(
            cs.ns(|| "compute v_h_alpha"),
            &alpha_gadget,
            domain_h_size,
        )
        .unwrap();
        let v_h_beta_gadget = AlgebraForIOP::eval_vanishing_polynomial(
            cs.ns(|| "compute v_h_beta"),
            &beta_gadget,
            domain_h_size,
        )
        .unwrap();
        let l_h_computed = AlgebraForIOP::prepared_eval_lagrange_kernel(
            cs.ns(|| "compute l_h"),
            &alpha_gadget,
            &beta_gadget,
            &v_h_alpha_gadget,
            &v_h_beta_gadget,
            &domain_h_size_inv,
        )
        .unwrap();
        l_h_computed
            .enforce_equal(cs.ns(|| "enforce l_h_gadget == l_h_computed"), &l_h_gadget)
            .unwrap();

        assert!(cs.is_satisfied())
    }
}
