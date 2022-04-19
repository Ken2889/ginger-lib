use crate::darlin::accumulators::dual::{DualAccumulator, DualAccumulatorItem};
use crate::darlin::accumulators::to_dual_field_vec::ToDualField;
use crate::darlin::accumulators::{Accumulator, AccumulatorItem};
use crate::darlin::IPACurve;
use algebra::{
    CanonicalDeserialize, CanonicalSerialize, DensePolynomial, Error, EvaluationDomain,
    Evaluations, Group, PrimeField, Read, SerializationError, ToBits, ToConstraintField,
    UniformRand, Write,
};
use derivative::Derivative;
use marlin::iop::sparse_linear_algebra::SparseMatrix;
use marlin::iop::LagrangeKernel;
use num_traits::{One, Zero};
use poly_commit::PolynomialCommitment;
use rand_core::RngCore;
use std::marker::PhantomData;

pub struct InnerSumcheckAccumulator<'a, G, PC, K>
where
    G: IPACurve,
    PC: PolynomialCommitment<G>,
    K: InnerSumcheckKey<G, PC>,
{
    _lifetime: PhantomData<&'a ()>,
    _g: PhantomData<G>,
    _pc: PhantomData<PC>,
    _k: PhantomData<K>,
}

impl<'a, G, PC, K: 'a> Accumulator for InnerSumcheckAccumulator<'a, G, PC, K>
where
    G: IPACurve,
    PC: PolynomialCommitment<G>,
    <PC as PolynomialCommitment<G>>::CommitterKey: 'a,
    K: InnerSumcheckKey<G, PC>,
{
    type ProverKey = ();
    type VerifierKey = (&'a K, &'a PC::CommitterKey);
    type Proof = ();
    type Item = InnerSumcheckItem<G, PC>;
    type ExpandedItem = DensePolynomial<G::ScalarField>;

    fn expand_item(
        vk: &Self::VerifierKey,
        accumulator: &Self::Item,
    ) -> Result<Self::ExpandedItem, Error> {
        let domain_h = vk.0.get_domain_h();
        let matrix_a = vk.0.get_matrix_a();
        let matrix_b = vk.0.get_matrix_b();
        let matrix_c = vk.0.get_matrix_c();

        let l_x_alpha_evals = domain_h
            .domain_eval_lagrange_kernel(accumulator.alpha)
            .unwrap();
        let t_evals = marlin::IOP::calculate_t(
            vec![matrix_a, matrix_b, matrix_c].into_iter(),
            accumulator.eta.as_slice(),
            domain_h.clone(),
            &l_x_alpha_evals,
        )
        .unwrap();

        Ok(Evaluations::from_vec_and_domain(t_evals, domain_h.clone()).interpolate())
    }

    fn check_item<R: RngCore>(
        vk: &Self::VerifierKey,
        accumulator: &Self::Item,
        _rng: &mut R,
    ) -> Result<Option<Self::ExpandedItem>, Error> {
        let t_poly = Self::expand_item(vk, accumulator)?;
        let (t_poly_comm, _) = PC::commit(&vk.1, &t_poly, false, None).unwrap();

        if t_poly_comm != accumulator.c {
            Ok(None)
        } else {
            Ok(Some(t_poly))
        }
    }

    fn check_items<R: RngCore>(
        vk: &Self::VerifierKey,
        accumulators: &[Self::Item],
        rng: &mut R,
    ) -> Result<Option<Vec<Self::ExpandedItem>>, Error> {
        let t_polys = Self::expand_items(vk, accumulators)?;

        let mut batching_chals = Vec::with_capacity(accumulators.len());
        {
            let random_scalar = G::ScalarField::rand(rng);
            let mut batching_chal = G::ScalarField::one();
            for _ in 0..accumulators.len() {
                batching_chals.push(batching_chal);
                batching_chal *= random_scalar;
            }
        }

        let (batched_t_poly, batched_comm) = t_polys
            .iter()
            .zip(accumulators.iter())
            .zip(batching_chals.iter())
            .map(|((poly, acc), chal)| (poly.clone() * chal, acc.c.clone() * chal))
            .reduce(|a, b| (a.0 + b.0, a.1 + b.1))
            .unwrap();

        let (batched_t_poly_comm, _) = PC::commit(&vk.1, &batched_t_poly, false, None).unwrap();

        if batched_t_poly_comm != batched_comm {
            Ok(None)
        } else {
            Ok(Some(t_polys))
        }
    }

    fn check_items_optimized<R: RngCore>(
        vk: &Self::VerifierKey,
        accumulators: &[Self::Item],
        rng: &mut R,
    ) -> Result<bool, Error> {
        let domain_h = vk.0.get_domain_h();
        let matrix_a = vk.0.get_matrix_a();
        let matrix_b = vk.0.get_matrix_b();
        let matrix_c = vk.0.get_matrix_c();

        let random_scalar = G::ScalarField::rand(rng);
        let mut batching_chal = G::ScalarField::one();

        let mut batched_comm = PC::Commitment::zero();
        let mut batched_t_evals = vec![G::ScalarField::zero(); domain_h.size()];
        for acc in accumulators.iter() {
            let mut etas = acc.eta.clone();
            for eta in etas.iter_mut() {
                *eta *= batching_chal;
            }

            batched_comm += acc.c.clone() * &batching_chal;

            let l_x_alpha_evals = domain_h.domain_eval_lagrange_kernel(acc.alpha).unwrap();
            let t_evals = marlin::IOP::calculate_t(
                vec![matrix_a, matrix_b, matrix_c].into_iter(),
                etas.as_slice(),
                domain_h.clone(),
                &l_x_alpha_evals,
            )
            .unwrap();

            for (acc_t, t) in batched_t_evals.iter_mut().zip(t_evals) {
                *acc_t += t;
            }

            batching_chal *= random_scalar;
        }

        let batched_t_poly =
            Evaluations::from_vec_and_domain(batched_t_evals, domain_h.clone()).interpolate();
        let (batched_t_poly_comm, _) = PC::commit(&vk.1, &batched_t_poly, false, None).unwrap();

        Ok(batched_t_poly_comm == batched_comm)
    }

    fn accumulate_items(
        _ck: &Self::ProverKey,
        _accumulators: Vec<Self::Item>,
    ) -> Result<(Self::Item, Self::Proof), Error> {
        unimplemented!()
    }

    fn verify_accumulated_items<R: RngCore>(
        _current_accumulator: &Self::Item,
        _vk: &Self::VerifierKey,
        _previous_accumulators: Vec<Self::Item>,
        _proof: &Self::Proof,
        _rng: &mut R,
    ) -> Result<bool, Error> {
        unimplemented!()
    }

    fn trivial_item(_vk: &Self::VerifierKey) -> Result<Self::Item, Error> {
        Ok(Self::Item {
            alpha: G::ScalarField::zero(),
            eta: vec![G::ScalarField::zero(); 3],
            c: PC::Commitment::zero(),
        })
    }

    fn random_item<R: RngCore>(vk: &Self::VerifierKey, rng: &mut R) -> Result<Self::Item, Error> {
        let domain_h = vk.0.get_domain_h();
        let matrix_a = vk.0.get_matrix_a();
        let matrix_b = vk.0.get_matrix_b();
        let matrix_c = vk.0.get_matrix_c();

        let alpha: G::ScalarField = u128::rand(rng).into();
        let eta: Vec<_> = (0..3)
            .into_iter()
            .map(|_| G::ScalarField::rand(rng))
            .collect();

        let l_x_alpha_evals = domain_h.domain_eval_lagrange_kernel(alpha).unwrap();

        let t_evals = marlin::IOP::calculate_t(
            vec![matrix_a, matrix_b, matrix_c].into_iter(),
            eta.as_slice(),
            domain_h.clone(),
            &l_x_alpha_evals,
        )
        .unwrap();
        let t_poly =
            Evaluations::from_vec_and_domain(t_evals.clone(), domain_h.clone()).interpolate();
        let (c, _) = PC::commit(&vk.1, &t_poly, false, None).unwrap();

        Ok(Self::Item { alpha, eta, c })
    }

    fn invalid_item<R: RngCore>(vk: &Self::VerifierKey, rng: &mut R) -> Result<Self::Item, Error> {
        let mut result = Self::random_item(vk, rng)?;
        result.c.double_in_place();
        Ok(result)
    }
}

/// An item to be collected in an inner-sumcheck accumulator.
#[derive(Derivative)]
#[derivative(Clone, Debug, Eq, PartialEq)]
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct InnerSumcheckItem<G: IPACurve, PC: PolynomialCommitment<G>> {
    /// Sampling point.
    pub alpha: G::ScalarField,
    /// Batching randomness.
    pub eta: Vec<G::ScalarField>,
    /// Commitment of the batched circuit polynomials.
    pub c: PC::Commitment,
}

impl<G, PC> AccumulatorItem for InnerSumcheckItem<G, PC>
where
    G: IPACurve,
    PC: PolynomialCommitment<G>,
{
}

impl<G, PC> ToConstraintField<G::ScalarField> for InnerSumcheckItem<G, PC>
where
    G: IPACurve,
    PC: PolynomialCommitment<G>,
{
    fn to_field_elements(&self) -> Result<Vec<G::ScalarField>, Error> {
        let mut fes = Vec::new();

        // The commitment c is over G::BaseField. We serialize it to bits and pack it safely into
        // G::ScalarField elements
        let mut c_g1_bits = Vec::new();
        let c_fes = self.c.to_field_elements()?;
        for fe in c_fes {
            c_g1_bits.append(&mut fe.write_bits());
        }
        fes.append(&mut c_g1_bits.to_field_elements()?);

        // The challenges alpha and eta are already over G::ScalarField. Since only alpha is a
        // 128-bit challenge, we wouldn't save anything from packing the challenges into bits.
        // Therefore we keep them as they are.
        fes.push(self.alpha);
        fes.append(&mut self.eta.clone());

        Ok(fes)
    }
}

impl<G, PC> ToDualField<G::BaseField> for InnerSumcheckItem<G, PC>
where
    G: IPACurve,
    PC: PolynomialCommitment<G>,
{
    fn to_dual_field_elements(&self) -> Result<Vec<G::BaseField>, Error> {
        let mut fes = Vec::new();

        // The commitment c consists of G::BaseField elements only.
        fes.append(&mut self.c.to_field_elements()?);

        // The alpha challenge is a 128 bit element from G::ScalarField. We convert it to bits.
        let mut challenge_bits = Vec::new();
        {
            let to_skip = <G::ScalarField as PrimeField>::size_in_bits() - 128;
            let bits = self.alpha.write_bits();
            challenge_bits.extend_from_slice(&bits[to_skip..]);
        }
        // The eta challenges are 3 generic elements from G::ScalarField. We convert them to bits.
        for fe in self.eta.iter() {
            let bits = fe.write_bits();
            challenge_bits.extend_from_slice(&bits);
        }

        // We pack the full bit vector into native field elements as efficiently as possible (yet
        // still secure).
        fes.append(&mut challenge_bits.to_field_elements()?);

        Ok(fes)
    }
}

pub trait InnerSumcheckKey<G: Group, PC: PolynomialCommitment<G>> {
    fn get_matrix_a(&self) -> &SparseMatrix<G::ScalarField>;
    fn get_matrix_b(&self) -> &SparseMatrix<G::ScalarField>;
    fn get_matrix_c(&self) -> &SparseMatrix<G::ScalarField>;
    fn get_domain_h(&self) -> Box<dyn EvaluationDomain<G::ScalarField>>;
}

pub type DualInnerSumcheckAccumulator<'a, G1, G2, PC1, PC2, K1, K2> = DualAccumulator<
    'a,
    InnerSumcheckAccumulator<'a, G1, PC1, K1>,
    InnerSumcheckAccumulator<'a, G2, PC2, K2>,
>;
pub type DualInnerSumcheckItem<G1, G2, PC1, PC2> =
    DualAccumulatorItem<InnerSumcheckItem<G1, PC1>, InnerSumcheckItem<G2, PC2>>;
