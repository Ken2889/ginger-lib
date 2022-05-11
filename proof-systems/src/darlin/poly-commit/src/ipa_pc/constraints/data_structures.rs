use crate::ipa_pc::constraints::InnerProductArgGadget;
use crate::ipa_pc::{DLogItem, InnerProductArgPC, MultiPointProof, Proof};
use crate::{
    MultiPointProofGadget, PolynomialCommitmentVerifierGadget,
    VerifierStateGadget,
};
use algebra::{EndoMulCurve, PrimeField, SemanticallyValid, ToBits};
use fiat_shamir::constraints::FiatShamirRngGadget;
use fiat_shamir::FiatShamirRng;
use num_traits::One;
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use r1cs_std::boolean::Boolean;
use r1cs_std::fields::fp::FpGadget;
use r1cs_std::fields::nonnative::nonnative_field_gadget::NonNativeFieldGadget;
use r1cs_std::prelude::{AllocGadget, EndoMulCurveGadget, FieldGadget};
use r1cs_std::to_field_gadget_vec::ToConstraintFieldGadget;
use std::borrow::Borrow;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SuccinctCheckPolynomialGadget<
    ConstraintF: PrimeField,
    G: EndoMulCurve<BaseField = ConstraintF>,
>(Vec<NonNativeFieldGadget<G::ScalarField, ConstraintF>>);

impl<ConstraintF: PrimeField, G: EndoMulCurve<BaseField = ConstraintF>>
    SuccinctCheckPolynomialGadget<ConstraintF, G>
{
    pub fn new(challenges: Vec<NonNativeFieldGadget<G::ScalarField, ConstraintF>>) -> Self {
        SuccinctCheckPolynomialGadget(challenges)
    }

    pub fn evaluate<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        point: &NonNativeFieldGadget<G::ScalarField, ConstraintF>,
    ) -> Result<NonNativeFieldGadget<G::ScalarField, ConstraintF>, SynthesisError> {
        let mut point_power = point.clone();
        let one = NonNativeFieldGadget::<G::ScalarField, ConstraintF>::one(
            cs.ns(|| "alloc 1 in scalar field"),
        )?;
        let mut bullet_polynomial_evaluation = one.clone();

        let challenges = &self.0;
        for (i, round_challenge) in challenges.iter().rev().enumerate() {
            let challenge_times_point_power = point_power.mul_without_prereduce(
                cs.ns(|| format!("round_challenge_{}*point^(2^{})", challenges.len() - i, i)),
                &round_challenge,
            )?;
            let current_term = challenge_times_point_power.add_constant(
                cs.ns(|| format!("round_challenge_{}*point^(2^{})+1", challenges.len() - i, i)),
                &G::ScalarField::one(),
            )?;
            let current_term = current_term.reduce(cs.ns(|| {
                format!(
                    "reduce round_challenge_{}*point^(2^{})+1",
                    challenges.len() - i,
                    i
                )
            }))?;

            if i != 0 {
                bullet_polynomial_evaluation.mul_in_place(
                    cs.ns(|| {
                        format!(
                            "update bullet polynomial with challenge {}",
                            challenges.len() - i
                        )
                    }),
                    &current_term,
                )?;
            } else {
                // avoid costly multiplication in the first iteration
                bullet_polynomial_evaluation = current_term;
            }

            if i == challenges.len() - 1 {
                //avoid costly squaring in the last iteration
                continue;
            }

            point_power.square_in_place(cs.ns(|| format!("compute point^(2^{})", i)))?;
        }
        Ok(bullet_polynomial_evaluation)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IPAVerifierStateGadget<
    ConstraintF: PrimeField,
    G: EndoMulCurve<BaseField = ConstraintF>,
    GG: 'static + EndoMulCurveGadget<G, ConstraintF>,
> {
    check_poly: SuccinctCheckPolynomialGadget<ConstraintF, G>,
    final_comm_key: GG,
}

impl<
        ConstraintF: PrimeField,
        G: EndoMulCurve<BaseField = ConstraintF>,
        GG: 'static + EndoMulCurveGadget<G, ConstraintF>,
    > IPAVerifierStateGadget<ConstraintF, G, GG>
{
    pub fn new(
        check_poly: SuccinctCheckPolynomialGadget<ConstraintF, G>,
        final_comm_key: GG,
    ) -> Self {
        Self {
            check_poly,
            final_comm_key,
        }
    }
}

impl<
        ConstraintF: PrimeField,
        G: EndoMulCurve<BaseField = ConstraintF>,
        GG: 'static + EndoMulCurveGadget<G, ConstraintF>,
    > VerifierStateGadget<DLogItem<G>, ConstraintF> for IPAVerifierStateGadget<ConstraintF, G, GG>
{
}

impl<
        ConstraintF: PrimeField,
        G: EndoMulCurve<BaseField = ConstraintF>,
        GG: 'static + EndoMulCurveGadget<G, ConstraintF>,
    > AllocGadget<DLogItem<G>, ConstraintF> for IPAVerifierStateGadget<ConstraintF, G, GG>
{
    fn alloc<F, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        f: F,
    ) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<DLogItem<G>>,
    {
        let t = f()?;
        let verifier_state = t.borrow();

        let mut check_poly = Vec::with_capacity(verifier_state.check_poly.get_chals().len());
        for (i, challenge) in verifier_state.check_poly.get_chals().iter().enumerate() {
            check_poly.push(NonNativeFieldGadget::<G::ScalarField, ConstraintF>::alloc(
                cs.ns(|| format!("alloc {}-th challenge for bullet polynomial", i + 1)),
                || Ok(challenge),
            )?);
        }

        let final_comm_key = GG::alloc(cs.ns(|| "alloc final commitment key"), || {
            Ok(verifier_state.final_comm_key)
        })?;

        Ok(Self {
            check_poly: SuccinctCheckPolynomialGadget(check_poly),
            final_comm_key,
        })
    }

    fn alloc_input<F, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        f: F,
    ) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<DLogItem<G>>,
    {
        let t = f()?;
        let verifier_state = t.borrow();

        let mut check_poly = Vec::with_capacity(verifier_state.check_poly.get_chals().len());
        for (i, challenge) in verifier_state.check_poly.get_chals().iter().enumerate() {
            check_poly.push(
                NonNativeFieldGadget::<G::ScalarField, ConstraintF>::alloc_input(
                    cs.ns(|| format!("alloc {}-th challenge for bullet polynomial", i + 1)),
                    || Ok(challenge),
                )?,
            );
        }

        let final_comm_key = GG::alloc_input(cs.ns(|| "alloc final commitment key"), || {
            Ok(verifier_state.final_comm_key)
        })?;

        Ok(Self {
            check_poly: SuccinctCheckPolynomialGadget(check_poly),
            final_comm_key,
        })
    }
}

#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
pub struct IPAProofGadget<
    ConstraintF: PrimeField,
    G: EndoMulCurve<BaseField = ConstraintF>,
    GG: 'static
        + EndoMulCurveGadget<G, ConstraintF, Value=G>
        + ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>,
    FS: FiatShamirRng,
    FSG: FiatShamirRngGadget<ConstraintF>,
> {
    pub(crate) vec_l: Vec<IPACommitmentGadgetType<ConstraintF, G, GG, FS, FSG>>,
    pub(crate) vec_r: Vec<IPACommitmentGadgetType<ConstraintF, G, GG, FS, FSG>>,
    pub(crate) final_comm_key: IPACommitmentGadgetType<ConstraintF, G, GG, FS, FSG>,
    pub(crate) c: Vec<Boolean>,
    pub(crate) hiding_comm: Option<IPACommitmentGadgetType<ConstraintF, G, GG, FS, FSG>>,
    pub(crate) rand: Option<Vec<Boolean>>,
}

impl<
        ConstraintF: PrimeField,
        G: EndoMulCurve<BaseField = ConstraintF>,
        GG: 'static
            + EndoMulCurveGadget<G, ConstraintF, Value=G>
            + ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>,
        FS: FiatShamirRng,
        FSG: FiatShamirRngGadget<ConstraintF>,
    > AllocGadget<Proof<G>, ConstraintF> for IPAProofGadget<ConstraintF, G, GG, FS, FSG>
{
    fn alloc<F, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        f: F,
    ) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Proof<G>>,
    {
        let t = f()?;
        let proof = t.borrow();
        if !proof.is_valid() {
            return Err(SynthesisError::Other(String::from(
                "invalid proof provided to alloc",
            )));
        }
        let mut vec_l = Vec::with_capacity(proof.l_vec.len());
        let mut vec_r = Vec::with_capacity(proof.r_vec.len());
        for (i, (el_vec_l, el_vec_r)) in proof.l_vec.iter().zip(proof.r_vec.iter()).enumerate() {
            vec_l.push(GG::alloc(
                cs.ns(|| format!("alloc left vec entry {} for proof", i)),
                || Ok(el_vec_l),
            )?);
            vec_r.push(GG::alloc(
                cs.ns(|| format!("alloc right vec entry {} for proof", i)),
                || Ok(el_vec_r),
            )?);
        }
        let final_comm_key = GG::alloc(cs.ns(|| "alloc final commitment key for proof"), || {
            Ok(proof.final_comm_key)
        })?;
        let c = Vec::<Boolean>::alloc(cs.ns(|| "alloc final polynomial for proof"), || {
            Ok(proof.c.write_bits())
        })?;

        let hiding_comm = match proof.hiding_comm {
            Some(g) => Some(GG::alloc(
                cs.ns(|| "alloc hiding commitment for proof"),
                || Ok(g),
            )?),
            None => None,
        };

        let rand = match proof.rand {
            Some(r) => Some(Vec::<Boolean>::alloc(
                cs.ns(|| "alloc hiding randomness for proof"),
                || Ok(r.write_bits()),
            )?),
            None => None,
        };

        Ok(Self {
            vec_l,
            vec_r,
            final_comm_key,
            c,
            hiding_comm,
            rand,
        })
    }

    fn alloc_input<F, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        f: F,
    ) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Proof<G>>,
    {
        let t = f()?;
        let proof = t.borrow();
        if !proof.is_valid() {
            return Err(SynthesisError::Other(String::from(
                "invalid proof provided to alloc",
            )));
        }
        let mut vec_l = Vec::with_capacity(proof.l_vec.len());
        let mut vec_r = Vec::with_capacity(proof.r_vec.len());
        for (i, (el_vec_l, el_vec_r)) in proof.l_vec.iter().zip(proof.r_vec.iter()).enumerate() {
            vec_l.push(GG::alloc_input(
                cs.ns(|| format!("alloc left vec entry {} for proof", i)),
                || Ok(el_vec_l),
            )?);
            vec_r.push(GG::alloc_input(
                cs.ns(|| format!("alloc right vec entry {} for proof", i)),
                || Ok(el_vec_r),
            )?);
        }
        let final_comm_key =
            GG::alloc_input(cs.ns(|| "alloc final commitment key for proof"), || {
                Ok(proof.final_comm_key)
            })?;
        let c = Vec::<Boolean>::alloc(cs.ns(|| "alloc final commitment for proof"), || {
            Ok(proof.c.write_bits())
        })?;

        let hiding_comm = match proof.hiding_comm {
            Some(g) => Some(GG::alloc_input(
                cs.ns(|| "alloc hiding commitment for proof"),
                || Ok(g),
            )?),
            None => None,
        };

        let rand = match proof.rand {
            Some(r) => Some(Vec::<Boolean>::alloc_input(
                cs.ns(|| "alloc hiding randomness for proof"),
                || Ok(r.write_bits()),
            )?),
            None => None,
        };

        Ok(Self {
            vec_l,
            vec_r,
            final_comm_key,
            c,
            hiding_comm,
            rand,
        })
    }
}

// alias for the proof type of InnerProductArgGadget
type IPAProofGadgetType<ConstraintF, G, GG, FS, FSG> =
    <InnerProductArgGadget<ConstraintF, FSG, G, GG> as PolynomialCommitmentVerifierGadget<
        ConstraintF,
        G,
        InnerProductArgPC<G, FS>,
    >>::ProofGadget;
// alias for the commitment type of InnerProductArgGadget
type IPACommitmentGadgetType<ConstraintF, G, GG, FS, FSG> =
    <InnerProductArgGadget<ConstraintF, FSG, G, GG> as PolynomialCommitmentVerifierGadget<
        ConstraintF,
        G,
        InnerProductArgPC<G, FS>,
    >>::CommitmentGadget;

#[derive(Clone)]
pub struct IPAMultiPointProofGadget<
    ConstraintF: PrimeField,
    G: EndoMulCurve<BaseField = ConstraintF>,
    GG: 'static
        + EndoMulCurveGadget<G, ConstraintF, Value=G>
        + ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>,
    FS: FiatShamirRng,
    FSG: FiatShamirRngGadget<ConstraintF>,
> {
    proof: IPAProofGadgetType<ConstraintF, G, GG, FS, FSG>,
    h_commitment: IPACommitmentGadgetType<ConstraintF, G, GG, FS, FSG>,
    #[cfg(not(feature = "minimize-proof-size"))]
    evaluations: Vec<Vec<Boolean>>
}

impl<
        ConstraintF: PrimeField,
        G: EndoMulCurve<BaseField = ConstraintF>,
        GG: 'static
            + EndoMulCurveGadget<G, ConstraintF, Value=G>
            + ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>,
        FS: FiatShamirRng,
        FSG: FiatShamirRngGadget<ConstraintF>,
    > AllocGadget<MultiPointProof<G>, ConstraintF>
    for IPAMultiPointProofGadget<ConstraintF, G, GG, FS, FSG>
{
    fn alloc<F, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        f: F,
    ) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<MultiPointProof<G>>,
    {
        let t = f()?;
        let mp_proof = t.borrow();

        let proof = IPAProofGadgetType::<ConstraintF, G, GG, FS, FSG>::alloc(
            cs.ns(|| "alloc combined proof for multi-point proof"),
            || Ok(mp_proof.proof.clone()),
        )?;
        let h_commitment = GG::alloc(cs.ns(|| "alloc h-commitment for multi-point proof"), || {
            Ok(mp_proof.h_commitment)
        })?;

        #[cfg(feature = "minimize-proof-size")]
            return Ok(
            Self{
                proof,
                h_commitment,
            }
        );

        #[cfg(not(feature = "minimize-proof-size"))]
        return {
            let mut evaluations = Vec::with_capacity(mp_proof.evaluations.len());
            for (i, value) in mp_proof.evaluations.iter().enumerate() {
                evaluations.push(Vec::<Boolean>::alloc(cs.ns(|| format!("alloc evaluation {} for multi-point proof", i)), || {
                    Ok(value.write_bits())
                })?);
            }

            Ok(Self {
                proof,
                h_commitment,
                evaluations,
            })
        };
    }

    fn alloc_input<F, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        f: F,
    ) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<MultiPointProof<G>>,
    {
        let t = f()?;
        let mp_proof = t.borrow();

        let proof = IPAProofGadgetType::<ConstraintF, G, GG, FS, FSG>::alloc_input(
            cs.ns(|| "alloc combined proof for multi-point proof"),
            || Ok(mp_proof.proof.clone()),
        )?;
        let h_commitment =
            GG::alloc_input(cs.ns(|| "alloc h-commitment for multi-point proof"), || {
                Ok(mp_proof.h_commitment)
            })?;

        #[cfg(feature = "minimize-proof-size")]
            return Ok(
            Self{
                proof,
                h_commitment,
            }
        );

        #[cfg(not(feature = "minimize-proof-size"))]
        return {
            let mut evaluations = Vec::with_capacity(mp_proof.evaluations.len());
            for (i, value) in mp_proof.evaluations.iter().enumerate() {
                evaluations.push(Vec::<Boolean>::alloc_input(cs.ns(|| format!("alloc evaluation {} for multi-point proof", i)), || {
                    Ok(value.write_bits())
                })?);
            }

            Ok(Self {
                proof,
                h_commitment,
                evaluations,
            })
        };
    }
}

impl<
        ConstraintF: PrimeField,
        G: EndoMulCurve<BaseField = ConstraintF>,
        GG: 'static
            + EndoMulCurveGadget<G, ConstraintF, Value=G>
            + ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>,
        FS: FiatShamirRng,
        FSG: FiatShamirRngGadget<ConstraintF>,
    > MultiPointProofGadget<ConstraintF, G, MultiPointProof<G>>
    for IPAMultiPointProofGadget<ConstraintF, G, GG, FS, FSG>
{
    type CommitmentGadget = IPACommitmentGadgetType<ConstraintF, G, GG, FS, FSG>;
    type ProofGadget = IPAProofGadgetType<ConstraintF, G, GG, FS, FSG>;

    fn get_proof(&self) -> &Self::ProofGadget {
        &self.proof
    }

    fn get_h_commitment(&self) -> &Self::CommitmentGadget {
        &self.h_commitment
    }

    #[cfg(not(feature = "minimize-proof-size"))]
    fn get_evaluations(&self) -> &Vec<Vec<Boolean>> {
        &self.evaluations
    }
}
