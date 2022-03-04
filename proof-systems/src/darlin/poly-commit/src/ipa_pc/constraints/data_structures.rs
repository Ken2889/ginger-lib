use crate::ipa_pc::constraints::InnerProductArgGadget;
use crate::ipa_pc::{InnerProductArgPC, MultiPointProof, Proof, VerifierKey, VerifierState};
use crate::{MultiPointProofGadget, PCVerifierKey, PolynomialCommitmentVerifierGadget, VerifierKeyGadget, VerifierStateGadget};
use algebra::{EndoMulCurve, PrimeField, SemanticallyValid, ToBits};
use fiat_shamir::constraints::FiatShamirRngGadget;
use fiat_shamir::FiatShamirRng;
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use r1cs_std::fields::fp::FpGadget;
use r1cs_std::fields::nonnative::nonnative_field_gadget::NonNativeFieldGadget;
use r1cs_std::prelude::{AllocGadget, EndoMulCurveGadget};
use r1cs_std::to_field_gadget_vec::ToConstraintFieldGadget;
use std::{borrow::Borrow, marker::PhantomData};
use r1cs_std::boolean::Boolean;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IPAVerifierKeyGadget<
    ConstraintF: PrimeField,
    G: EndoMulCurve<BaseField = ConstraintF>,
    GG: EndoMulCurveGadget<G, ConstraintF>,
> {
    segment_size: usize,
    pub(crate) h: GG,
    pub(crate) s: GG,
    hash: Vec<u8>,
    _group_phantom: PhantomData<G>,
    _constraint_field_phantom: PhantomData<ConstraintF>,
}

impl<
    ConstraintF: PrimeField,
    G: EndoMulCurve<BaseField = ConstraintF>,
    GG: EndoMulCurveGadget<G, ConstraintF>,
> VerifierKeyGadget<VerifierKey<G>, ConstraintF> for IPAVerifierKeyGadget<ConstraintF, G, GG> {
    fn segment_size(&self) -> usize {
        self.segment_size
    }

    fn get_hash(&self) -> &[u8] {
        self.hash.as_slice()
    }
}

impl<
        ConstraintF: PrimeField,
        G: EndoMulCurve<BaseField = ConstraintF>,
        GG: EndoMulCurveGadget<G, ConstraintF>,
    > AllocGadget<VerifierKey<G>, ConstraintF> for IPAVerifierKeyGadget<ConstraintF, G, GG>
{
    fn alloc<F, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        f: F,
    ) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<VerifierKey<G>>,
    {
        let t = f()?;
        let vk = t.borrow();

        let h = GG::alloc(cs.ns(|| "alloc base point h"), || Ok(vk.h))?;
        let s = GG::alloc(cs.ns(|| "alloc base point s"), || Ok(vk.s))?;

        Ok(Self {
            segment_size: vk.segment_size(),
            h,
            s,
            hash: vk.hash.clone(),
            _group_phantom: PhantomData,
            _constraint_field_phantom: PhantomData,
        })
    }

    fn alloc_input<F, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        f: F,
    ) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<VerifierKey<G>>,
    {
        let t = f()?;
        let vk = t.borrow();

        let h = GG::alloc_input(cs.ns(|| "alloc base point h"), || Ok(vk.h))?;
        let s = GG::alloc_input(cs.ns(|| "alloc base point s"), || Ok(vk.s))?;

        Ok(Self {
            segment_size: vk.segment_size(),
            h,
            s,
            hash: vk.hash.clone(),
            _group_phantom: PhantomData,
            _constraint_field_phantom: PhantomData,
        })
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BulletPolynomial<ConstraintF: PrimeField, G: EndoMulCurve<BaseField = ConstraintF>>(
    Vec<NonNativeFieldGadget<G::ScalarField, ConstraintF>>,
);

impl<ConstraintF: PrimeField, G: EndoMulCurve<BaseField = ConstraintF>>
    BulletPolynomial<ConstraintF, G>
{
    pub fn new(challenges: Vec<NonNativeFieldGadget<G::ScalarField, ConstraintF>>) -> Self {
        BulletPolynomial(challenges)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IPAVerifierState<
    ConstraintF: PrimeField,
    G: EndoMulCurve<BaseField = ConstraintF>,
    GG: EndoMulCurveGadget<G, ConstraintF>,
> {
    check_poly: BulletPolynomial<ConstraintF, G>,
    final_comm_key: GG,
}

impl<
        ConstraintF: PrimeField,
        G: EndoMulCurve<BaseField = ConstraintF>,
        GG: EndoMulCurveGadget<G, ConstraintF>,
    > IPAVerifierState<ConstraintF, G, GG>
{
    pub fn new(check_poly: BulletPolynomial<ConstraintF, G>, final_comm_key: GG) -> Self {
        Self {
            check_poly,
            final_comm_key,
        }
    }
}

impl<
        ConstraintF: PrimeField,
        G: EndoMulCurve<BaseField = ConstraintF>,
        GG: EndoMulCurveGadget<G, ConstraintF>,
    > VerifierStateGadget<VerifierState<G>, ConstraintF> for IPAVerifierState<ConstraintF, G, GG>
{
}

impl<
        ConstraintF: PrimeField,
        G: EndoMulCurve<BaseField = ConstraintF>,
        GG: EndoMulCurveGadget<G, ConstraintF>,
    > AllocGadget<VerifierState<G>, ConstraintF> for IPAVerifierState<ConstraintF, G, GG>
{
    fn alloc<F, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        f: F,
    ) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<VerifierState<G>>,
    {
        let t = f()?;
        let verifier_state = t.borrow();

        let mut check_poly = Vec::with_capacity(verifier_state.check_poly.0.len());
        for (i, challenge) in verifier_state.check_poly.0.iter().enumerate() {
            check_poly.push(NonNativeFieldGadget::<G::ScalarField, ConstraintF>::alloc(
                cs.ns(|| format!("alloc {}-th challenge for bullet polynomial", i + 1)),
                || Ok(challenge),
            )?);
        }

        let final_comm_key = GG::alloc(cs.ns(|| "alloc final commitment key"), || {
            Ok(verifier_state.final_comm_key)
        })?;

        Ok(Self {
            check_poly: BulletPolynomial(check_poly),
            final_comm_key,
        })
    }

    fn alloc_input<F, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        f: F,
    ) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<VerifierState<G>>,
    {
        let t = f()?;
        let verifier_state = t.borrow();

        let mut check_poly = Vec::with_capacity(verifier_state.check_poly.0.len());
        for (i, challenge) in verifier_state.check_poly.0.iter().enumerate() {
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
            check_poly: BulletPolynomial(check_poly),
            final_comm_key,
        })
    }
}

#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
pub struct IPAProofGadget<
    ConstraintF: PrimeField,
    G: EndoMulCurve<BaseField = ConstraintF>,
    GG: EndoMulCurveGadget<G, ConstraintF> + ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>,
    FS: FiatShamirRng,
    FSG: FiatShamirRngGadget<ConstraintF>
> {
    pub(crate) vec_l: Vec<IPACommitment<ConstraintF, G, GG, FS, FSG>>,
    pub(crate) vec_r: Vec<IPACommitment<ConstraintF, G, GG, FS, FSG>>,
    pub(crate) final_comm_key: IPACommitment<ConstraintF, G, GG, FS, FSG>,
    pub(crate) c: Vec<Boolean>,
    pub(crate) hiding_comm: Option<IPACommitment<ConstraintF, G, GG, FS, FSG>>,
    pub(crate) rand: Option<Vec<Boolean>>,
}

impl<
        ConstraintF: PrimeField,
        G: EndoMulCurve<BaseField = ConstraintF>,
        GG: EndoMulCurveGadget<G, ConstraintF> + ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>,
        FS: FiatShamirRng,
        FSG: FiatShamirRngGadget<ConstraintF>
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
type IPAProof<ConstraintF, G, GG, FS, FSG> =
    <InnerProductArgGadget<ConstraintF, FSG, G, GG> as PolynomialCommitmentVerifierGadget<
        ConstraintF,
        G,
        InnerProductArgPC<G, FS>,
    >>::Proof;
// alias for the commitment type of InnerProductArgGadget
type IPACommitment<ConstraintF, G, GG, FS, FSG> =
    <InnerProductArgGadget<ConstraintF, FSG, G, GG> as PolynomialCommitmentVerifierGadget<
        ConstraintF,
        G,
        InnerProductArgPC<G, FS>,
    >>::Commitment;

#[derive(Clone)]
pub struct IPAMultiPointProof<
    ConstraintF: PrimeField,
    G: EndoMulCurve<BaseField = ConstraintF>,
    GG: EndoMulCurveGadget<G, ConstraintF>
        + ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>,
    FS: FiatShamirRng,
    FSG: FiatShamirRngGadget<ConstraintF>,
> {
    proof: IPAProof<ConstraintF, G, GG, FS, FSG>,
    h_commitment: IPACommitment<ConstraintF, G, GG, FS, FSG>,
}

impl<
        ConstraintF: PrimeField,
        G: EndoMulCurve<BaseField = ConstraintF>,
        GG: EndoMulCurveGadget<G, ConstraintF>
            + ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>,
        FS: FiatShamirRng,
        FSG: FiatShamirRngGadget<ConstraintF>,
    > AllocGadget<MultiPointProof<G>, ConstraintF>
    for IPAMultiPointProof<ConstraintF, G, GG, FS, FSG>
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

        let proof = IPAProof::<ConstraintF, G, GG, FS, FSG>::alloc(
            cs.ns(|| "alloc combined proof for multi-point proof"),
            || Ok(mp_proof.proof.clone()),
        )?;
        let h_commitment = GG::alloc(cs.ns(|| "alloc h-commitment for multi-point proof"), || {
            Ok(mp_proof.h_commitment)
        })?;

        Ok(Self {
            proof,
            h_commitment,
        })
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

        let proof = IPAProof::<ConstraintF, G, GG, FS, FSG>::alloc_input(
            cs.ns(|| "alloc combined proof for multi-point proof"),
            || Ok(mp_proof.proof.clone()),
        )?;
        let h_commitment =
            GG::alloc_input(cs.ns(|| "alloc h-commitment for multi-point proof"), || {
                Ok(mp_proof.h_commitment)
            })?;

        Ok(Self {
            proof,
            h_commitment,
        })
    }
}

impl<
        ConstraintF: PrimeField,
        G: EndoMulCurve<BaseField = ConstraintF>,
        GG: EndoMulCurveGadget<G, ConstraintF>
            + ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>,
        FS: FiatShamirRng,
        FSG: FiatShamirRngGadget<ConstraintF>,
    > MultiPointProofGadget<ConstraintF, G, MultiPointProof<G>>
    for IPAMultiPointProof<ConstraintF, G, GG, FS, FSG>
{
    type Commitment = IPACommitment<ConstraintF, G, GG, FS, FSG>;
    type Proof = IPAProof<ConstraintF, G, GG, FS, FSG>;

    fn get_proof(&self) -> &Self::Proof {
        &self.proof
    }

    fn get_h_commitment(&self) -> &Self::Commitment {
        &self.h_commitment
    }
}
