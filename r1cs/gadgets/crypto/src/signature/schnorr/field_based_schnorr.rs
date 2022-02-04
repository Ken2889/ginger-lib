use crate::{crh::FieldBasedHashGadget, signature::FieldBasedSigGadget};
use algebra::{Curve, PrimeField, ToConstraintField};
use primitives::signature::schnorr::field_based_schnorr::FieldBasedSchnorrPk;
use primitives::{
    compute_truncation_size,
    crh::FieldBasedHash,
    signature::schnorr::field_based_schnorr::{
        FieldBasedSchnorrSignature, FieldBasedSchnorrSignatureScheme,
    },
};
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use r1cs_std::alloc::ConstantGadget;
use r1cs_std::{
    alloc::AllocGadget, bits::boolean::Boolean, eq::EqGadget, fields::fp::FpGadget,
    groups::GroupGadget, to_field_gadget_vec::ToConstraintFieldGadget,
};
use std::{borrow::Borrow, marker::PhantomData};

#[derive(Derivative)]
#[derivative(
    Debug(bound = "ConstraintF: PrimeField, G: Curve"),
    Clone(bound = "ConstraintF: PrimeField, G: Curve"),
    PartialEq(bound = "ConstraintF: PrimeField, G: Curve"),
    Eq(bound = "ConstraintF: PrimeField, G: Curve")
)]
pub struct FieldBasedSchnorrSigGadget<ConstraintF: PrimeField, G: Curve> {
    pub e: FpGadget<ConstraintF>,
    pub s: FpGadget<ConstraintF>,
    _field: PhantomData<ConstraintF>,
    _group: PhantomData<G>,
}

impl<ConstraintF, G> AllocGadget<FieldBasedSchnorrSignature<ConstraintF, G>, ConstraintF>
    for FieldBasedSchnorrSigGadget<ConstraintF, G>
where
    ConstraintF: PrimeField,
    G: Curve,
{
    fn alloc<FN, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        f: FN,
    ) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<FieldBasedSchnorrSignature<ConstraintF, G>>,
    {
        let (e, s) = match f() {
            Ok(sig) => {
                let sig = *sig.borrow();
                (Ok(sig.e), Ok(sig.s))
            }
            _ => (
                Err(SynthesisError::AssignmentMissing),
                Err(SynthesisError::AssignmentMissing),
            ),
        };

        let e = FpGadget::<ConstraintF>::alloc(cs.ns(|| "alloc e"), || e)?;
        let s = FpGadget::<ConstraintF>::alloc(cs.ns(|| "alloc s"), || s)?;
        Ok(Self {
            e,
            s,
            _field: PhantomData,
            _group: PhantomData,
        })
    }

    fn alloc_input<FN, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        f: FN,
    ) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<FieldBasedSchnorrSignature<ConstraintF, G>>,
    {
        let (e, s) = match f() {
            Ok(sig) => {
                let sig = *sig.borrow();
                (Ok(sig.e), Ok(sig.s))
            }
            _ => (
                Err(SynthesisError::AssignmentMissing),
                Err(SynthesisError::AssignmentMissing),
            ),
        };

        let e = FpGadget::<ConstraintF>::alloc_input(cs.ns(|| "alloc e"), || e)?;
        let s = FpGadget::<ConstraintF>::alloc_input(cs.ns(|| "alloc s"), || s)?;
        Ok(Self {
            e,
            s,
            _field: PhantomData,
            _group: PhantomData,
        })
    }
}

impl<ConstraintF, G> ConstantGadget<FieldBasedSchnorrSignature<ConstraintF, G>, ConstraintF>
    for FieldBasedSchnorrSigGadget<ConstraintF, G>
where
    ConstraintF: PrimeField,
    G: Curve,
{
    fn from_value<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        value: &FieldBasedSchnorrSignature<ConstraintF, G>,
    ) -> Self {
        let e = FpGadget::<ConstraintF>::from_value(cs.ns(|| "hardcode e"), &value.e);
        let s = FpGadget::<ConstraintF>::from_value(cs.ns(|| "hardcode s"), &value.s);
        Self {
            e,
            s,
            _field: PhantomData,
            _group: PhantomData,
        }
    }

    fn get_constant(&self) -> FieldBasedSchnorrSignature<ConstraintF, G> {
        let e = self.e.value.unwrap();
        let s = self.s.value.unwrap();
        FieldBasedSchnorrSignature::<ConstraintF, G>::new(e, s)
    }
}

impl<ConstraintF, G> EqGadget<ConstraintF> for FieldBasedSchnorrSigGadget<ConstraintF, G>
where
    ConstraintF: PrimeField,
    G: Curve,
{
    fn is_eq<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Boolean, SynthesisError> {
        let b1 = self.e.is_eq(cs.ns(|| "b1"), &other.e)?;
        let b2 = self.s.is_eq(cs.ns(|| "b2"), &other.s)?;
        Boolean::and(cs.ns(|| "b1 && b2"), &b1, &b2)
    }

    fn conditional_enforce_equal<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
        should_enforce: &Boolean,
    ) -> Result<(), SynthesisError> {
        self.e.conditional_enforce_equal(
            cs.ns(|| "self.e =? other.e"),
            &other.e,
            should_enforce,
        )?;
        self.s.conditional_enforce_equal(
            cs.ns(|| "self.s =? other.s"),
            &other.s,
            should_enforce,
        )?;
        Ok(())
    }

    fn conditional_enforce_not_equal<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
        should_enforce: &Boolean,
    ) -> Result<(), SynthesisError> {
        self.e.conditional_enforce_not_equal(
            cs.ns(|| "self.e !=? other.e"),
            &other.e,
            should_enforce,
        )?;
        self.s.conditional_enforce_not_equal(
            cs.ns(|| "self.s !=? other.s"),
            &other.s,
            should_enforce,
        )?;
        Ok(())
    }
}

impl<ConstraintF, G> ToConstraintFieldGadget<ConstraintF>
    for FieldBasedSchnorrSigGadget<ConstraintF, G>
where
    ConstraintF: PrimeField,
    G: Curve,
{
    type FieldGadget = FpGadget<ConstraintF>;

    fn to_field_gadget_elements<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        _cs: CS,
    ) -> Result<Vec<Self::FieldGadget>, SynthesisError> {
        Ok(vec![self.e.clone(), self.s.clone()])
    }
}

#[derive(Clone, Eq, PartialEq)]
pub struct FieldBasedSchnorrPkGadget<
    ConstraintF: PrimeField,
    G: Curve,
    GG: GroupGadget<G, ConstraintF>,
> {
    pub pk: GG,
    _field: PhantomData<ConstraintF>,
    _group: PhantomData<G>,
}

impl<ConstraintF, G, GG> AllocGadget<FieldBasedSchnorrPk<G>, ConstraintF>
    for FieldBasedSchnorrPkGadget<ConstraintF, G, GG>
where
    ConstraintF: PrimeField,
    G: Curve,
    GG: GroupGadget<G, ConstraintF>,
{
    fn alloc<F, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        f: F,
    ) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<FieldBasedSchnorrPk<G>>,
    {
        let pk =
            GG::alloc(cs.ns(|| "alloc pk"), || f().map(|pk| pk.borrow().0)).and_then(|pk_g| {
                pk_g.is_zero(cs.ns(|| "is pk zero"))?
                    .enforce_equal(cs.ns(|| "pk must not be zero"), &Boolean::constant(false))?;
                Ok(pk_g)
            })?;
        Ok(Self {
            pk,
            _field: PhantomData,
            _group: PhantomData,
        })
    }

    fn alloc_without_check<F, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        f: F,
    ) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<FieldBasedSchnorrPk<G>>,
    {
        let pk = GG::alloc_without_check(cs.ns(|| "alloc pk"), || f().map(|pk| pk.borrow().0))?;
        Ok(Self {
            pk,
            _field: PhantomData,
            _group: PhantomData,
        })
    }

    fn alloc_checked<F, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        f: F,
    ) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<FieldBasedSchnorrPk<G>>,
    {
        let pk = GG::alloc_checked(cs.ns(|| "alloc pk checked"), || f().map(|pk| pk.borrow().0))
            .and_then(|pk_g| {
                pk_g.is_zero(cs.ns(|| "is pk zero"))?
                    .enforce_equal(cs.ns(|| "pk must not be zero"), &Boolean::constant(false))?;
                Ok(pk_g)
            })?;
        Ok(Self {
            pk,
            _field: PhantomData,
            _group: PhantomData,
        })
    }

    fn alloc_input<F, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        f: F,
    ) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<FieldBasedSchnorrPk<G>>,
    {
        let pk = GG::alloc_input(cs.ns(|| "alloc pk"), || f().map(|pk| pk.borrow().0))?;
        Ok(Self {
            pk,
            _field: PhantomData,
            _group: PhantomData,
        })
    }
}

impl<ConstraintF, G, GG> ConstantGadget<FieldBasedSchnorrPk<G>, ConstraintF>
    for FieldBasedSchnorrPkGadget<ConstraintF, G, GG>
where
    ConstraintF: PrimeField,
    G: Curve,
    GG: GroupGadget<G, ConstraintF, Value = G>,
{
    fn from_value<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        value: &FieldBasedSchnorrPk<G>,
    ) -> Self {
        let pk = GG::from_value(cs.ns(|| "hardcode pk"), &value.0);
        Self {
            pk,
            _field: PhantomData,
            _group: PhantomData,
        }
    }

    fn get_constant(&self) -> FieldBasedSchnorrPk<G> {
        FieldBasedSchnorrPk::<G>(self.pk.get_value().unwrap())
    }
}

impl<ConstraintF, G, GG> EqGadget<ConstraintF> for FieldBasedSchnorrPkGadget<ConstraintF, G, GG>
where
    ConstraintF: PrimeField,
    G: Curve,
    GG: GroupGadget<G, ConstraintF, Value = G>,
{
    fn is_eq<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
        other: &Self,
    ) -> Result<Boolean, SynthesisError> {
        self.pk.is_eq(cs, &other.pk)
    }

    fn conditional_enforce_equal<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
        other: &Self,
        should_enforce: &Boolean,
    ) -> Result<(), SynthesisError> {
        self.pk
            .conditional_enforce_equal(cs, &other.pk, should_enforce)
    }

    fn conditional_enforce_not_equal<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
        other: &Self,
        should_enforce: &Boolean,
    ) -> Result<(), SynthesisError> {
        self.pk
            .conditional_enforce_not_equal(cs, &other.pk, should_enforce)
    }
}

impl<ConstraintF, G, GG> ToConstraintFieldGadget<ConstraintF>
    for FieldBasedSchnorrPkGadget<ConstraintF, G, GG>
where
    ConstraintF: PrimeField,
    G: Curve,
    GG: GroupGadget<G, ConstraintF, Value = G>
        + ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>,
{
    type FieldGadget = FpGadget<ConstraintF>;

    fn to_field_gadget_elements<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<Self::FieldGadget>, SynthesisError> {
        self.pk.to_field_gadget_elements(cs)
    }
}

pub struct FieldBasedSchnorrSigVerificationGadget<
    ConstraintF: PrimeField,
    G: Curve,
    GG: GroupGadget<G, ConstraintF>,
    H: FieldBasedHash<Data = ConstraintF>,
    HG: FieldBasedHashGadget<H, ConstraintF>,
> {
    _field: PhantomData<ConstraintF>,
    _group: PhantomData<G>,
    _group_gadget: PhantomData<GG>,
    _hash: PhantomData<H>,
    _hash_gadget: PhantomData<HG>,
}

// This implementation supports both complete and incomplete (safe) point addition.
// Assumes provided key material to be already checked.
//
// In case of incomplete point addition, with negligible probability, the
// proof creation might fail at first attempt and must be re-run (in order to sample
// fresh randomnesses).
// Furthermore, one exceptional case (e, s) has to be treated outside the circuit:
// if e * pk = s * G, i.e. when R' is trivial (therefore leaking the sk), then
// the circuit is not satisfiable.
impl<ConstraintF, G, GG, H, HG> FieldBasedSchnorrSigVerificationGadget<ConstraintF, G, GG, H, HG>
where
    ConstraintF: PrimeField,
    G: Curve + ToConstraintField<ConstraintF>,
    GG: GroupGadget<G, ConstraintF, Value = G>
        + ToConstraintFieldGadget<ConstraintF, FieldGadget = HG::DataGadget>,
    H: FieldBasedHash<Data = ConstraintF>,
    HG: FieldBasedHashGadget<H, ConstraintF, DataGadget = FpGadget<ConstraintF>>,
{
    fn enforce_signature_computation<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        public_key: &GG,
        signature: &FieldBasedSchnorrSigGadget<ConstraintF, G>,
        message: FpGadget<ConstraintF>,
    ) -> Result<FpGadget<ConstraintF>, SynthesisError> {
        //Enforce e' * pk
        let e_bits = {
            //Serialize e taking into account the length restriction
            let to_skip = compute_truncation_size(
                ConstraintF::size_in_bits() as i32,
                G::ScalarField::size_in_bits() as i32,
            );

            let e_bits = signature
                .e
                .to_bits_with_length_restriction(cs.ns(|| "e_to_bits"), to_skip)?;

            debug_assert!(e_bits.len() == ConstraintF::size_in_bits() - to_skip);
            e_bits
        };

        let neg_e_times_pk =
            public_key.mul_bits(cs.ns(|| "pk * e"), e_bits.as_slice().iter().rev())?;

        //Enforce s * G and R' = s*G - e*pk
        let mut s_bits = {
            //Serialize s taking into account the length restriction

            //Before computing the number of bits to truncate from s, we first have to normalize
            //it, i.e. considering its number of bits equals to G::ScalarField::MODULUS_BITS;
            let moduli_diff =
                ConstraintF::size_in_bits() as i32 - G::ScalarField::size_in_bits() as i32;
            let to_skip_init = (if moduli_diff > 0 { moduli_diff } else { 0 }) as usize;

            //Now we can compare the two moduli and decide the bits to truncate
            let to_skip = to_skip_init
                + compute_truncation_size(
                    G::ScalarField::size_in_bits() as i32,
                    ConstraintF::size_in_bits() as i32,
                );

            let s_bits = signature
                .s
                .to_bits_with_length_restriction(cs.ns(|| "s_to_bits"), to_skip as usize)?;

            debug_assert!(s_bits.len() == G::ScalarField::size_in_bits() + to_skip_init - to_skip);
            s_bits
        };

        s_bits.reverse();
        let g = GG::from_value(
            cs.ns(|| "hardcode generator"),
            &G::prime_subgroup_generator(),
        );
        let r_prime =
            GG::mul_bits_fixed_base(&g.get_constant(), cs.ns(|| "(s * G)"), s_bits.as_slice())?
                // If add is incomplete, and s * G - e * pk = 0, the circuit of the add won't be satisfiable
                .sub(cs.ns(|| "s * G - e * pk "), &neg_e_times_pk)?;

        let r_prime_coords = r_prime.to_field_gadget_elements(cs.ns(|| "r_prime to fes"))?;

        // Check e' = H(m || R' || pk.x)
        // Best constraints-efficiency is achieved when m is one field element
        // (or an odd number of field elements).
        let mut hash_input = Vec::new();
        hash_input.push(message);
        hash_input.extend_from_slice(r_prime_coords.as_slice());
        hash_input.push(
            public_key
                .to_field_gadget_elements(cs.ns(|| "pk to fes"))
                .unwrap()[0]
                .clone(),
        );

        HG::enforce_hash_constant_length(cs.ns(|| "check e_prime"), hash_input.as_slice())
    }
}

impl<ConstraintF, G, GG, H, HG>
    FieldBasedSigGadget<FieldBasedSchnorrSignatureScheme<ConstraintF, G, H>, ConstraintF>
    for FieldBasedSchnorrSigVerificationGadget<ConstraintF, G, GG, H, HG>
where
    ConstraintF: PrimeField,
    G: Curve + ToConstraintField<ConstraintF>,
    GG: GroupGadget<G, ConstraintF, Value = G>
        + ToConstraintFieldGadget<ConstraintF, FieldGadget = HG::DataGadget>,
    H: FieldBasedHash<Data = ConstraintF>,
    HG: FieldBasedHashGadget<H, ConstraintF, DataGadget = FpGadget<ConstraintF>>,
{
    type DataGadget = FpGadget<ConstraintF>;
    type SignatureGadget = FieldBasedSchnorrSigGadget<ConstraintF, G>;
    type PublicKeyGadget = FieldBasedSchnorrPkGadget<ConstraintF, G, GG>;

    fn enforce_signature_verdict<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        public_key: &Self::PublicKeyGadget,
        signature: &Self::SignatureGadget,
        message: Self::DataGadget,
    ) -> Result<Boolean, SynthesisError> {
        let e_prime = Self::enforce_signature_computation(
            cs.ns(|| "is sig verified"),
            &public_key.pk,
            signature,
            message,
        )?;

        //Enforce result of signature verification
        let is_verified = signature.e.is_eq(cs.ns(|| "is e == e_prime"), &e_prime)?;

        Ok(is_verified)
    }

    fn conditionally_enforce_signature_verification<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        public_key: &Self::PublicKeyGadget,
        signature: &Self::SignatureGadget,
        message: Self::DataGadget,
        should_enforce: &Boolean,
    ) -> Result<(), SynthesisError> {
        let e_prime = Self::enforce_signature_computation(
            cs.ns(|| "is sig verified"),
            &public_key.pk,
            signature,
            message,
        )?;
        signature.e.conditional_enforce_equal(
            cs.ns(|| "conditional verify signature"),
            &e_prime,
            should_enforce,
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use algebra::curves::{tweedle::dee::DeeJacobian, tweedle::dum::DumJacobian};
    use algebra::fields::tweedle::{Fq, Fr};

    use primitives::{
        crh::{TweedleFqPoseidonHash, TweedleFrPoseidonHash},
        signature::{schnorr::field_based_schnorr::*, FieldBasedSignatureScheme},
    };

    use crate::{
        crh::{TweedleFqPoseidonHashGadget, TweedleFrPoseidonHashGadget},
        signature::{schnorr::field_based_schnorr::*, FieldBasedSigGadget},
    };

    use r1cs_core::{
        ConstraintSystem, ConstraintSystemAbstract, ConstraintSystemDebugger, SynthesisMode,
    };
    use r1cs_std::alloc::AllocGadget;

    use r1cs_std::instantiated::tweedle::{TweedleDeeGadget, TweedleDumGadget};

    use rand::{thread_rng, Rng};

    type SchnorrTweedleDee =
        FieldBasedSchnorrSignatureScheme<Fr, DumJacobian, TweedleFrPoseidonHash>;
    type SchnorrTweedleDum =
        FieldBasedSchnorrSignatureScheme<Fq, DeeJacobian, TweedleFqPoseidonHash>;

    type SchnorrTweedleDeeSig = FieldBasedSchnorrSignature<Fr, DumJacobian>;
    type SchnorrTweedleDumSig = FieldBasedSchnorrSignature<Fq, DeeJacobian>;

    type SchnorrTweedleDeePk = FieldBasedSchnorrPk<DumJacobian>;
    type SchnorrTweedleDumPk = FieldBasedSchnorrPk<DeeJacobian>;

    type SchnorrTweedleDeeGadget = FieldBasedSchnorrSigVerificationGadget<
        Fr,
        DumJacobian,
        TweedleDumGadget,
        TweedleFrPoseidonHash,
        TweedleFrPoseidonHashGadget,
    >;
    type SchnorrTweedleDumGadget = FieldBasedSchnorrSigVerificationGadget<
        Fq,
        DeeJacobian,
        TweedleDeeGadget,
        TweedleFqPoseidonHash,
        TweedleFqPoseidonHashGadget,
    >;

    fn sign<S: FieldBasedSignatureScheme, R: Rng>(
        rng: &mut R,
        message: S::Data,
    ) -> (S::Signature, S::PublicKey) {
        let (pk, sk) = S::keygen(rng);
        assert!(S::keyverify(&pk));
        let sig = S::sign(rng, &pk, &sk, message).unwrap();
        (sig, pk)
    }

    fn tweedle_dee_schnorr_gadget_generate_constraints(
        message: Fr,
        pk: &SchnorrTweedleDeePk,
        sig: SchnorrTweedleDeeSig,
    ) -> bool {
        let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

        //Alloc signature, pk and message
        let sig_g = <SchnorrTweedleDeeGadget as FieldBasedSigGadget<SchnorrTweedleDee, Fr>>::SignatureGadget::alloc(
            cs.ns(|| "alloc sig"),
            || Ok(sig)
        ).unwrap();
        let pk_g = <SchnorrTweedleDeeGadget as FieldBasedSigGadget<SchnorrTweedleDee, Fr>>::PublicKeyGadget::alloc(cs.ns(|| "alloc pk"), || Ok(pk)).unwrap();
        let message_g =
            <SchnorrTweedleDeeGadget as FieldBasedSigGadget<SchnorrTweedleDee, Fr>>::DataGadget::alloc(
                cs.ns(|| "alloc message"),
                || Ok(message),
            )
            .unwrap();

        //Verify sig
        SchnorrTweedleDeeGadget::enforce_signature_verification(
            cs.ns(|| "verify sig1"),
            &pk_g,
            &sig_g,
            message_g.clone(),
        )
        .unwrap();

        let is_cs_satisfied = cs.is_satisfied();

        //Verify sig
        let is_verified = SchnorrTweedleDeeGadget::enforce_signature_verdict(
            cs.ns(|| "sig1 result"),
            &pk_g,
            &sig_g,
            message_g,
        )
        .unwrap();

        assert_eq!(is_verified.get_value().unwrap(), is_cs_satisfied);

        if !is_cs_satisfied {
            println!("**********Unsatisfied constraints***********");
            println!("{:?}", cs.which_is_unsatisfied());
        }

        is_cs_satisfied
    }

    #[test]
    fn tweedle_dee_schnorr_gadget_test() {
        //Sign a random field element f and get the signature and the public key
        let rng = &mut thread_rng();
        let message: Fr = rng.gen();
        let (sig, pk) = sign::<SchnorrTweedleDee, _>(rng, message);

        //Positive case
        assert!(tweedle_dee_schnorr_gadget_generate_constraints(
            message, &pk, sig
        ));

        //Change message
        let wrong_message: Fr = rng.gen();
        assert!(!tweedle_dee_schnorr_gadget_generate_constraints(
            wrong_message,
            &pk,
            sig
        ));

        //Change pk
        let wrong_pk: SchnorrTweedleDeePk = rng.gen();
        assert!(!tweedle_dee_schnorr_gadget_generate_constraints(
            message, &wrong_pk, sig
        ));

        //Change sig
        let (wrong_sig, _) = sign::<SchnorrTweedleDee, _>(rng, wrong_message);
        assert!(!tweedle_dee_schnorr_gadget_generate_constraints(
            message, &pk, wrong_sig
        ));
    }

    fn tweedle_dum_schnorr_gadget_generate_constraints(
        message: Fq,
        pk: &SchnorrTweedleDumPk,
        sig: SchnorrTweedleDumSig,
    ) -> bool {
        let mut cs = ConstraintSystem::<Fq>::new(SynthesisMode::Debug);

        //Alloc signature, pk and message
        let sig_g = <SchnorrTweedleDumGadget as FieldBasedSigGadget<SchnorrTweedleDum, Fq>>::SignatureGadget::alloc(
            cs.ns(|| "alloc sig"),
            || Ok(sig)
        ).unwrap();
        let pk_g = <SchnorrTweedleDumGadget as FieldBasedSigGadget<SchnorrTweedleDum, Fq>>::PublicKeyGadget::alloc(cs.ns(|| "alloc pk"), || Ok(pk)).unwrap();
        let message_g =
            <SchnorrTweedleDumGadget as FieldBasedSigGadget<SchnorrTweedleDum, Fq>>::DataGadget::alloc(
                cs.ns(|| "alloc message"),
                || Ok(message),
            )
            .unwrap();

        //Verify sig
        SchnorrTweedleDumGadget::enforce_signature_verification(
            cs.ns(|| "verify sig1"),
            &pk_g,
            &sig_g,
            message_g.clone(),
        )
        .unwrap();

        let is_cs_satisfied = cs.is_satisfied();

        let is_verified = SchnorrTweedleDumGadget::enforce_signature_verdict(
            cs.ns(|| "sig1 result"),
            &pk_g,
            &sig_g,
            message_g,
        )
        .unwrap();

        assert_eq!(is_verified.get_value().unwrap(), is_cs_satisfied);

        if !is_cs_satisfied {
            println!("**********Unsatisfied constraints***********");
            println!("{:?}", cs.which_is_unsatisfied());
        }

        is_cs_satisfied
    }

    #[test]
    fn tweedle_dum_schnorr_gadget_test() {
        //Sign a random field element f and get the signature and the public key
        let rng = &mut thread_rng();
        let message: Fq = rng.gen();
        let (sig, pk) = sign::<SchnorrTweedleDum, _>(rng, message);

        //Positive case
        assert!(tweedle_dum_schnorr_gadget_generate_constraints(
            message, &pk, sig
        ));

        //Change message
        let wrong_message: Fq = rng.gen();
        assert!(!tweedle_dum_schnorr_gadget_generate_constraints(
            wrong_message,
            &pk,
            sig
        ));

        //Change pk
        let wrong_pk: SchnorrTweedleDumPk = rng.gen();
        assert!(!tweedle_dum_schnorr_gadget_generate_constraints(
            message, &wrong_pk, sig
        ));

        //Change sig
        let (wrong_sig, _) = sign::<SchnorrTweedleDum, _>(rng, wrong_message);
        assert!(!tweedle_dum_schnorr_gadget_generate_constraints(
            message, &pk, wrong_sig
        ));
    }

    #[test]
    fn random_schnorr_gadget_test() {
        let rng = &mut thread_rng();

        let samples = 10;
        for _ in 0..samples {
            let message: Fr = rng.gen();
            let (sig, pk) = sign::<SchnorrTweedleDee, _>(rng, message);
            let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

            //Alloc signature, pk and message
            let sig_g = <SchnorrTweedleDeeGadget as FieldBasedSigGadget<SchnorrTweedleDee, Fr>>::SignatureGadget::alloc(
                cs.ns(|| "alloc sig"),
                || Ok(sig)
            ).unwrap();

            let pk_g = <SchnorrTweedleDeeGadget as FieldBasedSigGadget<SchnorrTweedleDee, Fr>>::PublicKeyGadget::alloc(
                cs.ns(|| "alloc pk"),
                || Ok(pk)
            ).unwrap();

            let message_g = <SchnorrTweedleDeeGadget as FieldBasedSigGadget<
                SchnorrTweedleDee,
                Fr,
            >>::DataGadget::alloc(cs.ns(|| "alloc message"), || {
                Ok(message)
            })
            .unwrap();

            //Verify sig
            let is_verified = SchnorrTweedleDeeGadget::enforce_signature_verdict(
                cs.ns(|| "sig result"),
                &pk_g,
                &sig_g,
                message_g.clone(),
            )
            .unwrap();

            assert!(is_verified.get_value().unwrap());

            SchnorrTweedleDeeGadget::enforce_signature_verification(
                cs.ns(|| "verify sig"),
                &pk_g,
                &sig_g,
                message_g,
            )
            .unwrap();

            assert!(cs.is_satisfied());

            //Negative case: wrong message (or wrong sig for another message)
            let new_message: Fr = rng.gen();
            let new_message_g = <SchnorrTweedleDeeGadget as FieldBasedSigGadget<
                SchnorrTweedleDee,
                Fr,
            >>::DataGadget::alloc(
                cs.ns(|| "alloc new_message"), || Ok(new_message)
            )
            .unwrap();

            let is_verified = SchnorrTweedleDeeGadget::enforce_signature_verdict(
                cs.ns(|| "new sig result"),
                &pk_g,
                &sig_g,
                new_message_g.clone(),
            )
            .unwrap();

            if !cs.is_satisfied() {
                println!("**********Unsatisfied constraints***********");
                println!("{:?}", cs.which_is_unsatisfied());
            }

            assert!(!is_verified.get_value().unwrap());
            assert!(cs.is_satisfied());

            SchnorrTweedleDeeGadget::enforce_signature_verification(
                cs.ns(|| "verify new sig"),
                &pk_g,
                &sig_g,
                new_message_g,
            )
            .unwrap();

            assert!(!cs.is_satisfied());
        }
    }
}
