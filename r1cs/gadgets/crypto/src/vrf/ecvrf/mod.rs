use algebra::{Curve, PrimeField};
use r1cs_std::{
    alloc::AllocGadget, bits::ToBytesGadget, eq::EqGadget, fields::fp::FpGadget,
    groups::GroupGadget, to_field_gadget_vec::ToConstraintFieldGadget,
};

use primitives::{
    compute_truncation_size,
    crh::{FieldBasedHash, FixedLengthCRH},
    vrf::ecvrf::{FieldBasedEcVrf, FieldBasedEcVrfProof},
};

use crate::{
    crh::{FieldBasedHashGadget, FixedLengthCRHGadget},
    vrf::FieldBasedVrfGadget,
};
use primitives::vrf::ecvrf::FieldBasedEcVrfPk;
use r1cs_core::{ConstraintSystemAbstract, SynthesisError, ToConstraintField};
use r1cs_std::bits::boolean::Boolean;
use std::{borrow::Borrow, marker::PhantomData};

#[derive(Derivative)]
#[derivative(
    Debug(bound = "ConstraintF: PrimeField, G: Curve, GG: GroupGadget<G, ConstraintF>"),
    Clone(bound = "ConstraintF: PrimeField, G: Curve, GG: GroupGadget<G, ConstraintF>"),
    PartialEq(bound = "ConstraintF: PrimeField, G: Curve, GG: GroupGadget<G, ConstraintF>"),
    Eq(bound = "ConstraintF: PrimeField, G: Curve, GG: GroupGadget<G, ConstraintF>")
)]
pub struct FieldBasedEcVrfProofGadget<ConstraintF, G, GG>
where
    ConstraintF: PrimeField,
    G: Curve,
    GG: GroupGadget<G, ConstraintF>,
{
    pub gamma: GG,
    pub c: FpGadget<ConstraintF>,
    pub s: FpGadget<ConstraintF>,
    _field: PhantomData<ConstraintF>,
    _group: PhantomData<G>,
}

impl<ConstraintF, G, GG> FieldBasedEcVrfProofGadget<ConstraintF, G, GG>
where
    ConstraintF: PrimeField,
    G: Curve,
    GG: GroupGadget<G, ConstraintF>,
{
    fn alloc_internal<FN, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        f: FN,
        gamma_on_curve: bool,
        gamma_prime_order: bool,
    ) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<FieldBasedEcVrfProof<ConstraintF, G>>,
    {
        let (gamma, c, s) = match f() {
            Ok(proof) => {
                let proof = *proof.borrow();
                (Ok(proof.gamma), Ok(proof.c), Ok(proof.s))
            }
            _ => (
                Err(SynthesisError::AssignmentMissing),
                Err(SynthesisError::AssignmentMissing),
                Err(SynthesisError::AssignmentMissing),
            ),
        };

        let gamma = match (gamma_on_curve, gamma_prime_order) {
            (false, false) => GG::alloc_without_check(cs.ns(|| "alloc gamma unchecked"), || gamma)?,
            (true, false) => GG::alloc(cs.ns(|| "alloc gamma"), || gamma).and_then(|gamma_g| {
                gamma_g.is_zero(cs.ns(|| "is gamma zero"))?.enforce_equal(
                    cs.ns(|| "gamma must not be zero"),
                    &Boolean::constant(false),
                )?;
                Ok(gamma_g)
            })?,
            (true, true) => GG::alloc_checked(cs.ns(|| "alloc gamma checked"), || gamma).and_then(
                |gamma_g| {
                    gamma_g.is_zero(cs.ns(|| "is gamma zero"))?.enforce_equal(
                        cs.ns(|| "gamma must not be zero"),
                        &Boolean::constant(false),
                    )?;
                    Ok(gamma_g)
                },
            )?,
            _ => unreachable!(),
        };
        let c = FpGadget::<ConstraintF>::alloc(cs.ns(|| "alloc c"), || c)?;
        let s = FpGadget::<ConstraintF>::alloc(cs.ns(|| "alloc s"), || s)?;
        Ok(Self {
            gamma,
            c,
            s,
            _field: PhantomData,
            _group: PhantomData,
        })
    }
}

impl<ConstraintF, G, GG> AllocGadget<FieldBasedEcVrfProof<ConstraintF, G>, ConstraintF>
    for FieldBasedEcVrfProofGadget<ConstraintF, G, GG>
where
    ConstraintF: PrimeField,
    G: Curve,
    GG: GroupGadget<G, ConstraintF>,
{
    fn alloc_without_check<FN, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        f: FN,
    ) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<FieldBasedEcVrfProof<ConstraintF, G>>,
    {
        Self::alloc_internal(cs, f, false, false)
    }

    fn alloc<FN, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        f: FN,
    ) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<FieldBasedEcVrfProof<ConstraintF, G>>,
    {
        Self::alloc_internal(cs, f, true, false)
    }

    fn alloc_checked<FN, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        f: FN,
    ) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<FieldBasedEcVrfProof<ConstraintF, G>>,
    {
        Self::alloc_internal(cs, f, true, true)
    }

    fn alloc_input<FN, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        f: FN,
    ) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<FieldBasedEcVrfProof<ConstraintF, G>>,
    {
        let (gamma, c, s) = match f() {
            Ok(proof) => {
                let proof = *proof.borrow();
                (Ok(proof.gamma), Ok(proof.c), Ok(proof.s))
            }
            _ => (
                Err(SynthesisError::AssignmentMissing),
                Err(SynthesisError::AssignmentMissing),
                Err(SynthesisError::AssignmentMissing),
            ),
        };

        let gamma = GG::alloc_input(cs.ns(|| "alloc gamma"), || gamma)?;
        let c = FpGadget::<ConstraintF>::alloc_input(cs.ns(|| "alloc c"), || c)?;
        let s = FpGadget::<ConstraintF>::alloc_input(cs.ns(|| "alloc s"), || s)?;
        Ok(Self {
            gamma,
            c,
            s,
            _field: PhantomData,
            _group: PhantomData,
        })
    }
}

pub struct FieldBasedEcVrfPkGadget<
    ConstraintF: PrimeField,
    G: Curve,
    GG: GroupGadget<G, ConstraintF>,
> {
    pub pk: GG,
    _field: PhantomData<ConstraintF>,
    _group: PhantomData<G>,
}

impl<ConstraintF, G, GG> AllocGadget<FieldBasedEcVrfPk<G>, ConstraintF>
    for FieldBasedEcVrfPkGadget<ConstraintF, G, GG>
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
        T: Borrow<FieldBasedEcVrfPk<G>>,
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
        T: Borrow<FieldBasedEcVrfPk<G>>,
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
        T: Borrow<FieldBasedEcVrfPk<G>>,
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
        T: Borrow<FieldBasedEcVrfPk<G>>,
    {
        let pk = GG::alloc_input(cs.ns(|| "alloc pk"), || f().map(|pk| pk.borrow().0))?;
        Ok(Self {
            pk,
            _field: PhantomData,
            _group: PhantomData,
        })
    }
}

pub struct FieldBasedEcVrfProofVerificationGadget<
    ConstraintF: PrimeField,
    G: Curve,
    GG: GroupGadget<G, ConstraintF>,
    FH: FieldBasedHash<Data = ConstraintF>,
    FHG: FieldBasedHashGadget<FH, ConstraintF>,
    GH: FixedLengthCRH<Output = G>,
    GHG: FixedLengthCRHGadget<GH, ConstraintF, OutputGadget = GG>,
> {
    _field: PhantomData<ConstraintF>,
    _group: PhantomData<G>,
    _group_gadget: PhantomData<GG>,
    _field_hash: PhantomData<FH>,
    _field_hash_gadget: PhantomData<FHG>,
    _group_hash: PhantomData<GH>,
    _group_hash_gadget: PhantomData<GHG>,
}

// This implementation supports both complete and incomplete (safe) point addition.
// Assumes provided key material to be already checked.
//
// In case of incomplete point addition, with negligible probability, the
// proof creation might fail at first attempt and must be re-run (in order to sample
// fresh randomnesses).
// Furthermore, two exceptional cases (gamma, c, s) have to be treated outside the circuit:
// - if c * pk = s * G, i.e. when u is trivial (therefore leaking the sk), OR
// - if c * gamma = s * mh, i.e. when v is trivial (therefore also leaking the sk), THEN
// the circuit is not satisfiable.
impl<ConstraintF, G, GG, FH, FHG, GH, GHG>
    FieldBasedVrfGadget<FieldBasedEcVrf<ConstraintF, G, FH, GH>, ConstraintF>
    for FieldBasedEcVrfProofVerificationGadget<ConstraintF, G, GG, FH, FHG, GH, GHG>
where
    ConstraintF: PrimeField,
    G: Curve + ToConstraintField<ConstraintF>,
    GG: GroupGadget<G, ConstraintF, Value = G>
        + ToConstraintFieldGadget<ConstraintF, FieldGadget = FHG::DataGadget>,
    FH: FieldBasedHash<Data = ConstraintF>,
    FHG: FieldBasedHashGadget<FH, ConstraintF, DataGadget = FpGadget<ConstraintF>>,
    GH: FixedLengthCRH<Output = G>,
    GHG: FixedLengthCRHGadget<GH, ConstraintF, OutputGadget = GG>,
{
    type DataGadget = FpGadget<ConstraintF>;
    type ProofGadget = FieldBasedEcVrfProofGadget<ConstraintF, G, GG>;
    type PublicKeyGadget = FieldBasedEcVrfPkGadget<ConstraintF, G, GG>;
    type GHParametersGadget = GHG::ParametersGadget;

    fn enforce_proof_to_hash_verification<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        group_hash_params: &Self::GHParametersGadget,
        public_key: &Self::PublicKeyGadget,
        proof: &Self::ProofGadget,
        message: Self::DataGadget,
    ) -> Result<Self::DataGadget, SynthesisError> {
        //Check mh = hash_to_curve(message)
        let message_bytes = message.to_bytes_strict(cs.ns(|| "message_to_bytes_restricted"))?;

        let message_on_curve = GHG::check_evaluation_gadget(
            cs.ns(|| "check message_on_curve"),
            group_hash_params,
            message_bytes.as_slice(),
        )?;

        //Serialize c and s

        let c_bits = {
            //Serialize e taking into account the length restriction
            let to_skip = compute_truncation_size(
                ConstraintF::size_in_bits() as i32,
                G::ScalarField::size_in_bits() as i32,
            );

            let c_bits = proof
                .c
                .to_bits_with_length_restriction(cs.ns(|| "c_to_bits"), to_skip)?;

            debug_assert!(c_bits.len() == ConstraintF::size_in_bits() - to_skip);
            c_bits
        };

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

            let s_bits = proof
                .s
                .to_bits_with_length_restriction(cs.ns(|| "s_to_bits"), to_skip as usize)?;

            debug_assert!(s_bits.len() == G::ScalarField::size_in_bits() + to_skip_init - to_skip);
            s_bits
        };
        s_bits.reverse();

        //Hardcode g
        let g = GG::from_value(
            cs.ns(|| "hardcode generator"),
            &G::prime_subgroup_generator(),
        );

        //Check u = g^s - pk^c
        let u = {
            let c_times_pk = public_key
                .pk
                .mul_bits(cs.ns(|| "pk * c"), c_bits.as_slice().iter().rev())?;
            GG::mul_bits_fixed_base(&g.get_constant(), cs.ns(|| "s * G"), s_bits.as_slice())?
                // If add is incomplete, and s * G - c * pk = 0, the circuit of the add won't be satisfiable
                .sub(cs.ns(|| "(s * G) - (c * pk)"), &c_times_pk)?
        };

        //Check v = mh^s - gamma^c
        let v = {
            let c_times_gamma = proof
                .gamma
                .mul_bits(cs.ns(|| "c * gamma"), c_bits.as_slice().iter().rev())?;
            message_on_curve
                .mul_bits(cs.ns(|| "s * mh"), s_bits.as_slice().iter())?
                // If add is incomplete, and s * mh - c * gamma = 0, the circuit of the add won't be satisfiable
                .sub(cs.ns(|| "(s * mh) - (c * gamma"), &c_times_gamma)?
        };

        // Check c' = H(m||pk.x||u.x||v.x)
        // Best constraints-efficiency is achieved when m is one field element
        // (or an odd number of field elements).
        let mut hash_input = Vec::new();
        hash_input.push(message.clone());
        hash_input.push(
            public_key
                .pk
                .to_field_gadget_elements(cs.ns(|| "pk to fes"))
                .unwrap()[0]
                .clone(),
        );
        hash_input.push(u.to_field_gadget_elements(cs.ns(|| "u to fes")).unwrap()[0].clone());
        hash_input.push(v.to_field_gadget_elements(cs.ns(|| "v to fes")).unwrap()[0].clone());

        let c_prime =
            FHG::enforce_hash_constant_length(cs.ns(|| "check c_prime"), hash_input.as_slice())?;

        //Enforce c = c'
        proof.c.enforce_equal(cs.ns(|| "check c == c'"), &c_prime)?;

        //Check and return VRF output
        hash_input = Vec::new();
        hash_input.push(message);
        hash_input.extend_from_slice(
            proof
                .gamma
                .to_field_gadget_elements(cs.ns(|| "gamma to fes"))
                .unwrap()
                .as_slice(),
        );

        let vrf_output =
            FHG::enforce_hash_constant_length(cs.ns(|| "check vrf_output"), hash_input.as_slice())?;

        Ok(vrf_output)
    }
}

#[cfg(test)]
mod test {
    use crate::{
        crh::{
            bowe_hopwood::BoweHopwoodPedersenCRHGadget, TweedleFqPoseidonHashGadget,
            TweedleFrPoseidonHashGadget,
        },
        vrf::{ecvrf::FieldBasedEcVrfProofVerificationGadget, FieldBasedVrfGadget},
    };
    use algebra::curves::{tweedle::dee::DeeJacobian, tweedle::dum::DumJacobian};
    use algebra::fields::tweedle::{Fq, Fr};
    use primitives::{
        crh::{
            bowe_hopwood::{BoweHopwoodPedersenCRH, BoweHopwoodPedersenParameters},
            pedersen::PedersenWindow,
            FixedLengthCRH, TweedleFqPoseidonHash, TweedleFrPoseidonHash,
        },
        vrf::{
            ecvrf::{FieldBasedEcVrf, FieldBasedEcVrfProof},
            FieldBasedVrf,
        },
    };

    use primitives::vrf::ecvrf::FieldBasedEcVrfPk;
    use r1cs_core::{
        ConstraintSystem, ConstraintSystemAbstract, ConstraintSystemDebugger, SynthesisMode,
    };
    use r1cs_std::alloc::AllocGadget;
    use r1cs_std::instantiated::tweedle::{TweedleDeeGadget, TweedleDumGadget};
    use rand::{thread_rng, Rng};

    #[derive(Clone)]
    struct TestWindow {}
    impl PedersenWindow for TestWindow {
        const WINDOW_SIZE: usize = 64;
        const NUM_WINDOWS: usize = 2;
    }

    type BHTweedleDee = BoweHopwoodPedersenCRH<DeeJacobian, TestWindow>;
    type BHTweedleDum = BoweHopwoodPedersenCRH<DumJacobian, TestWindow>;

    type BHTweedleDeeGadget = BoweHopwoodPedersenCRHGadget<DumJacobian, Fr, TweedleDumGadget>;
    type BHTweedleDumGadget = BoweHopwoodPedersenCRHGadget<DeeJacobian, Fq, TweedleDeeGadget>;

    type BHTweedleDeeParameters = BoweHopwoodPedersenParameters<DumJacobian>;
    type BHTweedleDumParameters = BoweHopwoodPedersenParameters<DeeJacobian>;

    type EcVrfTweedleDee = FieldBasedEcVrf<Fr, DumJacobian, TweedleFrPoseidonHash, BHTweedleDum>;
    type EcVrfTweedleDum = FieldBasedEcVrf<Fq, DeeJacobian, TweedleFqPoseidonHash, BHTweedleDee>;

    type EcVrfTweedleDeePk = FieldBasedEcVrfPk<DumJacobian>;
    type EcVrfTweedleDumPk = FieldBasedEcVrfPk<DeeJacobian>;

    type EcVrfTweedleDeeProof = FieldBasedEcVrfProof<Fr, DumJacobian>;
    type EcVrfTweedleDumProof = FieldBasedEcVrfProof<Fq, DeeJacobian>;

    type EcVrfTweedleDeeGadget = FieldBasedEcVrfProofVerificationGadget<
        Fr,
        DumJacobian,
        TweedleDumGadget,
        TweedleFrPoseidonHash,
        TweedleFrPoseidonHashGadget,
        BHTweedleDum,
        BHTweedleDeeGadget,
    >;

    type EcVrfTweedleDumGadget = FieldBasedEcVrfProofVerificationGadget<
        Fq,
        DeeJacobian,
        TweedleDeeGadget,
        TweedleFqPoseidonHash,
        TweedleFqPoseidonHashGadget,
        BHTweedleDee,
        BHTweedleDumGadget,
    >;

    fn prove<S: FieldBasedVrf, R: Rng>(
        rng: &mut R,
        pp: &S::GHParams,
        message: S::Data,
    ) -> (S::Proof, S::PublicKey) {
        let (pk, sk) = S::keygen(rng);
        assert!(S::keyverify(&pk));
        let proof = S::prove(rng, pp, &pk, &sk, message).unwrap();
        (proof, pk)
    }

    fn tweedle_dee_ecvrf_gadget_generate_constraints(
        message: Fr,
        pk: &EcVrfTweedleDeePk,
        proof: EcVrfTweedleDeeProof,
        pp: &BHTweedleDeeParameters,
    ) -> bool {
        let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

        //Alloc proof, pk and message
        let proof_g =
            <EcVrfTweedleDeeGadget as FieldBasedVrfGadget<EcVrfTweedleDee, Fr>>::ProofGadget::alloc(
                cs.ns(|| "alloc proof"),
                || Ok(proof),
            )
            .unwrap();

        let pk_g =
            <EcVrfTweedleDeeGadget as FieldBasedVrfGadget<EcVrfTweedleDee, Fr>>::PublicKeyGadget::alloc(
                cs.ns(|| "alloc pk"),
                || Ok(pk),
            )
            .unwrap();

        let pp_g =
            <EcVrfTweedleDeeGadget as FieldBasedVrfGadget<EcVrfTweedleDee, Fr>>::GHParametersGadget::alloc(
                cs.ns(|| "alloc gh params"),
                || Ok(pp),
            )
            .unwrap();

        let message_g =
            <EcVrfTweedleDeeGadget as FieldBasedVrfGadget<EcVrfTweedleDee, Fr>>::DataGadget::alloc(
                cs.ns(|| "alloc message"),
                || Ok(message),
            )
            .unwrap();

        //Verify proof
        EcVrfTweedleDeeGadget::enforce_proof_to_hash_verification(
            cs.ns(|| "verify proof1"),
            &pp_g,
            &pk_g,
            &proof_g,
            message_g,
        )
        .unwrap();

        if !cs.is_satisfied() {
            println!("**********Unsatisfied constraints***********");
            println!("{:?}", cs.which_is_unsatisfied());
        }

        cs.is_satisfied()
    }

    #[test]
    fn tweedle_dee_ecvrf_gadget_test() {
        let rng = &mut thread_rng();
        let message: Fr = rng.gen();
        let pp = <BHTweedleDum as FixedLengthCRH>::setup(rng).unwrap();
        let (proof, pk) = prove::<EcVrfTweedleDee, _>(rng, &pp, message);

        //Positive case
        assert!(tweedle_dee_ecvrf_gadget_generate_constraints(
            message, &pk, proof, &pp
        ));

        //Change message
        let wrong_message: Fr = rng.gen();
        assert!(!tweedle_dee_ecvrf_gadget_generate_constraints(
            wrong_message,
            &pk,
            proof,
            &pp
        ));

        //Change pk
        let wrong_pk: EcVrfTweedleDeePk = rng.gen();
        assert!(!tweedle_dee_ecvrf_gadget_generate_constraints(
            message, &wrong_pk, proof, &pp
        ));

        //Change proof
        let (wrong_proof, _) = prove::<EcVrfTweedleDee, _>(rng, &pp, wrong_message);
        assert!(!tweedle_dee_ecvrf_gadget_generate_constraints(
            message,
            &pk,
            wrong_proof,
            &pp
        ));
    }

    fn tweedle_dum_ecvrf_gadget_generate_constraints(
        message: Fq,
        pk: &EcVrfTweedleDumPk,
        proof: EcVrfTweedleDumProof,
        pp: &BHTweedleDumParameters,
    ) -> bool {
        let mut cs = ConstraintSystem::<Fq>::new(SynthesisMode::Debug);

        //Alloc proof, pk and message
        let proof_g =
            <EcVrfTweedleDumGadget as FieldBasedVrfGadget<EcVrfTweedleDum, Fq>>::ProofGadget::alloc(
                cs.ns(|| "alloc proof"),
                || Ok(proof),
            )
            .unwrap();
        let pk_g =
            <EcVrfTweedleDumGadget as FieldBasedVrfGadget<EcVrfTweedleDum, Fq>>::PublicKeyGadget::alloc(
                cs.ns(|| "alloc pk"),
                || Ok(pk),
            )
            .unwrap();
        let pp_g =
            <EcVrfTweedleDumGadget as FieldBasedVrfGadget<EcVrfTweedleDum, Fq>>::GHParametersGadget::alloc(
                cs.ns(|| "alloc gh params"),
                || Ok(pp),
            )
            .unwrap();
        let message_g =
            <EcVrfTweedleDumGadget as FieldBasedVrfGadget<EcVrfTweedleDum, Fq>>::DataGadget::alloc(
                cs.ns(|| "alloc message"),
                || Ok(message),
            )
            .unwrap();

        //Verify proof
        EcVrfTweedleDumGadget::enforce_proof_to_hash_verification(
            cs.ns(|| "verify proof1"),
            &pp_g,
            &pk_g,
            &proof_g,
            message_g,
        )
        .unwrap();

        if !cs.is_satisfied() {
            println!("**********Unsatisfied constraints***********");
            println!("{:?}", cs.which_is_unsatisfied());
        }

        cs.is_satisfied()
    }

    #[test]
    fn tweedle_dum_ecvrf_gadget_test() {
        let rng = &mut thread_rng();
        let message: Fq = rng.gen();
        let pp = <BHTweedleDee as FixedLengthCRH>::setup(rng).unwrap();
        let (proof, pk) = prove::<EcVrfTweedleDum, _>(rng, &pp, message);

        //Positive case
        assert!(tweedle_dum_ecvrf_gadget_generate_constraints(
            message, &pk, proof, &pp
        ));

        //Change message
        let wrong_message: Fq = rng.gen();
        assert!(!tweedle_dum_ecvrf_gadget_generate_constraints(
            wrong_message,
            &pk,
            proof,
            &pp
        ));

        //Change pk
        let wrong_pk: EcVrfTweedleDumPk = rng.gen();
        assert!(!tweedle_dum_ecvrf_gadget_generate_constraints(
            message, &wrong_pk, proof, &pp
        ));

        //Change proof
        let (wrong_proof, _) = prove::<EcVrfTweedleDum, _>(rng, &pp, wrong_message);
        assert!(!tweedle_dum_ecvrf_gadget_generate_constraints(
            message,
            &pk,
            wrong_proof,
            &pp
        ));
    }

    #[test]
    fn random_ecvrf_gadget_test() {
        //Generate VRF proof for a random field element f and get the proof and the public key
        let rng = &mut thread_rng();
        let pp = <BHTweedleDum as FixedLengthCRH>::setup(rng).unwrap();

        let samples = 10;
        for _ in 0..samples {
            let message: Fr = rng.gen();
            let (sig, pk) = prove::<EcVrfTweedleDee, _>(rng, &pp, message);
            let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

            //Alloc proof, pk, hash params and message
            let proof_g =
                <EcVrfTweedleDeeGadget as FieldBasedVrfGadget<EcVrfTweedleDee, Fr>>::ProofGadget::alloc(
                    cs.ns(|| "alloc proof"),
                    || Ok(sig),
                )
                .unwrap();

            let pk_g = <EcVrfTweedleDeeGadget as FieldBasedVrfGadget<EcVrfTweedleDee, Fr>>::PublicKeyGadget::alloc(
                cs.ns(|| "alloc pk"),
                || Ok(pk)
            ).unwrap();

            let pp_g = <EcVrfTweedleDeeGadget as FieldBasedVrfGadget<EcVrfTweedleDee, Fr>>::GHParametersGadget::alloc(
                cs.ns(|| "alloc gh params"),
                || Ok(&pp)
            ).unwrap();

            let message_g =
                <EcVrfTweedleDeeGadget as FieldBasedVrfGadget<EcVrfTweedleDee, Fr>>::DataGadget::alloc(
                    cs.ns(|| "alloc message"),
                    || Ok(message),
                )
                .unwrap();

            //Verify proof
            EcVrfTweedleDeeGadget::enforce_proof_to_hash_verification(
                cs.ns(|| "verify proof"),
                &pp_g,
                &pk_g,
                &proof_g,
                message_g,
            )
            .unwrap();

            if !cs.is_satisfied() {
                println!("**********Unsatisfied constraints***********");
                println!("{:?}", cs.which_is_unsatisfied());
            }

            assert!(cs.is_satisfied());

            //Negative case: wrong message (or wrong proof for another message)
            let new_message: Fr = rng.gen();

            let new_message_g = <EcVrfTweedleDeeGadget as FieldBasedVrfGadget<
                EcVrfTweedleDee,
                Fr,
            >>::DataGadget::alloc(
                cs.ns(|| "alloc new_message"), || Ok(new_message)
            )
            .unwrap();

            EcVrfTweedleDeeGadget::enforce_proof_to_hash_verification(
                cs.ns(|| "verify new proof"),
                &pp_g,
                &pk_g,
                &proof_g,
                new_message_g,
            )
            .unwrap();

            assert!(!cs.is_satisfied());
        }
    }
}
