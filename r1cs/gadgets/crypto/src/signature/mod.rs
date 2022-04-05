use algebra::PrimeField;
use primitives::signature::FieldBasedSignatureScheme;
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use r1cs_std::prelude::*;
use r1cs_std::to_field_gadget_vec::ToConstraintFieldGadget;

pub mod schnorr;

pub trait FieldBasedSigGadget<S: FieldBasedSignatureScheme, ConstraintF: PrimeField> {
    type DataGadget: FieldGadget<ConstraintF, ConstraintF>;
    type SignatureGadget: AllocGadget<S::Signature, ConstraintF>
        + ConstantGadget<S::Signature, ConstraintF>
        + EqGadget<ConstraintF>
        + ToConstraintFieldGadget<ConstraintF, FieldGadget = Self::DataGadget>;

    type PublicKeyGadget: AllocGadget<S::PublicKey, ConstraintF>
        + ConstantGadget<S::PublicKey, ConstraintF>
        + EqGadget<ConstraintF>
        + ToConstraintFieldGadget<ConstraintF, FieldGadget = Self::DataGadget>;

    /// Enforce `signature` verification with `public_key` on `message`, returning a Boolean
    /// enforced to be `true` if signature verification is successful, and `false` otherwise.
    fn enforce_signature_verdict<CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        public_key: &Self::PublicKeyGadget,
        signature: &Self::SignatureGadget,
        message: Self::DataGadget,
    ) -> Result<Boolean, SynthesisError>;

    /// Enforce `signature` verification with `public_key` on `message` to be successful.
    fn enforce_signature_verification<CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        public_key: &Self::PublicKeyGadget,
        signature: &Self::SignatureGadget,
        message: Self::DataGadget,
    ) -> Result<(), SynthesisError> {
        Self::conditionally_enforce_signature_verification(
            cs,
            public_key,
            signature,
            message,
            &Boolean::Constant(true),
        )
    }

    /// Enforce or not enforce, according to `should_enforce` value, `signature` verification with
    /// `public_key` on `message` to be successful.
    fn conditionally_enforce_signature_verification<CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        public_key: &Self::PublicKeyGadget,
        signature: &Self::SignatureGadget,
        message: Self::DataGadget,
        should_enforce: &Boolean,
    ) -> Result<(), SynthesisError>;
}
