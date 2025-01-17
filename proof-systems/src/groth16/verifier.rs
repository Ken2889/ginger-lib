use algebra::{AffineCurve, PairingEngine, PrimeField, ProjectiveCurve};

use super::{PreparedVerifyingKey, Proof, VerifyingKey};

use crate::groth16::SynthesisError;

use std::ops::{AddAssign, Neg};

pub fn prepare_verifying_key<E: PairingEngine>(vk: &VerifyingKey<E>) -> PreparedVerifyingKey<E> {
    PreparedVerifyingKey {
        alpha_g1_beta_g2: vk.alpha_g1_beta_g2,
        gamma_g2_neg_pc: vk.gamma_g2.neg().into(),
        delta_g2_neg_pc: vk.delta_g2.neg().into(),
        gamma_abc_g1: vk.gamma_abc_g1.clone(),
    }
}

pub fn verify_proof<E: PairingEngine>(
    pvk: &PreparedVerifyingKey<E>,
    proof: &Proof<E>,
    public_inputs: &[E::Fr],
) -> Result<bool, SynthesisError> {
    if (public_inputs.len() + 1) != pvk.gamma_abc_g1.len() {
        return Err(SynthesisError::MalformedVerifyingKey);
    }

    let mut g_ic = pvk.gamma_abc_g1[0].into_projective();
    for (i, b) in public_inputs.iter().zip(pvk.gamma_abc_g1.iter().skip(1)) {
        g_ic.add_assign(&b.mul(i.into_repr()));
    }

    // The original verification equation is:
    // A * B = alpha * beta + inputs * gamma + C * delta
    // ... however, we rearrange it so that it is:
    // A * B - inputs * gamma - C * delta = alpha * beta
    // or equivalently:
    // A * B + inputs * (-gamma) + C * (-delta) = alpha * beta
    // which allows us to do a single final exponentiation.

    let qap = E::miller_loop(
        [
            (proof.a.into(), proof.b.into()),
            (g_ic.into_affine().into(), pvk.gamma_g2_neg_pc.clone()),
            (proof.c.into(), pvk.delta_g2_neg_pc.clone()),
        ]
        .iter(),
    )?;

    let test = E::final_exponentiation(&qap)?;

    Ok(test == pvk.alpha_g1_beta_g2)
}
