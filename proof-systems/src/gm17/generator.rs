use algebra::fft::domain::{get_best_evaluation_domain, sample_element_outside_domain};
use algebra::msm::FixedBaseMSM;
use algebra::{AffineCurve, Field, PairingEngine, PrimeField, ProjectiveCurve, UniformRand};

use r1cs_core::{ConstraintSynthesizer, ConstraintSystem, SynthesisError, SynthesisMode};
use rand::Rng;
use rayon::prelude::*;

use crate::gm17::{r1cs_to_sap::R1CStoSAP, Parameters, VerifyingKey};

/// Generates a random common reference string for
/// a circuit.
pub fn generate_random_parameters<E, C, R>(
    circuit: C,
    rng: &mut R,
) -> Result<Parameters<E>, SynthesisError>
where
    E: PairingEngine,
    C: ConstraintSynthesizer<E::Fr>,
    R: Rng,
{
    let alpha = E::Fr::rand(rng);
    let beta = E::Fr::rand(rng);
    let gamma = E::Fr::one();
    let g = E::G1Projective::rand(rng);
    let h = E::G2Projective::rand(rng);

    generate_parameters::<E, C, R>(circuit, alpha, beta, gamma, g, h, rng)
}

/// Create parameters for a circuit, given some toxic waste.
pub fn generate_parameters<E, C, R>(
    circuit: C,
    alpha: E::Fr,
    beta: E::Fr,
    gamma: E::Fr,
    g: E::G1Projective,
    h: E::G2Projective,
    rng: &mut R,
) -> Result<Parameters<E>, SynthesisError>
where
    E: PairingEngine,
    C: ConstraintSynthesizer<E::Fr>,
    R: Rng,
{
    let mut assembly = ConstraintSystem::<E::Fr>::new(SynthesisMode::Setup);

    // Synthesize the circuit.
    let synthesis_time = start_timer!(|| "Constraint synthesis");
    circuit.generate_constraints(&mut assembly)?;
    end_timer!(synthesis_time);

    ///////////////////////////////////////////////////////////////////////////
    let domain_time = start_timer!(|| "Constructing evaluation domain");

    let domain_size = 2 * assembly.num_constraints + 2 * assembly.num_inputs - 1;
    let domain = get_best_evaluation_domain::<E::Fr>(domain_size)
        .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

    //Sample element outside domain
    let t = sample_element_outside_domain(&domain, rng);
    end_timer!(domain_time);
    ///////////////////////////////////////////////////////////////////////////

    let reduction_time = start_timer!(|| "R1CS to SAP Instance Map with Evaluation");
    let (a, c, zt, sap_num_variables, m_raw) =
        R1CStoSAP::instance_map_with_evaluation::<E>(&assembly, &t)?;
    end_timer!(reduction_time);

    // Compute query densities
    let non_zero_a = (0..sap_num_variables)
        .into_par_iter()
        .map(|i| (!a[i].is_zero()) as usize)
        .sum();
    let scalar_bits = E::Fr::size_in_bits();

    // Compute G window table
    let g_window_time = start_timer!(|| "Compute G window table");
    let g_window = FixedBaseMSM::get_mul_window_size(
        // Verifier query
        assembly.num_inputs
        // A query
        + non_zero_a
        // C query 1
        + (sap_num_variables - (assembly.num_inputs - 1))
        // C query 2
        + sap_num_variables + 1
        // G gamma2 Z t
        + m_raw + 1,
    );
    let g_table = FixedBaseMSM::get_window_table::<E::G1Projective>(scalar_bits, g_window, g);
    end_timer!(g_window_time);

    // Generate the R1CS proving key
    let proving_key_time = start_timer!(|| "Generate the R1CS proving key");

    // Compute the A-query
    let a_time = start_timer!(|| "Calculate A");
    let mut a_query = FixedBaseMSM::multi_scalar_mul::<E::G1Projective>(
        scalar_bits,
        g_window,
        &g_table,
        &a.par_iter().map(|a| *a * &gamma).collect::<Vec<_>>(),
    )?;
    end_timer!(a_time);

    // Compute the G_gamma-query
    let g_gamma_time = start_timer!(|| "Calculate G gamma");
    let gamma_z = zt * &gamma;
    let alpha_beta = alpha + &beta;
    let ab_gamma_z = alpha_beta * &gamma * &zt;
    let g_gamma = g.into_affine().mul(gamma.into_repr());
    let g_gamma_z = g.into_affine().mul(gamma_z.into_repr());
    let h_gamma = h.into_affine().mul(gamma.into_repr());
    let h_gamma_z = h_gamma.into_affine().mul(zt.into_repr());
    let g_ab_gamma_z = g.into_affine().mul(ab_gamma_z.into_repr());
    let g_gamma2_z2 = g.into_affine().mul(gamma_z.square().into_repr());

    // Compute the vector G_gamma2_z_t := Z(t) * t^i * gamma^2 * G
    let gamma2_z_t = gamma_z * &gamma;
    let mut g_gamma2_z_t = FixedBaseMSM::multi_scalar_mul::<E::G1Projective>(
        scalar_bits,
        g_window,
        &g_table,
        &(0..m_raw + 1)
            .into_par_iter()
            .map(|i| gamma2_z_t * &(t.pow([i as u64])))
            .collect::<Vec<_>>(),
    )?;
    end_timer!(g_gamma_time);

    // Compute the C_1-query
    let c1_time = start_timer!(|| "Calculate C1");
    let result = FixedBaseMSM::multi_scalar_mul::<E::G1Projective>(
        scalar_bits,
        g_window,
        &g_table,
        &(0..sap_num_variables + 1)
            .into_par_iter()
            .map(|i| c[i] * &gamma + &(a[i] * &alpha_beta))
            .collect::<Vec<_>>(),
    )?;
    let (verifier_query, c_query_1) = result.split_at(assembly.num_inputs);
    end_timer!(c1_time);

    // Compute the C_2-query
    let c2_time = start_timer!(|| "Calculate C2");
    let double_gamma2_z = (zt * &gamma.square()).double();
    let mut c_query_2 = FixedBaseMSM::multi_scalar_mul::<E::G1Projective>(
        scalar_bits,
        g_window,
        &g_table,
        &(0..sap_num_variables + 1)
            .into_par_iter()
            .map(|i| a[i] * &double_gamma2_z)
            .collect::<Vec<_>>(),
    )?;
    drop(g_table);
    end_timer!(c2_time);

    // Compute H_gamma window table
    let h_gamma_time = start_timer!(|| "Compute H table");
    let h_gamma_window = FixedBaseMSM::get_mul_window_size(non_zero_a);
    let h_gamma_table =
        FixedBaseMSM::get_window_table::<E::G2Projective>(scalar_bits, h_gamma_window, h_gamma);
    end_timer!(h_gamma_time);

    // Compute the B-query
    let b_time = start_timer!(|| "Calculate B");
    let mut b_query = FixedBaseMSM::multi_scalar_mul::<E::G2Projective>(
        scalar_bits,
        h_gamma_window,
        &h_gamma_table,
        &a,
    )?;
    end_timer!(b_time);

    end_timer!(proving_key_time);

    // Generate R1CS verification key
    let verifying_key_time = start_timer!(|| "Generate the R1CS verification key");
    let g_alpha = g.into_affine().mul(alpha.into_repr());
    let h_beta = h.into_affine().mul(beta.into_repr());
    end_timer!(verifying_key_time);

    let vk = VerifyingKey::<E> {
        h_g2: h.into_affine(),
        g_alpha_g1: g_alpha.into_affine(),
        h_beta_g2: h_beta.into_affine(),
        g_gamma_g1: g_gamma.into_affine(),
        h_gamma_g2: h_gamma.into_affine(),
        query: verifier_query
            .into_par_iter()
            .map(|e| e.into_affine())
            .collect(),
    };

    let mut c_query_1 = c_query_1.to_vec();

    let batch_normalization_time = start_timer!(|| "Convert proving key elements to affine");
    E::G1Projective::batch_normalization(a_query.as_mut_slice());
    E::G2Projective::batch_normalization(b_query.as_mut_slice());
    E::G1Projective::batch_normalization(c_query_1.as_mut_slice());
    E::G1Projective::batch_normalization(c_query_2.as_mut_slice());
    E::G1Projective::batch_normalization(g_gamma2_z_t.as_mut_slice());
    end_timer!(batch_normalization_time);

    Ok(Parameters {
        vk,
        a_query: a_query.into_iter().map(Into::into).collect(),
        b_query: b_query.into_iter().map(Into::into).collect(),
        c_query_1: c_query_1.into_iter().map(Into::into).collect(),
        c_query_2: c_query_2.into_iter().map(Into::into).collect(),
        g_gamma_z: g_gamma_z.into_affine(),
        h_gamma_z: h_gamma_z.into_affine(),
        g_ab_gamma_z: g_ab_gamma_z.into_affine(),
        g_gamma2_z2: g_gamma2_z2.into_affine(),
        g_gamma2_z_t: g_gamma2_z_t.into_iter().map(Into::into).collect(),
    })
}
