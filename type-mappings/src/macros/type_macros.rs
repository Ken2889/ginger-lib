#[macro_export]
macro_rules! generate_algebraic_types {
    ($curve: ident, $curve_parameters: ty) => {

        // Basic algebraic types
        pub type FieldElement = <$curve_parameters as ModelParameters>::BaseField;

        pub type ScalarFieldElement = <$curve_parameters as ModelParameters>::ScalarField;

        pub type Group = $curve;

        pub type BigInteger = <<FieldElement as Field>::BasePrimeField as PrimeField>::BigInt;

        // Basic constants
        pub const FIELD_CAPACITY: usize = <FieldElement as PrimeField>::Params::CAPACITY as usize;
        pub const FIELD_SIZE: usize = ((<FieldElement as PrimeField>::Params::MODULUS_BITS
            + <FieldElement as PrimeField>::Params::REPR_SHAVE_BITS)
            as usize)
            / 8;
        pub const SCALAR_FIELD_SIZE: usize =
            ((<ScalarFieldElement as PrimeField>::Params::MODULUS_BITS
                + <ScalarFieldElement as PrimeField>::Params::REPR_SHAVE_BITS)
                / 8) as usize;
        pub const GROUP_SIZE: usize = 2 * FIELD_SIZE + 1;
        // ceil ((MODULUS_BITS + 2 (1 bit for infinity and 1 for odd/even y))/8)
        pub const GROUP_COMPRESSED_SIZE: usize = FIELD_SIZE
            + if <FieldElement as PrimeField>::Params::REPR_SHAVE_BITS >= 2 {
                0
            } else {
                1
            };
    };
}

#[macro_export]
macro_rules! generate_poseidon_hash_types {
    ($field_hash: ident, $batch_field_hash: ident) => {
        pub type FieldHash = $field_hash;
        pub type BatchFieldHash = $batch_field_hash;
    };
}

/// Pre-conditions: algebraic and poseidon hash types already generated
#[macro_export]
macro_rules! _generate_merkle_tree_types {
    ($tree_params: ident, $tree_arity: expr) => {
        #[derive(Clone, Debug)]
        pub struct GingerMHTParams;

        impl FieldBasedMerkleTreeParameters for GingerMHTParams {
            type Data = FieldElement;
            type H = FieldHash;
            const MERKLE_ARITY: usize = $tree_arity;
            const ZERO_NODE_CST: Option<
                FieldBasedMerkleTreePrecomputedZeroConstants<'static, Self::H>,
            > = Some($tree_params);
        }

        impl BatchFieldBasedMerkleTreeParameters for GingerMHTParams {
            type BH = BatchFieldHash;
        }

        pub type GingerMHT = FieldBasedOptimizedMHT<GingerMHTParams>;
        pub type GingerMHTPath = FieldBasedBinaryMHTPath<GingerMHTParams>;
        pub const GINGER_MHT_POSEIDON_PARAMETERS: FieldBasedMerkleTreePrecomputedZeroConstants<'static, FieldHash> = $tree_params;
    };
}


#[macro_export]
macro_rules! generate_merkle_tree_types {
    // No pre-conditions:
    ($curve: ident, $curve_parameters: ty, $field_hash: ident, $batch_field_hash: ident, $tree_params: ident, $tree_arity: expr) => {
        generate_algebraic_types($curve, $curve_parameters);
        generate_poseidon_hash_types!($field_hash, $batch_field_hash);
        _generate_merkle_tree_types!($tree_params, $tree_arity);
    };

    // Pre-conditions: algebraic types already generated
    ($field_hash: ident, $batch_field_hash: ident, $tree_params: ident, $tree_arity: expr) => {
        generate_poseidon_hash_types!($field_hash, $batch_field_hash);
        _generate_merkle_tree_types!($tree_params, $tree_arity);
    };

    // Pre-conditions: algebraic and poseidon hash types already generated
    ($tree_params: ident, $tree_arity: expr) => {
        _generate_merkle_tree_types!($tree_params, $tree_arity);
    };
}

/// Pre-conditions: algebraic and poseidon hash types already generated
#[macro_export]
macro_rules! _generate_schnorr_signature_types {
    ($projective_curve: ident, $affine_curve: ident) => {
        pub const SCHNORR_PK_SIZE: usize = GROUP_COMPRESSED_SIZE;
        pub const SCHNORR_SK_SIZE: usize = SCALAR_FIELD_SIZE;
        pub const SCHNORR_SIG_SIZE: usize = 2 * FIELD_SIZE;

        pub type SchnorrSigScheme =
            FieldBasedSchnorrSignatureScheme<FieldElement, $projective_curve, FieldHash>;
        pub type SchnorrSig = FieldBasedSchnorrSignature<FieldElement, $projective_curve>;
        pub type SchnorrPk = $affine_curve;
        pub type SchnorrSk = ScalarFieldElement;
    };
}

#[macro_export]
macro_rules! generate_schnorr_signature_types {
    // No pre-conditions:
    ($affine_curve: ident, $projective_curve: ident, $curve_parameters: ty, $field_hash: ident, $batch_field_hash: ident) => {
        generate_algebraic_types($affine_curve, $curve_parameters);
        generate_poseidon_hash_types!($field_hash, $batch_field_hash);
        _generate_schnorr_signature_types!($projective_curve, $affine_curve);
    };

    // Pre-conditions: algebraic types already generated
    ($field_hash: ident, $batch_field_hash: ident, $affine_curve: ident, $projective_curve: ident) => {
        generate_poseidon_hash_types!($field_hash, $batch_field_hash);
        _generate_schnorr_signature_types!($projective_curve, $affine_curve);
    };

    // Pre-conditions: algebraic and poseidon hash types already generated
    ($projective_curve: ident, $affine_curve: ident) => {
        _generate_schnorr_signature_types!($projective_curve, $affine_curve);
    };
}

/// Pre-conditions: algebraic and poseidon hash types already generated
#[macro_export]
macro_rules! _generate_vrf_types {
    ($projective_curve: ident, $affine_curve: ident) => {
        // Group hash personalizations
        /// BLAKE2s Personalization for Group hash generators used for VRF.
        const VRF_GROUP_HASH_GENERATORS_PERSONALIZATION: &'static [u8; 8] = b"ZenVrfPH";

        #[derive(Clone)]
        pub struct VRFWindow {}
        impl PedersenWindow for VRFWindow {
            const WINDOW_SIZE: usize = 128;
            const NUM_WINDOWS: usize = 2;
        }

        lazy_static! {
            pub static ref VRF_GH_PARAMS: BoweHopwoodPedersenParameters<$projective_curve> =
                get_vrf_params();
        }

        fn compute_group_hash_table(
            generators: Vec<$projective_curve>,
        ) -> Vec<Vec<$projective_curve>> {
            let mut gen_table = Vec::new();
            for i in 0..VRFWindow::NUM_WINDOWS {
                let mut generators_for_segment = Vec::new();
                let mut base = generators[i];
                for _ in 0..VRFWindow::WINDOW_SIZE {
                    generators_for_segment.push(base);
                    for _ in 0..4 {
                        base.double_in_place();
                    }
                }
                gen_table.push(generators_for_segment);
            }
            gen_table
        }

        fn get_vrf_params() -> BoweHopwoodPedersenParameters<$projective_curve> {
            let personalization = VRF_GROUP_HASH_GENERATORS_PERSONALIZATION;

            //Gen1
            let tag = b"Magnesium Mg 12";
            let htc_g1_out = hash_to_curve::<FieldElement, $affine_curve>(tag, personalization)
                .unwrap()
                .into_projective();

            //Gen2
            let tag = b"Gold Au 79";
            let htc_g2_out = hash_to_curve::<FieldElement, $affine_curve>(tag, personalization)
                .unwrap()
                .into_projective();

            //Check GH generators
            let gh_generators = compute_group_hash_table([htc_g1_out, htc_g2_out].to_vec());

            BoweHopwoodPedersenParameters::<$projective_curve> {
                generators: gh_generators,
            }
        }

        pub const VRF_PK_SIZE: usize = GROUP_COMPRESSED_SIZE;
        pub const VRF_SK_SIZE: usize = SCALAR_FIELD_SIZE;
        pub const VRF_PROOF_SIZE: usize = GROUP_COMPRESSED_SIZE + 2 * FIELD_SIZE;

        pub type GroupHash = BoweHopwoodPedersenCRH<$projective_curve, VRFWindow>;

        pub type VRFScheme = FieldBasedEcVrf<FieldElement, $projective_curve, FieldHash, GroupHash>;
        pub type VRFProof = FieldBasedEcVrfProof<FieldElement, $projective_curve>;
        pub type VRFPk = $affine_curve;
        pub type VRFSk = ScalarFieldElement;
    };
}

#[macro_export]
macro_rules! generate_vrf_types {
    // No pre-conditions:
    ($affine_curve: ident, $projective_curve: ident, $curve_parameters: ty, $field_hash: ident, $batch_field_hash: ident) => {
        generate_algebraic_types($affine_curve, $curve_parameters);
        generate_poseidon_hash_types!($field_hash, $batch_field_hash);
        _generate_vrf_types!($projective_curve, $affine_curve);
    };

    // Pre-conditions: algebraic types already generated
    ($field_hash: ident, $batch_field_hash: ident, $affine_curve: ident, $projective_curve: ident) => {
        generate_poseidon_hash_types!($field_hash, $batch_field_hash);
        _generate_vrf_types!($projective_curve, $affine_curve);
    };

    // Pre-conditions: algebraic and poseidon hash types already generated
    ($projective_curve: ident, $affine_curve: ident) => {
        _generate_vrf_types!($projective_curve, $affine_curve);
    };
}

/// Pre-conditions: schnorr signature types already generated
#[macro_export]
macro_rules! generate_phantom_schnorr_bindings {
    ($projective_curve: ident, $affine_curve: ident) => {
        lazy_static! {
            pub static ref PHANTOM_SIG: SchnorrSig =
                SchnorrSig::new(FieldElement::one(), FieldElement::one());
        }

        const NULL_PK_PERSONALIZATION: &'static [u8; 8] = b"ZenullPK";

        lazy_static! {
            pub static ref PHANTOM_PK: $projective_curve = {
                let tag = b"Strontium Sr 90";
                let personalization = NULL_PK_PERSONALIZATION;
                hash_to_curve::<FieldElement, $affine_curve>(tag, personalization)
                    .unwrap()
                    .into_projective()
            };
        }
    };
}

#[macro_export]
macro_rules! generate_all_algebraic_crypto_types {
    ($affine_curve: ident, $projective_curve: ident, $curve_parameters: ty, $field_hash: ident, $batch_field_hash: ident, $tree_params: ident, $tree_arity: expr) => {
        generate_algebraic_types!($affine_curve, $curve_parameters);
        generate_poseidon_hash_types!($field_hash, $batch_field_hash);
        generate_merkle_tree_types!($tree_params, $tree_arity);
        generate_schnorr_signature_types!($projective_curve, $affine_curve);
        generate_vrf_types!($projective_curve, $affine_curve);
    };
}

/// Pre-conditions: Field types already generated
#[cfg(feature = "groth16")]
#[macro_export]
macro_rules! generate_groth16_types {
    ($pairing_curve: ident) => {
        use proof_systems::groth16::{Parameters, Proof, VerifyingKey, PreparedVerifyingKey};

        pub type PairingCurve = $pairing_curve;
        pub type Groth16Parameters = Parameters<PairingCurve>;
        pub type Groth16Proof = Proof<PairingCurve>;
        pub type Groth16VerifyingKey = VerifyingKey<PairingCurve>;
        pub type Groth16PreparedVerifyingKey = PreparedVerifyingKey<PairingCurve>;

        pub const GROUP_2_SIZE: usize = 4 * FIELD_SIZE + 1;

        pub const ZK_PROOF_SIZE: usize = 2 * GROUP_SIZE + GROUP_2_SIZE;
    };
}

/// Pre-conditions: Field types already generated
#[cfg(feature = "darlin")]
#[macro_export]
macro_rules! _generate_darlin_types {
    ($dual_group_affine: ident, $dual_group_projective: ident) => {
        use blake2::Blake2s;
        use poly_commit::ipa_pc::*;
        use proof_systems::darlin::pcd::simple_marlin::MarlinProof;
        use proof_systems::darlin::{data_structures::*, *};

        // Basic algebraic types
        pub type DualGroup = $dual_group_affine;
        pub type DualGroupProjective = $dual_group_projective;

        // Polynomial Commitment instantiations
        pub type Digest = Blake2s;
        pub type IPAPC = InnerProductArgPC<$dual_group_affine, Digest>;
        pub type CommitterKeyDualGroup = CommitterKey<$dual_group_affine>;
        pub type CommitterKeyGroup = CommitterKey<Group>;

        // Coboundary Marlin instantiations
        pub type CoboundaryMarlin = marlin::Marlin<FieldElement, IPAPC, Digest>;
        pub type CoboundaryMarlinProof = MarlinProof<$dual_group_affine, Digest>;
        pub type CoboundaryMarlinProverKey = marlin::ProverKey<FieldElement, IPAPC>;
        pub type CoboundaryMarlinVerifierKey = marlin::VerifierKey<FieldElement, IPAPC>;

        // (Final) Darlin instantiations
        pub type Darlin<'a> = FinalDarlin<'a, $dual_group_affine, Group, Digest>;
        pub type DarlinProof = FinalDarlinProof<$dual_group_affine, Group, Digest>;
        pub type DarlinProverKey = FinalDarlinProverKey<FieldElement, IPAPC>;
        pub type DarlinVerifierKey = FinalDarlinVerifierKey<FieldElement, IPAPC>;
    };
}

#[cfg(feature = "darlin")]
#[macro_export]
macro_rules! generate_darlin_types {

    // No pre-conditions
    ($group: ident, $group_parameters: ty, $dual_group_affine: ident, $dual_group_projective: ident) => {
        generate_algebraic_types!($group, $group_parameters);
        _generate_darlin_types!($dual_group_affine, $dual_group_projective);
    };

    // Pre-conditions: Field types already generated
    ($dual_group_affine: ident, $dual_group_projective: ident) => {
        _generate_darlin_types!($dual_group_affine, $dual_group_projective);
    }
}