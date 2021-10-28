use super::*;

#[macro_export]
macro_rules! generate_serialization_functions {
    () => {
        fn _deserialize_inner<R: Read, T: CanonicalDeserialize + SemanticallyValid>(
            reader: R,
            semantic_checks: Option<bool>,
            compressed: Option<bool>,
        ) -> Result<T, SerializationError> {
            let semantic_checks = semantic_checks.unwrap_or(false);
            let compressed = compressed.unwrap_or(false);

            let t = if compressed {
                T::deserialize_unchecked(reader)
            } else {
                T::deserialize_uncompressed_unchecked(reader)
            }?;

            if semantic_checks && !t.is_valid() {
                return Err(SerializationError::InvalidData);
            }

            Ok(t)
        }

        /// Deserialize from `buffer` a compressed or uncompressed element, depending on the value of
        /// `compressed` flag, and perform checks on it, depending on the value of `semantic_checks` flag.
        /// `compressed` can be optional, due to some types being uncompressable;
        /// `semantic_checks` can be optional, due to some types having no checks to be performed,
        /// or trivial checks already performed a priori during serialization.
        pub fn deserialize_from_buffer<T: CanonicalDeserialize + SemanticallyValid>(
            buffer: &[u8],
            semantic_checks: Option<bool>,
            compressed: Option<bool>,
        ) -> Result<T, SerializationError> {
            _deserialize_inner(buffer, semantic_checks, compressed)
        }

        /// Deserialize from `buffer` a compressed or uncompressed element, depending on the value of
        /// `compressed` flag, and perform checks on it, depending on the value of `semantic_checks` flag.
        /// `compressed` can be optional, due to some types being uncompressable;
        /// `semantic_checks` can be optional, due to some types having no checks to be performed,
        /// or trivial checks already performed a priori during serialization.
        /// If there are still bytes to read in `buffer` after deserializing T, this function returns an error.
        pub fn deserialize_from_buffer_strict<T: CanonicalDeserialize + SemanticallyValid>(
            buffer: &[u8],
            semantic_checks: Option<bool>,
            compressed: Option<bool>,
        ) -> Result<T, SerializationError> {
            // Wrap buffer in a cursor
            let buff_len = buffer.len() as u64;
            let mut buffer = Cursor::new(buffer);

            // Deserialize t
            let t = _deserialize_inner(&mut buffer, semantic_checks, compressed)?;

            let position = buffer.position();
            if position != buff_len {
                return Err(SerializationError::IoError(IoError::new(
                    ErrorKind::InvalidInput,
                    format!(
                        "Oversized data. Read {} but buff len is {}",
                        position, buff_len
                    ),
                )));
            }

            Ok(t)
        }

        /// Serialize to buffer, choosing whether to use compressed representation or not,
        /// depending on the value of `compressed` flag.
        /// `compressed` can be optional, due to some types being uncompressable.
        pub fn serialize_to_buffer<T: CanonicalSerialize>(
            to_write: &T,
            compressed: Option<bool>,
        ) -> Result<Vec<u8>, SerializationError> {
            let compressed = compressed.unwrap_or(false);

            let mut buffer;
            if compressed {
                buffer = Vec::with_capacity(to_write.serialized_size());
                CanonicalSerialize::serialize(to_write, &mut buffer)?;
            } else {
                buffer = Vec::with_capacity(to_write.uncompressed_size());
                CanonicalSerialize::serialize_uncompressed(to_write, &mut buffer)?;
            }
            Ok(buffer)
        }

        pub const DEFAULT_BUF_SIZE: usize = 1 << 20;

        /// Deserialize from the file at `file_path` a compressed or uncompressed element,
        /// depending on the value of `compressed` flag, and perform checks on it, depending
        /// on the value of `semantic_checks` flag.
        /// `compressed` can be optional, due to some types being uncompressable;
        /// `semantic_checks` can be optional, due to some types having no checks to be performed,
        /// or trivial checks already performed a priori during serialization.
        pub fn read_from_file<T: CanonicalDeserialize + SemanticallyValid>(
            file_path: &str,
            semantic_checks: Option<bool>,
            compressed: Option<bool>,
        ) -> Result<T, SerializationError> {
            let fs = File::open(file_path).map_err(SerializationError::IoError)?;
            let reader = BufReader::with_capacity(DEFAULT_BUF_SIZE, fs);

            _deserialize_inner(reader, semantic_checks, compressed)
        }

        /// Serialize to file, choosing whether to use compressed representation or not,
        /// depending on the value of `compressed` flag.
        /// `compressed` can be optional, due to some types being uncompressable.
        pub fn write_to_file<T: CanonicalSerialize>(
            to_write: &T,
            file_path: &str,
            compressed: Option<bool>,
        ) -> Result<(), SerializationError> {
            let compressed = compressed.unwrap_or(false);

            let fs = File::create(file_path).map_err(SerializationError::IoError)?;
            let mut writer = BufWriter::with_capacity(DEFAULT_BUF_SIZE, fs);

            if compressed {
                CanonicalSerialize::serialize(to_write, &mut writer)?;
            } else {
                CanonicalSerialize::serialize_uncompressed(to_write, &mut writer)?;
            }

            writer.flush().map_err(SerializationError::IoError)?;
            Ok(())
        }

        pub fn is_valid<T: SemanticallyValid>(to_check: &T) -> bool {
            T::is_valid(to_check)
        }

        pub(crate) fn into_i8(v: Vec<u8>) -> Vec<i8> {
            // first, make sure v's destructor doesn't free the data
            // it thinks it owns when it goes out of scope
            let mut v = std::mem::ManuallyDrop::new(v);
        
            // then, pick apart the existing Vec
            let p = v.as_mut_ptr();
            let len = v.len();
            let cap = v.capacity();
        
            // finally, adopt the data into a new Vec
            unsafe { Vec::from_raw_parts(p as *mut i8, len, cap) }
        }
    }
}

/// Pre-requisite: FieldElement types generated
#[macro_export]
macro_rules! _generate_field_element_functions {
    () => {
        pub fn read_field_element_from_u64(num: u64) -> FieldElement {
            FieldElement::from_repr(BigInteger::from(num))
        }

        //Will return error if buffer.len > FIELD_SIZE. If buffer.len < FIELD_SIZE, padding 0s will be added
        pub fn read_field_element_from_buffer_with_padding<F: PrimeField>(
            buffer: &[u8],
        ) -> Result<F, algebra::serialize::SerializationError> {
            let buff_len = buffer.len();

            //Pad to reach field element size
            let mut new_buffer = Vec::new();
            new_buffer.extend_from_slice(buffer);

            for _ in buff_len..FIELD_SIZE {
                new_buffer.push(0u8)
            } //Add padding zeros to reach field size

            algebra::serialize::CanonicalDeserialize::deserialize(new_buffer.as_slice())
        }

        //*******************************Generic functions**********************************************

        pub fn get_secure_random_field_element() -> FieldElement {
            FieldElement::rand(&mut rand::rngs::OsRng::default())
        }

        // NOTE: This function relies on a non-cryptographically safe RNG, therefore it
        // must be used ONLY for testing purposes
        pub fn get_random_field_element(seed: u64) -> FieldElement {
            let mut rng = XorShiftRng::seed_from_u64(seed);
            FieldElement::rand(&mut rng)
        }
    };
}

#[macro_export]
macro_rules! generate_field_element_functions {
    ($curve: ident, $curve_parameters: ty) => {{
        generate_algebraic_types!($curve, $curve_parameters);
        _generate_field_element_functions!();
    }};

    // Pre-requisite: FieldElement types generated
    () => {
        _generate_field_element_functions!();
    };
}

/// Pre-requisite: FieldElement and FieldHash types generated
#[macro_export]
macro_rules! _generate_poseidon_hash_functions {
    () => {
        use super::*;
        use primitives::crh::*;

        pub fn get_poseidon_hash_constant_length(
            input_size: usize,
            personalization: Option<Vec<&FieldElement>>,
        ) -> FieldHash {
            if let Some(personalization) = personalization {
                FieldHash::init_constant_length(
                    input_size,
                    Some(
                        personalization
                            .into_iter()
                            .copied()
                            .collect::<Vec<_>>()
                            .as_slice(),
                    ),
                )
            } else {
                FieldHash::init_constant_length(input_size, None)
            }
        }

        pub fn get_poseidon_hash_variable_length(
            mod_rate: bool,
            personalization: Option<Vec<&FieldElement>>,
        ) -> FieldHash {
            if let Some(personalization) = personalization {
                FieldHash::init_variable_length(
                    mod_rate,
                    Some(
                        personalization
                            .into_iter()
                            .copied()
                            .collect::<Vec<_>>()
                            .as_slice(),
                    ),
                )
            } else {
                FieldHash::init_variable_length(mod_rate, None)
            }
        }

        pub fn update_poseidon_hash(hash: &mut FieldHash, input: &FieldElement) {
            hash.update(*input);
        }

        pub fn reset_poseidon_hash(hash: &mut FieldHash, personalization: Option<Vec<&FieldElement>>) {
            if let Some(personalization) = personalization {
                hash.reset(Some(
                    personalization
                        .into_iter()
                        .copied()
                        .collect::<Vec<_>>()
                        .as_slice(),
                ))
            } else {
                hash.reset(None)
            };
        }

        pub fn finalize_poseidon_hash(hash: &FieldHash) -> Result<FieldElement, Error> {
            let result = hash.finalize()?;
            Ok(result)
        }

        #[test]
        fn sample_calls_poseidon_hash() {

            let mut rng = OsRng;
            let hash_input = vec![FieldElement::rand(&mut rng); 2];
            let mut h = get_poseidon_hash_variable_length(false, None);

            //Compute poseidon hash
            update_poseidon_hash(&mut h, &hash_input[0]);
            update_poseidon_hash(&mut h, &hash_input[1]);
            let h_output = finalize_poseidon_hash(&h).unwrap();

            //Call to finalize keeps the state
            reset_poseidon_hash(&mut h, None);
            update_poseidon_hash(&mut h, &hash_input[0]);
            finalize_poseidon_hash(&h).unwrap(); //Call to finalize() keeps the state
            update_poseidon_hash(&mut h, &hash_input[1]);
            assert_eq!(h_output, finalize_poseidon_hash(&h).unwrap());

            //finalize() is idempotent
            assert_eq!(h_output, finalize_poseidon_hash(&h).unwrap());
        }
    };
}

#[macro_export]
macro_rules! generate_poseidon_hash_functions {
    ($curve: ident, $curve_parameters: ty, $field_hash: ident, $batch_field_hash: ident) => {{
        generate_algebraic_types!($curve, $curve_parameters);
        generate_poseidon_hash_types!($field_hash, $batch_field_hash);
        _generate_poseidon_hash_functions!();
    }};

    // Pre-requisite: FieldElement types generated
    ($field_hash: ident, $batch_field_hash: ident) => {{
        generate_poseidon_hash_types!($field_hash, $batch_field_hash);
        _generate_poseidon_hash_functions!();
    }};

    // Pre-requisite: FieldElement and FieldHash types generated
    () => {
        _generate_poseidon_hash_functions!();
    };
}

/// Pre-requisites: FieldElement, MerkleTree types generated
#[macro_export]
macro_rules! _generate_merkle_tree_functions {
    () => {
        use super::*;
        use primitives::merkle_tree::*;
        pub fn new_ginger_mht(height: usize, processing_step: usize) -> Result<GingerMHT, Error> {
            GingerMHT::init(height, processing_step)
        }

        pub fn append_leaf_to_ginger_mht(tree: &mut GingerMHT, leaf: &FieldElement) -> Result<(), Error> {
            let _ = tree.append(*leaf)?;
            Ok(())
        }

        pub fn finalize_ginger_mht(tree: &GingerMHT) -> Result<GingerMHT, Error> {
            tree.finalize()
        }

        pub fn finalize_ginger_mht_in_place(tree: &mut GingerMHT) -> Result<(), Error> {
            tree.finalize_in_place()?;
            Ok(())
        }

        pub fn get_ginger_mht_root(tree: &GingerMHT) -> Result<FieldElement, Error> {
            let root = tree
                .root()
                .ok_or("Unable to get root of a non finalized tree")?;
            Ok(root)
        }

        pub fn get_leaf_index(tree: &GingerMHT, leaf: &FieldElement) -> Option<usize> {
            // Search for address inside the leaves of the tree
            let tree_leaves = tree.get_leaves();
            tree_leaves.iter().position(|x| x == leaf)
        }

        pub fn get_ginger_mht_path(tree: &GingerMHT, leaf_index: u64) -> Result<GingerMHTPath, Error> {
            use std::convert::TryInto;

            let path = match tree.get_merkle_path(leaf_index as usize) {
                Some(path) => path
                    .try_into()
                    .map_err(|e| format!("Unable to convert to binary Merkle Path {:?}", e)),
                None => Err("Unable to get path of a non finalized tree".to_owned()),
            }?;

            Ok(path)
        }

        pub fn reset_ginger_mht(tree: &mut GingerMHT) {
            tree.reset();
        }

        pub fn verify_ginger_merkle_path(
            path: &GingerMHTPath,
            height: usize,
            leaf: &FieldElement,
            root: &FieldElement,
        ) -> Result<bool, Error> {
            path.verify(height, leaf, root)
        }

        pub fn verify_ginger_merkle_path_without_length_check(
            path: &GingerMHTPath,
            leaf: &FieldElement,
            root: &FieldElement,
        ) -> bool {
            path.verify_without_length_check(leaf, root)
        }

        pub fn is_path_leftmost(path: &GingerMHTPath) -> bool {
            path.is_leftmost()
        }

        pub fn is_path_rightmost(path: &GingerMHTPath) -> bool {
            path.is_rightmost()
        }

        pub fn are_right_leaves_empty(path: &GingerMHTPath) -> bool {
            path.are_right_leaves_empty()
        }

        pub fn get_leaf_index_from_path(path: &GingerMHTPath) -> u64 {
            path.leaf_index() as u64
        }

        pub fn get_root_from_path(path: &GingerMHTPath, leaf: &FieldElement) -> FieldElement {
            path.compute_root(leaf)
        }

        #[test]
        fn sample_calls_merkle_path() {

            let height = 6;
            let leaves_num = 2usize.pow(height as u32);

            // Get GingerMHT
            let mut mht = new_ginger_mht(height, leaves_num).unwrap();

            // Add leaves
            let mut mht_leaves = Vec::with_capacity(leaves_num);
            for i in 0..leaves_num / 2 {
                let leaf = get_random_field_element(i as u64);
                mht_leaves.push(leaf);
                append_leaf_to_ginger_mht(&mut mht, &leaf).unwrap();
            }
            for _ in leaves_num / 2..leaves_num {
                mht_leaves.push(FieldElement::zero());
            }

            // Compute the root
            finalize_ginger_mht_in_place(&mut mht).unwrap();
            let mht_root = get_ginger_mht_root(&mht).expect("Tree must've been finalized");

            for (i, leaf) in mht_leaves.iter().enumerate() {
                //Create and verify merkle paths for each leaf
                let path = get_ginger_mht_path(&mht, i as u64).unwrap();
                assert!(verify_ginger_merkle_path_without_length_check(
                    &path, leaf, &mht_root
                ));

                // Check leaf index is the correct one
                assert_eq!(i as u64, get_leaf_index_from_path(&path));

                if i == 0 {
                    // leftmost check
                    assert!(is_path_leftmost(&path));
                } else if i == (leaves_num / 2) - 1 {
                    // non-empty rightmost check
                    assert!(are_right_leaves_empty(&path));
                } else if i == leaves_num - 1 {
                    //rightmost check
                    assert!(is_path_rightmost(&path));
                } else {
                    // Other cases check
                    assert!(!is_path_leftmost(&path));
                    assert!(!is_path_rightmost(&path));

                    if i < (leaves_num / 2) - 1 {
                        assert!(!are_right_leaves_empty(&path));
                    }
                }

                // Serialization/deserialization test
                let path_serialized = serialize_to_buffer(&path, None).unwrap();
                let path_deserialized: GingerMHTPath =
                    deserialize_from_buffer(&path_serialized, Some(true), None).unwrap();
                assert_eq!(path, path_deserialized);
            }
        }
    };
}

#[macro_export]
macro_rules! generate_merkle_tree_functions {
    // No pre-conditions:
    ($curve: ident, $curve_parameters: ty, $field_hash: ident, $batch_field_hash: ident, $tree_params: ident, $tree_arity: expr) => {{
        generate_merkle_tree_types!($curve, $curve_parameters, $field_hash, $batch_field_hash, $tree_params, $tree_arity);
        _generate_merkle_tree_functions!();
    }};

    // Pre-conditions: algebraic types already generated
    ($field_hash: ident, $batch_field_hash: ident, $tree_params: ident, $tree_arity: expr) => {{
        generate_merkle_tree_types!($field_hash, $batch_field_hash, $tree_params, $tree_arity);
        _generate_merkle_tree_functions!();
    }};

    // Pre-conditions: algebraic and poseidon hash types already generated
    ($tree_params: ident, $tree_arity: expr) => {{
        generate_merkle_tree_types!($tree_params, $tree_arity);
        _generate_merkle_tree_functions!();
    }};

    // Pre-conditions: MerkleTree types already generated
    () => {
        _generate_merkle_tree_functions!();
    };
}

/// Pre-conditions: FieldElement and SchnorrSignature types already generated
#[macro_export]
macro_rules! _generate_schnorr_signature_functions {
    () => {
        pub fn schnorr_generate_key() -> (SchnorrPk, SchnorrSk) {
            let mut rng = OsRng;
            let (pk, sk) = SchnorrSigScheme::keygen(&mut rng);
            (pk.0.into_affine(), sk)
        }

        pub fn schnorr_get_public_key(sk: &SchnorrSk) -> SchnorrPk {
            SchnorrSigScheme::get_public_key(sk).0.into_affine()
        }

        pub fn schnorr_verify_public_key(pk: &SchnorrPk) -> bool {
            SchnorrSigScheme::keyverify(&FieldBasedSchnorrPk(pk.into_projective()))
        }

        pub fn schnorr_sign(
            msg: &FieldElement,
            sk: &SchnorrSk,
            pk: &SchnorrPk,
        ) -> Result<SchnorrSig, Error> {
            let mut rng = OsRng;
            SchnorrSigScheme::sign(
                &mut rng,
                &FieldBasedSchnorrPk(pk.into_projective()),
                sk,
                *msg,
            )
        }

        pub fn schnorr_verify_signature(
            msg: &FieldElement,
            pk: &SchnorrPk,
            signature: &SchnorrSig,
        ) -> Result<bool, Error> {
            SchnorrSigScheme::verify(&FieldBasedSchnorrPk(pk.into_projective()), *msg, signature)
        }

        #[test]
        fn sample_calls_schnorr_sig_prove_verify() {

            let mut rng = OsRng;
            let msg = FieldElement::rand(&mut rng);
            {
                let msg_bytes = serialize_to_buffer(&msg, None).unwrap();
                println!("msg bytes: {:?}", into_i8(msg_bytes));
            }

            let (pk, sk) = schnorr_generate_key(); //Keygen
            assert_eq!(schnorr_get_public_key(&sk), pk); //Get pk
            assert!(schnorr_verify_public_key(&pk)); //Verify pk

            //Serialize/deserialize pk
            let pk_serialized = serialize_to_buffer(&pk, Some(true)).unwrap();
            assert_eq!(pk_serialized.len(), SCHNORR_PK_SIZE);
            let pk_deserialized: SchnorrPk =
                deserialize_from_buffer(&pk_serialized, Some(true), Some(true)).unwrap();
            assert_eq!(pk, pk_deserialized);

            //Serialize/deserialize sk
            let sk_serialized = serialize_to_buffer(&sk, None).unwrap();
            assert_eq!(sk_serialized.len(), SCHNORR_SK_SIZE);
            println!("sk bytes: {:?}", into_i8(sk_serialized.clone()));
            let sk_deserialized = deserialize_from_buffer(&sk_serialized, None, None).unwrap();
            assert_eq!(sk, sk_deserialized);

            let sig = schnorr_sign(&msg, &sk, &pk).unwrap(); //Sign msg
            assert!(is_valid(&sig));

            //Serialize/deserialize sig
            let sig_serialized = serialize_to_buffer(&sig, None).unwrap();
            println!("sig bytes: {:?}", into_i8(sig_serialized.clone()));
            assert_eq!(sig_serialized.len(), SCHNORR_SIG_SIZE);
            let sig_deserialized = deserialize_from_buffer(&sig_serialized, Some(true), None).unwrap();
            assert_eq!(sig, sig_deserialized);

            assert!(schnorr_verify_signature(&msg, &pk, &sig).unwrap()); //Verify sig

            //Negative case
            let wrong_msg = FieldElement::rand(&mut rng);
            assert!(!schnorr_verify_signature(&wrong_msg, &pk, &sig).unwrap());
        }

    };
}

#[macro_export]
macro_rules! generate_schnorr_signature_functions {
    // No pre-conditions:
    ($affine_curve: ident, $projective_curve: ident, $curve_parameters: ty, $field_hash: ident, $batch_field_hash: ident) => {{
        generate_schnorr_signature_types!($affine_curve, $projective_curve, $curve_parameters, $field_hash, $batch_field_hash);
        _generate_schnorr_signature_functions!();
    }};

    // Pre-conditions: algebraic types already generated
    ($field_hash: ident, $batch_field_hash: ident, $affine_curve: ident, $projective_curve: ident) => {{
        generate_schnorr_signature_types!($field_hash, $batch_field_hash, $affine_curve, $projective_curve);
        _generate_schnorr_signature_functions!();
    }};

    // Pre-conditions: algebraic and poseidon hash types already generated
    ($projective_curve: ident, $affine_curve: ident) => {{
        generate_schnorr_signature_types!($projective_curve, $affine_curve);
        _generate_schnorr_signature_functions!();
    }};

    // Pre-conditions: FieldElement and SchnorrSignature types already generated
    () => {
        _generate_schnorr_signature_functions!();
    };
}

/// Pre-conditions: FieldElement, FieldHash and VRF types already generated
#[macro_export]
macro_rules! _generate_vrf_functions {
    () => {
        pub fn vrf_generate_key() -> (VRFPk, VRFSk) {
            let mut rng = OsRng;
            let (pk, sk) = VRFScheme::keygen(&mut rng);
            (pk.0.into_affine(), sk)
        }
        
        pub fn vrf_get_public_key(sk: &VRFSk) -> VRFPk {
            VRFScheme::get_public_key(sk).0.into_affine()
        }
        
        pub fn vrf_verify_public_key(pk: &VRFPk) -> bool {
            VRFScheme::keyverify(&FieldBasedEcVrfPk(pk.into_projective()))
        }
        
        pub fn vrf_prove(
            msg: &FieldElement,
            sk: &VRFSk,
            pk: &VRFPk,
        ) -> Result<(VRFProof, FieldElement), Error> {
            let mut rng = OsRng;
        
            //Compute proof
            let proof = VRFScheme::prove(
                &mut rng,
                &VRF_GH_PARAMS,
                &FieldBasedEcVrfPk(pk.into_projective()),
                sk,
                *msg,
            )?;
        
            //Convert gamma from proof to field elements
            let gamma_coords = proof.gamma.to_field_elements().unwrap();
        
            //Compute VRF output
            let output = {
                let mut h = FieldHash::init_constant_length(3, None);
                h.update(*msg);
                gamma_coords.into_iter().for_each(|c| {
                    h.update(c);
                });
                h.finalize()
            }?;
        
            Ok((proof, output))
        }
        
        pub fn vrf_proof_to_hash(
            msg: &FieldElement,
            pk: &VRFPk,
            proof: &VRFProof,
        ) -> Result<FieldElement, Error> {
            VRFScheme::proof_to_hash(
                &VRF_GH_PARAMS,
                &FieldBasedEcVrfPk(pk.into_projective()),
                *msg,
                proof,
            )
        }

        #[test]
        fn sample_calls_vrf_prove_verify() {

            let mut rng = OsRng;
            let msg = FieldElement::rand(&mut rng);
            {
                let msg_bytes = serialize_to_buffer(&msg, None).unwrap();
                println!("msg bytes: {:?}", into_i8(msg_bytes));
            }

            let (pk, sk) = vrf_generate_key(); //Keygen
            assert_eq!(vrf_get_public_key(&sk), pk); //Get pk
            assert!(vrf_verify_public_key(&pk)); //Verify pk

            //Serialize/deserialize pk
            let pk_serialized = serialize_to_buffer(&pk, Some(true)).unwrap();
            assert_eq!(pk_serialized.len(), VRF_PK_SIZE);
            let pk_deserialized: VRFPk =
                deserialize_from_buffer(&pk_serialized, Some(true), Some(true)).unwrap();
            assert_eq!(pk, pk_deserialized);

            //Serialize/deserialize sk
            let sk_serialized = serialize_to_buffer(&sk, None).unwrap();
            assert_eq!(sk_serialized.len(), VRF_SK_SIZE);
            println!("sk bytes: {:?}", into_i8(sk_serialized.clone()));
            let sk_deserialized = deserialize_from_buffer(&sk_serialized, None, None).unwrap();
            assert_eq!(sk, sk_deserialized);

            let (vrf_proof, vrf_out) = vrf_prove(&msg, &sk, &pk).unwrap(); //Create vrf proof for msg
            assert!(is_valid(&vrf_proof));

            //Serialize/deserialize vrf proof
            let proof_serialized = serialize_to_buffer(&vrf_proof, Some(true)).unwrap();
            assert_eq!(proof_serialized.len(), VRF_PROOF_SIZE);
            println!("proof bytes: {:?}", into_i8(proof_serialized.clone()));
            let proof_deserialized =
                deserialize_from_buffer(&proof_serialized, Some(true), Some(true)).unwrap();
            assert_eq!(vrf_proof, proof_deserialized);

            //Serialize/deserialize vrf out (i.e. a field element)
            let vrf_out_serialized = serialize_to_buffer(&vrf_out, None).unwrap();
            println!("vrf out bytes: {:?}", into_i8(vrf_out_serialized.clone()));
            let vrf_out_deserialized =
                deserialize_from_buffer(&vrf_out_serialized, None, None).unwrap();
            assert_eq!(vrf_out, vrf_out_deserialized);

            let vrf_out_dup = vrf_proof_to_hash(&msg, &pk, &vrf_proof).unwrap(); //Verify vrf proof and get vrf out for msg
            assert_eq!(vrf_out, vrf_out_dup);

            //Negative case
            let wrong_msg = FieldElement::rand(&mut rng);
            assert!(vrf_proof_to_hash(&wrong_msg, &pk, &vrf_proof).is_err());
        }
    };
}

#[macro_export]
macro_rules! generate_vrf_functions {
    // No pre-conditions:
    ($affine_curve: ident, $projective_curve: ident, $curve_parameters: ty, $field_hash: ident, $batch_field_hash: ident) => {{
        generate_vrf_types!($affine_curve, $projective_curve, $curve_parameters, $field_hash, $batch_field_hash);
        _generate_vrf_functions!();
    }};

    // Pre-conditions: algebraic types already generated
    ($field_hash: ident, $batch_field_hash: ident, $affine_curve: ident, $projective_curve: ident) => {{
        generate_vrf_types!($field_hash, $batch_field_hash, $affine_curve, $projective_curve);
        _generate_vrf_functions!();
    }};

    // Pre-conditions: algebraic and poseidon hash types already generated
    ($projective_curve: ident, $affine_curve: ident) => {{
        generate_vrf_types!($projective_curve, $affine_curve);
        _generate_vrf_functions!();
    }};

    // Pre-conditions: FieldElement, FieldHash and VRF types already generated
    () => {
        _generate_vrf_functions!();
    };
}

/// Pre-conditions: all types generated
#[macro_export]
macro_rules! generate_all_functions {
    () => {
        generate_serialization_functions!();
        generate_field_element_functions!();
        generate_poseidon_hash_functions!();
        generate_merkle_tree_functions!();
        generate_schnorr_signature_functions!();
        generate_vrf_functions!();
    };
}

#[cfg(feature = "groth16")]
#[macro_export]
/// Pre-conditions: Groth16, FieldElement types and serialization functions already generated
macro_rules! _generate_groth16_functions {
    () => {
        pub fn generate_and_save_random_parameters_to_file<C: ConstraintSynthesizer<FieldElement>>(
            circuit: C,
            circuit_name: &str,
            proving_key_path: &str,
            verification_key_path: &str,
        ) -> Result<Parameters, Error>
        {
            use proof_systems::groth16::generate_parameters;
    
            let params = generate_random_parameters::<PairingCurve, _, _>(c, &mut OsRng::default())
            .map_err(|e| {
                format!(
                    "Unable to generate (pk, vk) for {:?} circuit: {:?}",
                    circuit_name,
                    e
                )
            })?;
        
            // Save them at specified paths
            write_to_file(&params, proving_key_path, Some(false))
                .map_err(|e| format!("Unable to save pk to file {:?} : {:?}", proving_key_path, e))?;
        
            write_to_file(&(params.vk), verification_key_path, Some(false)).map_err(|e| {
                format!(
                    "Unable to save vk to file {:?} : {:?}",
                    verification_key_path, e
                )
            })?;
            Ok(())
        }
    
        pub fn create_random_proof<C: ConstraintSynthesizer<FieldElement>>(
            circuit: C,
            proving_key_path: &str,
        ) -> Result<Proof, Error> {
            use proof_systems::groth16::create_random_proof;
    
            // Read proving key
            let params = read_from_file(proving_key_path, Some(false), Some(false))?;
    
            // Create proof
            let proof = create_random_proof(c, &params, &mut OsRng::default())?;
    
            Ok(proof)
        }
    
        pub fn verify_proof(
            public_inputs: &[FieldElement],
            verification_key_path: &str,
        ) -> Result<bool, Error> {
            use proof_systems::groth16::{prepare_verifying_key, verify_proof};
    
            // Read verification key
            let vk = read_from_file(verification_key_path, Some(false), Some(false))?;
    
            // Prepare verification key
            let pvk = prepare_verifying_key(&vk);
    
            // Construct public inputs
            let pub_ins = vec![
                *cumulative_merkle_root,
                *address_merkle_root,
                *payment_hash,
                *hsec,
                *nullifier,
            ];
    
            // Verify proof
            let result = verify_proof(&pvk, &proof, pub_ins.as_slice())?;
    
            Ok(result)
        }
    }   
}

#[cfg(feature = "groth16")]
#[macro_export]
macro_rules! generate_groth16_functions {
    ($curve: ident, $curve_type: ident) => {{
        generate_groth16_types!($curve, $curve_type):
        _generate_groth16_functions!();
    }};

    ($curve: ident) => {{
        generate_groth16_types!($curve):
        _generate_groth16_functions!();
    }};

    () => {
        _generate_groth16_functions!();
    }
}