echo "################ CHECKING ALL FIELD PARAMETERS ##################"
echo "#################################################################"
echo #
echo "###############Checking bls12_377 field parameters:"
echo "############ Base field:"
sage check_field_parameters.sage bls12_377/fq.rs #
echo "############ Scalar field:"
sage check_field_parameters.sage bls12_377/fr.rs #
echo #
echo "################Checking bls12_381 field parameters:"
echo "############ Base field:"
sage check_field_parameters.sage bls12_381/fq.rs #
echo "############ Scalar field:"
sage check_field_parameters.sage jubjub/fq.rs #
echo #
echo "###############Checking bn_382 field parameters:"
echo "############ Base field:"
sage check_field_parameters.sage bn_382/fq.rs #
echo "############ Scalar field:"
sage check_field_parameters.sage bn_382/fr.rs #
echo #
echo "###############Checking ed25519 field parameters:"
echo "############ Base field:"
sage check_field_parameters.sage ed25519/fq.rs #
echo "############ Scalar field:"
sage check_field_parameters.sage ed25519/fr.rs #
echo #
echo "###############Checking edwards_bls12 field parameters:"
echo "############ Base field:"
sage check_field_parameters.sage bls12_377/fr.rs #
echo "############ Scalar field:"
sage check_field_parameters.sage edwards_bls12/fr.rs #
echo #
echo "###############Checking edwards_sw6 field parameters:"
echo "############ Base field:"
sage check_field_parameters.sage bls12_377/fr.rs #
echo "############ Scalar field:"
sage check_field_parameters.sage edwards_sw6/fr.rs #
echo #
echo "###############Checking jubjub field parameters:"
echo "############ Base field:"
sage check_field_parameters.sage jubjub/fq.rs #
echo "############ Scalar field:"
sage check_field_parameters.sage jubjub/fr.rs #
echo #
echo "###############Checking mnt6 field parameters:"
echo "############ Base field:"
sage check_field_parameters.sage mnt6/fq.rs #
echo "############ Scalar field:"
sage check_field_parameters.sage mnt6/fr.rs #
echo #
echo "###############Checking mnt4753 field parameters:"
echo "############ Base field:"
sage check_field_parameters.sage mnt4753/fq.rs #
echo "############ Scalar field:"
sage check_field_parameters.sage mnt6753/fq.rs #
echo #
echo "###############Checking mnt6753 field parameters:"
echo "############ Base field:"
sage check_field_parameters.sage mnt6753/fq.rs #
echo "############ Scalar field:"
sage check_field_parameters.sage mnt4753/fq.rs #
echo #
echo "###############Checking secp256k1 field parameters:"
echo "############ Base field:"
sage check_field_parameters.sage secp256k1/fq.rs #
echo "############ Scalar field:"
sage check_field_parameters.sage secp256k1/fr.rs #
echo #
echo "###############Checking sw6 field parameters:"
echo "############ Base field:"
sage check_field_parameters.sage sw6/fq.rs #
echo "############ Scalar field:"
sage check_field_parameters.sage bls12_377/fq.rs #
echo #
echo "###############Checking tweedle field parameters:"
echo "############ Base field:"
sage check_field_parameters.sage tweedle/fq.rs #
echo "############ Scalar field:"
sage check_field_parameters.sage tweedle/fr.rs #