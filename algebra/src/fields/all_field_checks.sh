echo "################ CHECKING ALL FIELD PARAMETERS ##################"
echo "#################################################################"
echo #
echo "###############Checking ed25519 field parameters:"
echo "############ Base field:"
sage check_field_parameters.sage ed25519/fq.rs #
echo "############ Scalar field:"
sage check_field_parameters.sage ed25519/fr.rs #
echo #
echo "###############Checking secp256k1 field parameters:"
echo "############ Base field:"
sage check_field_parameters.sage secp256k1/fq.rs #
echo "############ Scalar field:"
sage check_field_parameters.sage secp256k1/fr.rs #
echo #
echo "###############Checking tweedle field parameters:"
echo "############ Base field:"
sage check_field_parameters.sage tweedle/fq.rs #
echo "############ Scalar field:"
sage check_field_parameters.sage tweedle/fr.rs #