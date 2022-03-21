echo "################ CHECKING ALL CURVE PARAMETERS##################"
echo "################################################################"
echo #
echo "################Checking ed25519 curve parameters:"
sage check_curve_parameters.sage ed25519/mod.rs ../fields/ed25519/fq.rs  ../fields/ed25519/fr.rs #
echo #
echo "###############Checking secp256k1 curve parameters:"
sage check_curve_parameters.sage secp256k1/mod.rs ../fields/secp256k1/fq.rs  ../fields/secp256k1/fr.rs #
echo #
echo "###############Checking tweedle curve parameters:"
echo "############ dee:"
sage check_curve_parameters.sage tweedle/dee.rs ../fields/tweedle/fq.rs  ../fields/tweedle/fr.rs #
echo "############ dum:"
sage check_curve_parameters.sage tweedle/dum.rs ../fields/tweedle/fr.rs  ../fields/tweedle/fq.rs #