echo "################ CHECKING ALL CURVE PARAMETERS##################"
echo "################################################################"
echo #
echo "###############Checking bls12_377 curve parameters:"
sage check_curve_parameters.sage bls12_377/g1.rs ../fields/bls12_377/fq.rs ../fields/bls12_377/fr.rs #
echo #
echo "################Checking bls12_381 curve parameters:"
sage check_curve_parameters.sage bls12_381/g1.rs ../fields/bls12_381/fq.rs  ../fields/jubjub/fq.rs #
echo #
echo "###############Checking bn_382 curve parameters:"
echo "########### curve g1:"
sage check_curve_parameters.sage bn_382/g1.rs ../fields/bn_382/fq.rs ../fields/bn_382/fr.rs #
echo "########### curve g:"
sage check_curve_parameters.sage bn_382/g.rs ../fields/bn_382/fr.rs ../fields/bn_382/fq.rs #
echo #
echo "################Checking ed25519 curve parameters:"
sage check_curve_parameters.sage ed25519/mod.rs ../fields/ed25519/fq.rs  ../fields/ed25519/fr.rs #
echo #
echo "###############Checking mnt6 curve parameters:"
sage check_curve_parameters.sage mnt6/g1.rs ../fields/mnt6/fq.rs ../fields/mnt6/fr.rs #
echo #
echo "###############Checking mnt4753 curve parameters:"
sage check_curve_parameters.sage mnt4753/g1.rs ../fields/mnt4753/fq.rs  ../fields/mnt6753/fq.rs #
echo #
echo "###############Checking mnt6753 curve parameters:"
sage check_curve_parameters.sage mnt6753/g1.rs ../fields/mnt6753/fq.rs ../fields/mnt4753/fq.rs #
echo #
echo "###############Checking secp256k1 curve parameters:"
sage check_curve_parameters.sage secp256k1/mod.rs ../fields/secp256k1/fq.rs  ../fields/secp256k1/fr.rs #
echo #
echo "###############Checking sw6 curve parameters:" # Very long computation.
sage check_curve_parameters.sage sw6/g1.rs ../fields/sw6/fq.rs ../fields/bls12_377/fq.rs # 
echo #
echo "###############Checking tweedle curve parameters:"
echo "############ dee:"
sage check_curve_parameters.sage tweedle/dee.rs ../fields/tweedle/fq.rs  ../fields/tweedle/fr.rs #
echo "############ dum:"
sage check_curve_parameters.sage tweedle/dum.rs ../fields/tweedle/fr.rs  ../fields/tweedle/fq.rs #