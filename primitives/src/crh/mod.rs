use algebra::{bytes::ToBytes, Field, PrimeField, FpParameters, ToConstraintField};
use rand::Rng;
use serde::{Deserialize, Serialize};
use std::hash::Hash;

pub mod bowe_hopwood;
pub mod injective_map;
pub mod pedersen;

pub mod sbox;
pub use self::sbox::*;

pub mod poseidon;
pub use self::poseidon::*;

use crate::{CryptoError, Error};
use rayon::prelude::*;

pub trait FixedLengthCRH {
    const INPUT_SIZE_BITS: usize;
    type Output: ToBytes + Serialize + for<'a> Deserialize<'a> + Clone + Eq + Hash + Default;
    type Parameters: Clone + Serialize + for<'a> Deserialize<'a> + Default;

    fn setup<R: Rng>(r: &mut R) -> Result<Self::Parameters, Error>;
    fn evaluate(parameters: &Self::Parameters, input: &[u8]) -> Result<Self::Output, Error>;
}

/// Define parameters required to implement a hash function working with field arithmetics.
/// TODO: Depending on the hash construction some parameters may be present and others not
///       we should think about particularizing or generalizing this trait definition.
pub trait FieldBasedHashParameters: Clone {
    type Fr: Field;

    /// The rate of the hash function
    const R: usize;
}

pub trait FieldBasedHash {
    type Data: Field;
    type Parameters: FieldBasedHashParameters<Fr = Self::Data>;

    /// Initialize a Field Hash accepting inputs of constant length `input_size`:
    /// any attempt to finalize the hash after having updated the Self instance
    /// with a number of inputs not equal to `input_size` should result in an error.
    /// Initialize the hash to a null state, or with `personalization` if specified.
    fn init_constant_length(input_size: usize, personalization: Option<&[Self::Data]>) -> Self;

    /// Initialize a Field Hash accepting inputs of variable length.
    /// It is able to serve two different modes, selected by the boolean `mod_rate`:
    /// - `mod_rate` = False is for the ususal variable length hash, whereas
    /// - `mod_rate` = True allows the input only to be a multiple of the rate (and hence
    /// should throw an error when trying to finalize with a non-multiple of rate input).
    /// This mode allows an optimized handling of padding, saving constraints in SNARK applications;
    fn init_variable_length(mod_rate: bool, personalization: Option<&[Self::Data]>) -> Self;

    /// Update the hash with `input`.
    fn update(&mut self, input: Self::Data) -> &mut Self;

    /// Return the hash. This method is idempotent, and calling it multiple times will
    /// give the same result.
    fn finalize(&self) -> Result<Self::Data, Error>;

    /// Reset self to its initial state, allowing to change `personalization` too if needed.
    fn reset(&mut self, personalization: Option<&[Self::Data]>) -> &mut Self;
}

/// Helper allowing to hash the implementor of this trait into a Field
pub trait FieldHasher<F: Field, H: FieldBasedHash<Data = F>> {
    /// Hash `self`, given some optional `personalization` into a Field
    fn hash(&self, personalization: Option<&[H::Data]>) -> Result<H::Data, Error>;
}

pub trait BatchFieldBasedHash {
    type Data: Field;

    /// Specification of this type allows to provide a default implementation and more flexibility
    /// when included in other traits/struct (i.e. a FieldBasedMerkleTree using both simple and
    /// batch hashes can only specify this trait, simplifying its design and usage).
    /// Still, it's a reasonable addition for a trait like this.
    type BaseHash: FieldBasedHash<Data = Self::Data>;

    /// Given an `input_array` of size n * hash_rate, batches the computation of the n hashes
    /// and outputs the n hash results.
    /// NOTE: The hashes are independent from each other, therefore the output is not some sort
    /// of aggregated hash but it's actually the hash result of each of the inputs, grouped in
    /// hash_rate chunks.
    fn batch_evaluate(input_array: &[Self::Data]) -> Result<Vec<Self::Data>, Error> {
        let rate = <<Self::BaseHash as FieldBasedHash>::Parameters as FieldBasedHashParameters>::R;
        if input_array.len() % rate != 0 {
            return Err(Box::new(CryptoError::Other(
                "The length of the input data array is not a multiple of the rate".to_owned(),
            )));
        }
        if input_array.len() == 0 {
            return Err(Box::new(CryptoError::Other(
                "Input data array does not contain any data".to_owned(),
            )));
        }

        Ok(input_array
            .par_chunks(rate)
            .map(|chunk| {
                let mut digest =
                    <Self::BaseHash as FieldBasedHash>::init_constant_length(rate, None);
                chunk.iter().for_each(|input| {
                    digest.update(input.clone());
                });
                digest.finalize().unwrap()
            })
            .collect::<Vec<_>>())
    }

    /// Given an `input_array` of size n * hash_rate, batches the computation of the n hashes
    /// and outputs the n hash results.
    /// Avoids a copy by requiring to pass the `output_array` already as input to the
    /// function.
    /// NOTE: The hashes are independent from each other, therefore the output is not some sort
    /// of aggregated hash but it's actually the hash result of each of the inputs, grouped in
    /// hash_rate chunks.
    fn batch_evaluate_in_place(
        input_array: &mut [Self::Data],
        output_array: &mut [Self::Data],
    ) -> Result<(), Error> {
        let rate = <<Self::BaseHash as FieldBasedHash>::Parameters as FieldBasedHashParameters>::R;
        if input_array.len() % rate != 0 {
            return Err(Box::new(CryptoError::Other(
                "The length of the input data array is not a multiple of the rate".to_owned(),
            )));
        }
        if input_array.len() == 0 {
            return Err(Box::new(CryptoError::Other(
                "Input data array does not contain any data".to_owned(),
            )));
        }
        if output_array.len() != input_array.len() / rate {
            return Err(Box::new(CryptoError::Other(format!(
                "Output array size must be equal to input_array_size/rate. Output array size: {}, Input array size: {}, Rate: {}",
                output_array.len(),
                input_array.len(),
                rate
            ))));
        }
        input_array
            .par_chunks(rate)
            .zip(output_array.par_iter_mut())
            .for_each(|(inputs, output)| {
                let mut digest =
                    <Self::BaseHash as FieldBasedHash>::init_constant_length(rate, None);
                inputs.iter().for_each(|input| {
                    digest.update(input.clone());
                });
                *output = digest.finalize().unwrap();
            });
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub enum SpongeMode {
    Absorbing,
    Squeezing,
}

/// The trait for an algebraic sponge
pub trait AlgebraicSponge<SpongeF: PrimeField>: Clone
{
    /// The internal state of the Sponge
    type State: Clone + Eq + PartialEq + std::fmt::Debug;

    /// Initialize the sponge in absorbing mode
    fn init() -> Self;

    /// Get the sponge internal state
    fn get_state(&self) -> Self::State;

    /// Set the sponge internal state
    fn set_state(&mut self, state: Self::State);

    /// Get Sponge current operating mode
    fn get_mode(&self) -> &SpongeMode;

    /// Set Sponge operating mode
    fn set_mode(&mut self, mode: SpongeMode);

    /// Absorb field elements belonging to F.
    /// If 'to_absorb' is empty an Error should be thrown and state consistency should be assured.
    fn absorb<F: Field, A: ToConstraintField<F>>(&mut self, to_absorb: A) -> Result<&mut Self, Error>;

    /// Squeeze field elements belonging to SpongeF.
    /// If 'num' == 0 an Error should be thrown and state consistency should be assured.
    fn squeeze(&mut self, num: usize) -> Result<Vec<SpongeF>, Error>;

    /// Squeeze 'num_bits' from this sponge
    /// If 'num_bits' == 0 an Error should be thrown and state consistency should be assured.
    fn squeeze_bits(&mut self, num_bits: usize) -> Result<Vec<bool>, Error> {
        // We return a certain amount of bits by squeezing field elements instead,
        // serialize them and return their bits.

        // Smallest number of field elements to squeeze to reach 'num_bits' is ceil(num_bits/FIELD_CAPACITY).
        // This is done to achieve uniform distribution over the output space, and it also
        // comes handy as in the circuit we don't need to enforce range proofs for them.
        let usable_bits = SpongeF::Params::CAPACITY as usize; 
        let num_elements = (num_bits + usable_bits - 1) / usable_bits;
        let src_elements = self.squeeze(num_elements)?;

        // Serialize field elements into bits and return them
        let mut dest_bits: Vec<bool> = Vec::with_capacity(num_bits);
    
        // discard leading zeros + 1 bit below modulus bits
        let skip = SpongeF::Params::MODULUS_BITS as usize - usable_bits; 
        for elem in src_elements.iter() {
            let elem_bits = elem.write_bits();
            dest_bits.extend_from_slice(&elem_bits[skip..]);
        }
        Ok(dest_bits[..num_bits].to_vec())
    }

    /// Reset the sponge to its initial state
    fn reset(&mut self) {
        *self = Self::init();
    }
}

#[cfg(test)]
mod test {

    use algebra::{Group, fields::tweedle::Fr as Fr, Field, UniformRand};

    use super::*;
    use crate::crh::poseidon::{TweedleFrBatchPoseidonHash, TweedleFrPoseidonHash};

    use rand::{SeedableRng, RngCore};
    use rand_xorshift::XorShiftRng;

    struct DummyTweedleFrBatchPoseidonHash;

    impl BatchFieldBasedHash for DummyTweedleFrBatchPoseidonHash {
        type Data = Fr;
        type BaseHash = TweedleFrPoseidonHash;
    }

    pub(crate) fn constant_length_field_based_hash_test<H: FieldBasedHash>(
        digest: &mut H,
        inputs: Vec<H::Data>,
    ) {
        let inputs_len = inputs.len();

        let final_elem = inputs[inputs_len - 1].clone();

        digest.reset(None);
        inputs.into_iter().take(inputs_len - 1).for_each(|fe| {
            digest.update(fe);
        });

        // Test call to finalize() with too few inputs with respect to the declared size
        // results in an error.
        assert!(
            digest.finalize().is_err(),
            "Success call to finalize despite smaller number of inputs"
        );

        //Test finalize() being idempotent
        digest.update(final_elem);
        let output = digest.finalize().unwrap();
        assert_eq!(
            output,
            digest.finalize().unwrap(),
            "Two subsequent calls to finalize gave different results"
        );

        // Test call to finalize() with too much inputs with respect to the declared size
        // results in an error.
        digest.update(final_elem);
        assert!(
            digest.finalize().is_err(),
            "Success call to finalize despite bigger number of inputs"
        );
    }

    pub(crate) fn variable_length_field_based_hash_test<H: FieldBasedHash>(
        digest: &mut H,
        inputs: Vec<H::Data>,
        mod_rate: bool,
    ) {
        let rate = <H::Parameters as FieldBasedHashParameters>::R;

        let pad_inputs = |mut inputs: Vec<H::Data>| -> Vec<H::Data> {
            inputs.push(H::Data::one());
            inputs.append(&mut vec![H::Data::zero(); rate - (inputs.len() % rate)]);
            inputs
        };

        if mod_rate {
            constant_length_field_based_hash_test(digest, inputs);
        } else {
            // Check padding is added correctly and that the hash is collision free when input
            // is not modulus rate
            let output = digest.finalize().unwrap();
            let padded_inputs = pad_inputs(inputs.clone());
            digest.reset(None);
            padded_inputs.iter().for_each(|fe| {
                digest.update(fe.clone());
            });
            assert_ne!(
                output,
                digest.finalize().unwrap(),
                "Incorrect padding: collision detected"
            );

            // Check padding is added correctly and that the hash is collision free also when input
            // happens to be modulus rate
            let output = digest.finalize().unwrap();
            let padded_inputs = pad_inputs(padded_inputs);
            digest.reset(None);
            padded_inputs.into_iter().for_each(|fe| {
                digest.update(fe);
            });
            assert_ne!(
                output,
                digest.finalize().unwrap(),
                "Incorrect padding: collision detected"
            );
        }
    }

    pub(crate) fn algebraic_sponge_consistency_test<H: AlgebraicSponge<F1>, F1: PrimeField, F2: PrimeField, R: RngCore>(rng: &mut R, expected_output: F1)
    {
        let mut sponge = H::init();
        assert!(matches!(sponge.get_mode(), SpongeMode::Absorbing));

        // Absorb random native field elements
        let to_absorb = (0..10).map(|_| F1::rand(rng)).collect::<Vec<_>>();
        sponge.absorb(to_absorb).unwrap();
        assert!(matches!(sponge.get_mode(), SpongeMode::Absorbing));

        // Absorb random non native field elements
        let to_absorb = (0..10).map(|_| F2::rand(rng)).collect::<Vec<_>>();
        sponge.absorb(to_absorb).unwrap();
        assert!(matches!(sponge.get_mode(), SpongeMode::Absorbing));

        // Absorb random bytes
        let to_absorb = (0..100).map(|_| rng.gen()).collect::<Vec<u8>>();
        sponge.absorb::<F1, _>(to_absorb.as_slice()).unwrap();
        assert!(matches!(sponge.get_mode(), SpongeMode::Absorbing));

        let out: F1 = sponge.squeeze(1).unwrap()[0];
        assert_eq!(out, expected_output);
        assert!(matches!(sponge.get_mode(), SpongeMode::Squeezing));
        // println!("{:?}", out);

        // Check that calling squeeze() multiple times without absorbing
        // changes the output
        let mut prev = out;
        for _ in 0..100 {
            let curr = sponge.squeeze(1).unwrap()[0];
            assert!(matches!(sponge.get_mode(), SpongeMode::Squeezing));
            assert!(prev != curr);
            prev = curr;
        }

        // Check squeeze() outputs the correct number of field elements
        // all different from each others
        for i in 1..=10 {
            let mut set = std::collections::HashSet::new();
            let random_fes = (0..i).map(|_| F1::rand(rng)).collect::<Vec<_>>();
            sponge.absorb(random_fes).unwrap();
            assert!(matches!(sponge.get_mode(), SpongeMode::Absorbing));

            // Native squeeze test
            let outs: Vec<F1> = sponge.squeeze(i).unwrap();
            assert!(matches!(sponge.get_mode(), SpongeMode::Squeezing));
            assert_eq!(i, outs.len());

            // HashSet::insert(val) returns false if val was already present, so to check
            // that all the elements output by the sponge are different, we assert insert()
            // returning always true
            outs.into_iter().for_each(|f| assert!(set.insert(f)));
        }

        // Check squeeze_bits() outputs the correct number of bits
        for i in 1..=10 {
            let random_fes = (0..i).map(|_| F1::rand(rng)).collect::<Vec<_>>();
            sponge.absorb(random_fes).unwrap();
            assert!(matches!(sponge.get_mode(), SpongeMode::Absorbing));

            // Native squeeze bits test
            let out_bits: Vec<bool> = sponge.squeeze_bits(i * 10).unwrap();
            assert_eq!(i * 10, out_bits.len());
            assert!(matches!(sponge.get_mode(), SpongeMode::Squeezing));

            // Bits shouldn't be all 0 with overwhelming probabiltiy
            assert!(!out_bits.iter().all(|bit| !bit));

            // Bits shouldn't be all 1 with overwhelming probabiltiy
            assert!(!out_bits.into_iter().all(|bit| bit));
        }

        //Test edge cases.
        sponge.reset();
        assert!(matches!(sponge.get_mode(), SpongeMode::Absorbing));

        let prev_state = sponge.get_state();

        // Absorb nothing. Check that the internal state is not changed.
        assert!(sponge.absorb(Vec::<F1>::new()).is_err());
        assert!(matches!(sponge.get_mode(), SpongeMode::Absorbing));
        assert_eq!(prev_state, sponge.get_state());

        // Squeeze nothing. Check that the internal state is not changed.
        assert!(sponge.squeeze(0).is_err());
        assert!(matches!(sponge.get_mode(), SpongeMode::Absorbing));
        assert_eq!(prev_state, sponge.get_state());
    }

    #[ignore]
    #[test]
    fn test_default_batch_hash_implementation() {
        let rate = 2;
        let num_inputs = 100;
        let mut inputs = Vec::with_capacity(num_inputs);
        let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

        for _ in 0..num_inputs {
            inputs.push(Fr::rand(&mut rng))
        }

        let batch_hash_output = TweedleFrBatchPoseidonHash::batch_evaluate(inputs.as_slice()).unwrap();
        let dummy_batch_hash_output =
            DummyTweedleFrBatchPoseidonHash::batch_evaluate(inputs.as_slice()).unwrap();
        assert_eq!(batch_hash_output, dummy_batch_hash_output);

        let mut batch_hash_output_new = vec![Fr::zero(); num_inputs / rate];
        let mut dummy_batch_hash_output_new = vec![Fr::zero(); num_inputs / rate];

        TweedleFrBatchPoseidonHash::batch_evaluate_in_place(
            inputs.as_mut_slice(),
            batch_hash_output_new.as_mut_slice(),
        )
        .unwrap();
        DummyTweedleFrBatchPoseidonHash::batch_evaluate_in_place(
            inputs.as_mut_slice(),
            dummy_batch_hash_output_new.as_mut_slice(),
        )
        .unwrap();

        assert_eq!(batch_hash_output_new, dummy_batch_hash_output_new);
        assert_eq!(batch_hash_output, batch_hash_output_new);
        assert_eq!(dummy_batch_hash_output, dummy_batch_hash_output_new);
    }
}
