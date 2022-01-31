use algebra::{PrimeField, FpParameters, CanonicalSerialize, serialize_no_metadata, ToBits, ToConstraintField, Field, EndoMulCurve};
use primitives::{PoseidonSponge, PoseidonParameters, SBox, check_field_equals, AlgebraicSponge};
use super::{FiatShamirRngSeed, FiatShamirRng, Error};
use std::convert::TryInto;

/// Circuit implementation of this RNG
pub mod constraints;

#[derive(Default)]
/// Encoding of seed material as discussed in [issue/22](https://github.com/HorizenLabs/poly-commit/issues/22).
/// Output type of the seed is a vector of field elements
pub struct FiatShamirPoseidonSeed<ConstraintF: PrimeField> {
    /// the number of seed elements.
    num_elements: u64,
    /// the bit length of the seed elements.
    elements_len: Vec<u64>,
    /// the concatenated bit sequence of elements, derived from bytes or non native field elements
    seed_bits: Vec<bool>,
    /// the concatenated native field elements
    seed_fes: Vec<ConstraintF>
}

impl<ConstraintF: PrimeField> FiatShamirPoseidonSeed<ConstraintF> {
    fn check_seed_input(&self, input_len: usize) -> Result<u64, Error> {
        // Check we have not reached the maximum allowed seed size
        if self.num_elements == u64::MAX {
            return Err(Error::BadFiatShamirInitialization(format!(
                "Maximum seed length {} exceeded",
                u64::MAX
            )));
        }

        let input_len_u64: u64 = input_len.try_into().map_err(|_| {
            Error::BadFiatShamirInitialization(format!(
                "Max elem length exceeded. Max: {}",
                u64::MAX
            ))
        })?;

        Ok(input_len_u64)
    }
}

impl<ConstraintF: PrimeField> FiatShamirRngSeed for FiatShamirPoseidonSeed<ConstraintF> {
    type FinalizedSeed = Vec<ConstraintF>;
    type Error = Error;

    fn new() -> Self {
        Self::default()
    }

    fn add_bytes<'a, T: 'a + CanonicalSerialize>(&mut self, elem: &'a T) -> Result<&mut Self, Self::Error> {
        // Check that we can add this input to the seed
        let input_len = self.check_seed_input(elem.serialized_size() * 8)?;
        
        // Serialize and get the bits
        let mut elem_bits = serialize_no_metadata!(elem)
            .map_err(|_| {
                Error::BadFiatShamirInitialization("Unable to convert elem to bytes".to_owned())
            })?
            .write_bits();

        // Update internal state
        self.num_elements += 1;
        self.elements_len.push(input_len);
        self.seed_bits.append(&mut elem_bits);
        Ok(self)
    }

    fn add_field<F: PrimeField>(&mut self, elem: &F) -> Result<&mut Self, Self::Error> {
        // Check that we can add this input to the seed
        let input_len = self.check_seed_input(F::Params::MODULUS_BITS as usize)?;

        if check_field_equals::<F, ConstraintF>() {
            // Element belonging to native field
            // Safe casting, since we checked that the two types are the same
            // NOTE: If we don't want to use unsafe we can convert by serialization/deserialization
            //       but it's more expensive.
            let fe = unsafe { std::mem::transmute::<Vec<F>, Vec<ConstraintF>>(vec![*elem]) }[0];
            self.seed_fes.push(fe);
            
        } else {
            self.seed_bits.append(&mut elem.write_bits());
        }

        // Update internal state
        self.num_elements += 1;
        self.elements_len.push(input_len);

        Ok(self)
    }

    fn finalize(mut self) -> Result<Self::FinalizedSeed, Self::Error> {

        // Convert a u64 to its LE bits (doesn't really matter the endianness)
        let u64_to_bit_vec = |mut val: u64| -> Vec<bool> {
            let mut v = Vec::with_capacity(64);

            for _ in 0..64 {
                v.push(val & 1 == 1);
                val >>= 1;
            }

            v
        };

        // Build seed
        let mut final_seed_bits = Vec::new();

        // Convert num_elements to bits and append to final_seed_bits
        {
            let mut num_elements = u64_to_bit_vec(self.num_elements);
            final_seed_bits.append(&mut num_elements);
        }

        // Convert elements_len to bits and append to final_seed_bits
        {
            let mut elements_len = self
                .elements_len
                .iter()
                .flat_map(|val | u64_to_bit_vec(*val))
                .collect::<Vec<bool>>();
            
            final_seed_bits.append(&mut elements_len);
        }
        
        // Append data bits to final_seed_bits
        final_seed_bits.append(&mut self.seed_bits);

        // Build field elements
        let mut final_seed_fes = final_seed_bits
            .to_field_elements()
            .unwrap();

        final_seed_fes.append(&mut self.seed_fes);

        // Return field elements
        Ok(final_seed_fes)
    }
}

impl<SpongeF, P, SB> FiatShamirRng for PoseidonSponge<SpongeF, P, SB>
    where
        SpongeF: PrimeField,
        P: PoseidonParameters<Fr = SpongeF>,
        SB: SBox<Field = SpongeF, Parameters = P>,
{
    type State = Vec<SpongeF>;
    type Seed = FiatShamirPoseidonSeed<SpongeF>;
    type Error = Error;

    fn from_seed(seed: <FiatShamirPoseidonSeed<SpongeF> as FiatShamirRngSeed>::FinalizedSeed) -> Self {
        // Initialize Poseidon sponge
        let mut sponge = Self::init();

        // Absorb seed elements into the sponge
        seed
            .iter()
            .for_each(|fe| <Self as AlgebraicSponge<SpongeF>>::absorb(&mut sponge, fe));

        // If there are pending elements, add them to the state and apply a permutation
        if sponge.pending.len() != 0 {
            sponge.apply_permutation();
        }

        // Return the sponge
        sponge
    }

    fn absorb<F: Field, A: ToConstraintField<F> + CanonicalSerialize>(&mut self, to_absorb: A) -> Result<&mut Self, Self::Error> {
        <Self as AlgebraicSponge<SpongeF>>::absorb(self, &to_absorb);

        Ok(self)
    }

    fn squeeze<F: PrimeField>(&mut self) -> F
    {
        // We allow only squeezing native field elements
        assert!(check_field_equals::<F, SpongeF>());

        // Squeeze field elements
        let fes = <Self as AlgebraicSponge<SpongeF>>::squeeze(self, 1);

        // Cast to SpongeF and return
        (unsafe { std::mem::transmute::<Vec<SpongeF>, Vec<F>>(fes) })[0]
    }

    fn squeeze_128_bits_challenge<G: EndoMulCurve>(&mut self) -> G::ScalarField {
        // Squeeze 128 bits from the sponge
        let bits = self.squeeze_bits(128);

        // Return an endo scalar out of them
        G::endo_rep_to_scalar(bits).expect("Should be able to get endo scalar")
    }

    fn get_state(&self) -> Self::State {
        <Self as AlgebraicSponge<SpongeF>>::get_state(self)
    }

    fn set_state(&mut self, new_state: Self::State) {
        <Self as AlgebraicSponge<SpongeF>>::set_state(self, new_state)
    }
}