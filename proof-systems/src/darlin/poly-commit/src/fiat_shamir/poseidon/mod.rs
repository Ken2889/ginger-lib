use algebra::{PrimeField, FpParameters, ToBytes, to_bytes};
use crate::{error::Error, FiatShamirRngSeed};

#[derive(Default)]
/// Encoding of seed material as discussed in [issue/22](https://github.com/HorizenLabs/poly-commit/issues/22).
/// Output type of the seed is a vector of field elements
pub struct FiatShamirPoseidonSeed<ConstraintF: PrimeField> {
    /// the maximum allowed number of seed elements.
    max_num_elements: u64,
    /// the maximum allowed (bit) length of seed element
    max_elements_len: u64,
    /// the number of seed elements.
    num_elements: u64,
    /// the byte lengths of the seed elements.
    elements_len: Vec<u64>,
    /// the concatenated byte sequence of elements.
    seed_bytes: Vec<u8>,
    /// the concatenated field element sequence of elements
    seed_fes: Vec<ConstraintF>
}

impl<ConstraintF: PrimeField> FiatShamirRngSeed for FiatShamirPoseidonSeed<ConstraintF> {
    type FinalizedSeed = Vec<ConstraintF>;
    type Error = Error;

    fn new() -> Self {
        let mut new_instance = Self::default();
        new_instance.max_num_elements = (ConstraintF::Params::MODULUS_BITS as u64/8) - 2;
        new_instance.max

        new_instance
    }

    fn add_bytes<'a, T: 'a + ToBytes>(&mut self, elem: &'a T) -> Result<&mut Self, Self::Error> {
        // Check we have not reached the maximum allowed seed size
        if self.num_elements == u64::MAX {
            return Err(Error::BadFiatShamirInitialization(format!(
                "Maximum seed length {} exceeded",
                u64::MAX
            )));
        }

        // Get elem bytes and check that they are not over the maximum allowed elem len
        let mut elem_bytes = to_bytes!(elem).map_err(|_| {
            Error::BadFiatShamirInitialization("Unable to convert elem to bytes".to_owned())
        })?;
        let elem_bytes_len: u64 = elem_bytes.len().try_into().map_err(|_| {
            Error::BadFiatShamirInitialization(format!(
                "Max elem length exceeded. Max: {}",
                u64::MAX
            ))
        })?;

        // Update internal state
        self.num_elements += 1;
        self.elements_len.push(elem_bytes_len);
        self.seed_bytes.append(&mut elem_bytes);
        Ok(self)
    }

    fn add_field<F: PrimeField>(&mut self, elem: &F) -> Result<&mut Self, Self::Error> {
        let fe_bytes = to_bytes!(elem).map_err(|_| {
            Error::BadFiatShamirInitialization("Unable to convert fe to bytes".to_owned())
        })?;

        self.add_bytes(&fe_bytes)
    }

    fn finalize(mut self) -> Self::FinalizedSeed {
        let mut final_seed = Vec::new();
        final_seed.append(&mut to_bytes!(self.num_elements).unwrap());
        final_seed.append(&mut to_bytes!(self.elements_len).unwrap());
        final_seed.append(&mut self.seed_bytes);
        final_seed
    }
}