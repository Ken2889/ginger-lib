use crate::{bytes_to_bits, CryptoError, Error};
use rand::Rng;
use rayon::prelude::*;
use std::{
    fmt::{Debug, Formatter, Result as FmtResult},
    marker::PhantomData,
};

use crate::crh::FixedLengthCRH;
use algebra::{Group, fields::{PrimeField, FpParameters}};
use serde::{Deserialize, Serialize};

pub const CHUNK_SIZE: usize = 3;

pub trait PedersenWindow: Clone {
    const WINDOW_SIZE: usize;
    const NUM_WINDOWS: usize;
}

#[derive(Clone, Default, Serialize, Deserialize)]
#[serde(bound(deserialize = "G: Group"))]
pub struct BoweHopwoodPedersenParameters<G: Group> {
    pub generators: Vec<Vec<G>>,
}

pub struct BoweHopwoodPedersenCRH<G: Group, W: PedersenWindow> {
    group: PhantomData<G>,
    window: PhantomData<W>,
}

impl<G: Group, W: PedersenWindow> BoweHopwoodPedersenCRH<G, W> {
    pub fn create_generators<R: Rng>(rng: &mut R) -> Vec<Vec<G>> {
        let mut generators = Vec::new();
        for _ in 0..W::NUM_WINDOWS {
            let mut generators_for_segment = Vec::new();
            let mut base = G::rand(rng);
            for _ in 0..W::WINDOW_SIZE {
                generators_for_segment.push(base.clone());
                for _ in 0..4 {
                    base.double_in_place();
                }
            }
            generators.push(generators_for_segment);
        }
        generators
    }
}

impl<G: Group, W: PedersenWindow> FixedLengthCRH for BoweHopwoodPedersenCRH<G, W> {
    const INPUT_SIZE_BITS: usize = W::WINDOW_SIZE * W::NUM_WINDOWS * CHUNK_SIZE;
    type Output = G;
    type Parameters = BoweHopwoodPedersenParameters<G>;

    fn setup<R: Rng>(rng: &mut R) -> Result<Self::Parameters, Error> {
        assert_eq!(CHUNK_SIZE, 3);

        // Rough approximation (safe though, as it's an overestimate) of the bound on WINDOW_SIZE described
        // in section 5.4.1.7 of the Zcash protocol specification.
        let maximum_num_chunks_in_segment = <G::ScalarField as PrimeField>::Params::CAPACITY as usize/4;
        if W::WINDOW_SIZE > maximum_num_chunks_in_segment {
            return Err(format!(
                "Bowe-Hopwood hash must have a window size resulting in scalars < (p-1)/2, \
                 maximum segment size is {}",
                maximum_num_chunks_in_segment
            )
            .into());
        }

        let time = start_timer!(|| format!(
            "BoweHopwoodPedersenCRH::Setup: {} segments of {} 3-bit chunks; {{0,1}}^{{{}}} -> G",
            W::NUM_WINDOWS,
            W::WINDOW_SIZE,
            W::WINDOW_SIZE * W::NUM_WINDOWS * CHUNK_SIZE
        ));
        let generators = Self::create_generators(rng);
        end_timer!(time);
        Ok(Self::Parameters { generators })
    }

    fn evaluate(parameters: &Self::Parameters, input: &[u8]) -> Result<Self::Output, Error> {
        assert_eq!(CHUNK_SIZE, 3);

        let eval_time = start_timer!(|| "BoweHopwoodPedersenCRH::Eval");

        let input_len = input.len() * 8;

        if input_len > Self::INPUT_SIZE_BITS {
            return Err(Box::new(CryptoError::Other(
                format!(
                    "incorrect input length of {:?} bits for window params {:?}x{:?}x{}",
                    input_len,
                    W::WINDOW_SIZE,
                    W::NUM_WINDOWS,
                    CHUNK_SIZE,
                )
                .to_owned(),
            )));
        }

        // Pad the input if it is not the current length.
        let mut padded_input = bytes_to_bits(input);
        if input_len < Self::INPUT_SIZE_BITS {
            padded_input.append(&mut vec![false; Self::INPUT_SIZE_BITS - input_len]);
        }

        if parameters.generators.len() != W::NUM_WINDOWS {
            Err(Box::new(CryptoError::Other(
                format!(
                    "Incorrect pp of size {:?} for window params {:?}x{:?}x{}",
                    parameters.generators.len(),
                    W::WINDOW_SIZE,
                    W::NUM_WINDOWS,
                    CHUNK_SIZE
                )
                .to_owned(),
            )))?
        }
        for generators in parameters.generators.iter() {
            if generators.len() != W::WINDOW_SIZE {
                Err(Box::new(CryptoError::Other(format!(
                    "Number of generators: {} not enough for the selected window size: {}",
                    parameters.generators.len(),
                    W::WINDOW_SIZE
                ))))?
            }
        }

        // Compute sum of h_i^{sum of (1-2*c_{i,j,2})*(1+c_{i,j,0}+2*c_{i,j,1})*2^{4*(j-1)} for all j in segment} for all i.
        // Described in section 5.4.1.7 in the Zcash protocol specification.
        let result = padded_input
            .par_chunks(W::WINDOW_SIZE * CHUNK_SIZE)
            .zip(&parameters.generators)
            .map(|(segment_bits, segment_generators)| {
                segment_bits
                    .par_chunks(CHUNK_SIZE)
                    .zip(segment_generators)
                    .map(|(chunk_bits, generator)| {
                        let mut encoded = generator.clone();
                        if chunk_bits[0] {
                            encoded = encoded + generator;
                        }
                        if chunk_bits[1] {
                            encoded = encoded + &generator.double();
                        }
                        if chunk_bits[2] {
                            encoded = encoded.neg();
                        }
                        encoded
                    })
                    .reduce(|| G::zero(), |a, b| a + &b)
            })
            .reduce(|| G::zero(), |a, b| a + &b);
        end_timer!(eval_time);

        Ok(result)
    }
}

impl<G: Group> Debug for BoweHopwoodPedersenParameters<G> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "Bowe-Hopwood Pedersen Hash Parameters {{\n")?;
        for (i, g) in self.generators.iter().enumerate() {
            write!(f, "\t  Generator {}: {:?}\n", i, g)?;
        }
        write!(f, "}}\n")
    }
}

impl<G: Group> BoweHopwoodPedersenParameters<G> {
    pub fn check_consistency(&self) -> bool {
        for (i, p1) in self.generators.iter().enumerate() {
            if p1[0] == G::zero() {
                return false; // infinity generator
            }
            for p2 in self.generators.iter().skip(i + 1) {
                if p1[0] == p2[0] {
                    return false; // duplicate generator
                }
                if p1[0] == p2[0].clone().neg() {
                    return false; // inverse generator
                }
            }
        }
        return true;
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use algebra::curves::tweedle::dee::DeeJacobian;
    use rand::thread_rng;

    #[test]
    fn test_simple_bh() {
        #[derive(Clone)]
        struct TestWindow {}
        impl PedersenWindow for TestWindow {
            const WINDOW_SIZE: usize = 3;
            const NUM_WINDOWS: usize = 3;
        }

        let rng = &mut thread_rng();
        let params =
            <BoweHopwoodPedersenCRH<DeeJacobian, TestWindow> as FixedLengthCRH>::setup(rng)
                .unwrap();
        <BoweHopwoodPedersenCRH<DeeJacobian, TestWindow> as FixedLengthCRH>::evaluate(
            &params,
            &[1, 2, 3],
        )
        .unwrap();
    }
}
