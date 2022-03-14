extern crate rand;
extern crate rayon;

use algebra::PrimeField;

use std::{marker::PhantomData, ops::Mul};

use crate::{
    crh::{FieldBasedHash, FieldBasedHashParameters, SBox},
    CryptoError, Error,
};

use num_traits::Zero;

pub mod batched_crh;

pub mod parameters;
pub use self::parameters::*;

pub mod sbox;
pub use self::sbox::*;

pub trait PoseidonParameters: 'static + FieldBasedHashParameters + Clone {
    const T: usize; // Number of S-Boxes
    const R_F: i32; // Number of full rounds
    const R_P: i32; // Number of partial rounds
    const ZERO: Self::Fr; // The zero element in the field
    const AFTER_ZERO_PERM: &'static [Self::Fr]; // State vector after a zero permutation
    const ROUND_CST: &'static [Self::Fr]; // Array of round constants
    const MDS_CST: &'static [Self::Fr]; // The MDS matrix

    /// Add round constants to `state` starting from `start_idx_cst`, modifying `state` in place.
    #[inline]
    fn add_round_constants(
        state: &mut [<Self as FieldBasedHashParameters>::Fr],
        start_idx_cst: &mut usize,
    ) {
        for d in state.iter_mut() {
            let rc = Self::ROUND_CST[*start_idx_cst];
            *d += &rc;
            *start_idx_cst += 1;
        }
    }

    /// Perform scalar multiplication between vectors `res` and `state`,
    /// modifying `res` in place.
    #[inline]
    fn dot_product(
        res: &mut <Self as FieldBasedHashParameters>::Fr,
        state: &mut [<Self as FieldBasedHashParameters>::Fr],
        mut start_idx_cst: usize,
    ) {
        state.iter().for_each(|x| {
            let elem = x.mul(&Self::MDS_CST[start_idx_cst]);
            start_idx_cst += 1;
            *res += &elem;
        });
    }

    /// Perform matrix mix on `state`, modifying `state` in place.
    #[inline]
    fn matrix_mix(state: &mut Vec<<Self as FieldBasedHashParameters>::Fr>) {
        // the new state where the result will be stored initialized to zero elements
        let mut new_state = vec![<Self as FieldBasedHashParameters>::Fr::zero(); Self::T];

        let mut idx_cst = 0;
        for i in 0..Self::T {
            Self::dot_product(&mut new_state[i], state, idx_cst);
            idx_cst += Self::T;
        }
        *state = new_state;
    }
}

pub trait PoseidonShortParameters: PoseidonParameters {
    /// MDS matrix supporting short Montgomery multiplication with respect to the short
    /// Montgomery constant R_2=2^64
    const MDS_CST_SHORT: &'static [Self::Fr];
}

#[derive(Derivative)]
#[derivative(Clone(bound = ""), Debug(bound = ""))]
pub struct PoseidonHash<
    F: PrimeField,
    P: PoseidonParameters<Fr = F>,
    SB: SBox<Field = F, Parameters = P>,
> {
    state: Vec<F>,
    pending: Vec<F>,
    input_size: Option<usize>,
    updates_ctr: usize,
    mod_rate: bool,
    _parameters: PhantomData<P>,
    _sbox: PhantomData<SB>,
}

impl<F, P, SB> PoseidonHash<F, P, SB>
where
    F: PrimeField,
    P: PoseidonParameters<Fr = F>,
    SB: SBox<Field = F, Parameters = P>,
{
    fn _init(constant_size: Option<usize>, mod_rate: bool, personalization: Option<&[F]>) -> Self {
        let mut state = Vec::with_capacity(P::T);
        for i in 0..P::T {
            state.push(P::AFTER_ZERO_PERM[i]);
        }

        let mut instance = Self {
            state,
            pending: Vec::with_capacity(P::R),
            input_size: constant_size,
            updates_ctr: 0,
            mod_rate,
            _parameters: PhantomData,
            _sbox: PhantomData,
        };

        // If personalization Vec is not multiple of the rate, we pad it with zero field elements.
        // This will allow eventually to precompute the constants of the initial state. This
        // is exactly as doing H(personalization, padding, ...). NOTE: this way of personalizing
        // the hash is not mentioned in https://eprint.iacr.org/2019/458.pdf
        if personalization.is_some() {
            // Use a support variable-length non mod rate instance
            let mut personalization_instance = Self::init_variable_length(false, None);
            let personalization = personalization.unwrap();

            // Apply personalization
            for &p in personalization.into_iter() {
                personalization_instance.update(p);
            }

            // Apply padding (according to the variable length input strategy)
            personalization_instance.update(F::one());
            while personalization_instance.pending.len() != 0 {
                personalization_instance.update(F::zero());
            }
            debug_assert_eq!(personalization_instance.pending.len(), 0);

            // Set the new initial state
            instance.state = personalization_instance.state;
        }
        instance
    }

    #[inline]
    fn apply_permutation_if_needed(&mut self) {
        if self.pending.len() == P::R {
            for (input, state) in self.pending.iter().zip(self.state.iter_mut()) {
                *state += input;
            }
            Self::poseidon_perm(&mut self.state);
            self.pending.clear();
        }
    }

    #[inline]
    fn get_hash(mut state: Vec<F>, inputs: Vec<F>) -> F {
        for (input, s) in inputs.iter().zip(state.iter_mut()) {
            *s += input;
        }
        Self::poseidon_perm(&mut state);
        state[0]
    }

    #[inline]
    // Padding strategy is described in https://eprint.iacr.org/2019/458.pdf(Section 4.2)
    fn pad_and_finalize(&self) -> F {
        // Constant input length instance
        if self.input_size.is_some() {
            // The constant size is modulus rate, so we already have the hash output in state[0]
            // as a permutation is applied each time pending reaches P::R length
            if self.pending.is_empty() {
                self.state[0].clone()
            }
            // Pending is not empty: pad with 0s up to rate then compute the hash,
            else {
                Self::get_hash(self.state.clone(), self.pending.clone())
            }
        }
        // Variable input length instance
        else {
            // The input is of variable length, but always modulus rate: result is already available
            // in state[0] as a permutation is applied each time pending reaches P::R length
            if self.mod_rate {
                self.state[0].clone()
            }
            // The input is of variable length, but not modulus rate: we always need to apply
            // padding. Pad with a single 1 and then 0s up to rate. Compute hash.
            else {
                let mut pending = self.pending.clone(); // Can also be empty if the input happens to be mod rate
                pending.push(F::one());
                Self::get_hash(self.state.clone(), pending)
            }
        }
    }

    pub(crate) fn poseidon_perm(state: &mut Vec<F>) {
        // index that goes over the round constants
        let round_cst_idx = &mut 0;

        // First full rounds
        for _i in 0..P::R_F {
            // Add the round constants to the state vector
            P::add_round_constants(state, round_cst_idx);

            // Apply the S-BOX to each of the elements of the state vector
            SB::apply_full(state);

            // Perform matrix mix
            P::matrix_mix(state);
        }

        // Partial rounds
        for _i in 0..P::R_P {
            // Add the round constants to the state vector
            P::add_round_constants(state, round_cst_idx);

            // Apply S-BOX only to the first element of the state vector
            SB::apply_partial(state);

            // Perform matrix mix
            P::matrix_mix(state);
        }

        // Second full rounds
        for _i in 0..P::R_F {
            // Add the round constants
            P::add_round_constants(state, round_cst_idx);

            // Apply the S-BOX to each of the elements of the state vector
            SB::apply_full(state);

            // Perform matrix mix
            P::matrix_mix(state);
        }
    }
}

impl<F, P, SB> FieldBasedHash for PoseidonHash<F, P, SB>
where
    F: PrimeField,
    P: PoseidonParameters<Fr = F>,
    SB: SBox<Field = F, Parameters = P>,
{
    type Data = F;
    type Parameters = P;

    fn init_constant_length(input_size: usize, personalization: Option<&[Self::Data]>) -> Self {
        Self::_init(
            Some(input_size),
            input_size % P::R == 0, // Not taken into account, can be any
            personalization,
        )
    }

    fn init_variable_length(mod_rate: bool, personalization: Option<&[Self::Data]>) -> Self {
        Self::_init(None, mod_rate, personalization)
    }

    fn update(&mut self, input: Self::Data) -> &mut Self {
        self.pending.push(input);
        self.updates_ctr += 1;
        self.apply_permutation_if_needed();
        self
    }

    fn finalize(&self) -> Result<Self::Data, Error> {
        let error_condition =

            // Constant input length instance, but the size of the input is different from the declared one
            (self.input_size.is_some() && self.updates_ctr != self.input_size.unwrap())

            ||

            // Variable modulus rate input length instance, but the size of the input is not modulus rate
            (self.input_size.is_none() && self.mod_rate && self.updates_ctr % P::R != 0);

        // If one of the conditions above is true, we must throw an error
        if error_condition {
            Err(Box::new(CryptoError::HashingError(
                "attempt to finalize with an input of invalid size".to_owned(),
            )))
        }
        // Otherwise pad if needed (according to the Self instance type) and return the hash output
        else {
            Ok(self.pad_and_finalize())
        }
    }

    fn reset(&mut self, personalization: Option<&[Self::Data]>) -> &mut Self {
        let new_instance = Self::_init(self.input_size, self.mod_rate, personalization);
        *self = new_instance;
        self
    }
}

#[cfg(test)]
mod test {
    use crate::crh::{
        test::{constant_length_field_based_hash_test, variable_length_field_based_hash_test},
        FieldBasedHash, SBox,
    };
    use crate::{FieldBasedHashParameters, PoseidonHash, PoseidonParameters};
    use algebra::PrimeField;

    fn generate_inputs<F: PrimeField>(num: usize) -> Vec<F> {
        let mut inputs = Vec::with_capacity(num);
        for i in 1..=num {
            let input = F::from(i as u32);
            inputs.push(input);
        }
        inputs
    }

    fn poseidon_permutation_regression_test<
        F: PrimeField,
        P: PoseidonParameters<Fr = F>,
        SB: SBox<Field = F, Parameters = P>,
    >(
        start_states: Vec<Vec<F>>,
        end_states: Vec<Vec<F>>,
    ) {
        // Regression test
        start_states
            .into_iter()
            .zip(end_states)
            .enumerate()
            .for_each(|(i, (mut start_state, end_state))| {
                PoseidonHash::<F, P, SB>::poseidon_perm(&mut start_state);
                assert_eq!(
                    start_state, end_state,
                    "Incorrect end state {}:\n Expected\n{:?}\n, Found\n {:?}\n",
                    i, start_state, end_state
                );
            });
    }

    fn test_routine<F: PrimeField, H: FieldBasedHash<Data = F>>(num_samples: usize) {
        let rate = <H::Parameters as FieldBasedHashParameters>::R;
        for i in 0..num_samples {
            let ins = generate_inputs::<F>(i + 1);

            // Constant length
            {
                let mut digest = H::init_constant_length(i + 1, None);

                constant_length_field_based_hash_test::<H>(&mut digest, ins.clone());
            }

            // Variable length
            {
                let mod_rate = (i + 1) % rate == 0;
                let mut digest = H::init_variable_length(mod_rate, None);

                variable_length_field_based_hash_test::<H>(&mut digest, ins.clone(), mod_rate);

                // Test also case in which mod_rate is false but the input happens to be mod rate
                if mod_rate {
                    let mut digest = H::init_variable_length(!mod_rate, None);
                    variable_length_field_based_hash_test::<H>(&mut digest, ins, !mod_rate);
                }
            }
        }
    }

    #[cfg(feature = "tweedle")]
    #[test]
    fn test_poseidon_hash_tweedle_fr() {
        use crate::crh::poseidon::parameters::tweedle_dee::{
            TweedleFrPoseidonHash, TweedleFrPoseidonParameters, TweedleFrQuinticSbox,
        };
        use algebra::{biginteger::BigInteger256, fields::tweedle::Fr as TweedleFr};
        use num_traits::Zero;

        // Test vectors are computed via the script in ./parameters/scripts/permutation_deefr.sage
        let start_states = vec![
            vec![TweedleFr::zero(); 3],
            vec![
                TweedleFr::new(BigInteger256([
                    0x2d9ced12b8448fa3,
                    0xe47617895bcb1def,
                    0xdb309341af8fc9bc,
                    0x3518ed3d596d9b3d,
                ])),
                TweedleFr::new(BigInteger256([
                    0x2f00b53bfb408372,
                    0x6de08091d9994983,
                    0x30787444ac8639a3,
                    0x18b1a8fe589e66ad,
                ])),
                TweedleFr::new(BigInteger256([
                    0xbbff40a91825c30d,
                    0xa82ca4dd45ed43cd,
                    0x3ce8daf6c9c21029,
                    0x10c0f7735f33aa7a,
                ])),
            ],
            vec![
                TweedleFr::new(BigInteger256([
                    0x5f37a0bd77589e1f,
                    0x5473621f06e318b0,
                    0x134c69d294364fc2,
                    0x17ce475fc0918e98,
                ])),
                TweedleFr::new(BigInteger256([
                    0xf997aedfd435a00c,
                    0xff8244711a05ace4,
                    0x111f3729665dfce3,
                    0x12e06c5d75a20f44,
                ])),
                TweedleFr::new(BigInteger256([
                    0x4fe219488f716f3b,
                    0x47994803d7aa1b4b,
                    0x83c0b9401250e3df,
                    0xc55e3e5129040af,
                ])),
            ],
            vec![
                TweedleFr::new(BigInteger256([
                    0x1c88b7f17d83e522,
                    0x63bbb3d972a8a79,
                    0x3cd3b269e9148e61,
                    0x107064754c2219f6,
                ])),
                TweedleFr::new(BigInteger256([
                    0xd98347c19ef61123,
                    0x8c2f919a2ce03104,
                    0x19a6ebeb17c8d50b,
                    0x211359dab98e662b,
                ])),
                TweedleFr::new(BigInteger256([
                    0x6fca9aeca36a6a90,
                    0x9a5901d4db4cb38b,
                    0xb7a625b6fa9c1d25,
                    0x1c0c5a9e4863c446,
                ])),
            ],
            vec![
                TweedleFr::new(BigInteger256([
                    0x52cc4aa39d8838b8,
                    0x412ba25c63120ebb,
                    0x667515874f0074d6,
                    0x1d2f166897ea99e,
                ])),
                TweedleFr::new(BigInteger256([
                    0x466265a678233c51,
                    0xd6b41807e24ee39f,
                    0xee5874453e9c291c,
                    0x1b0bbd1b8e79ea9d,
                ])),
                TweedleFr::new(BigInteger256([
                    0x49d2b1885d136bf6,
                    0xfebba4a8e8c0595b,
                    0xa5b4ca600f485e66,
                    0x27c2b78d22e855c0,
                ])),
            ],
        ];

        let end_states = vec![
            vec![
                TweedleFr::new(BigInteger256([
                    0x85614442a60ac11a,
                    0x55a43ca8180d2e08,
                    0x43f61ff197080ac4,
                    0x19d87eb89a42aaf1,
                ])),
                TweedleFr::new(BigInteger256([
                    0xa2f6b5a9a16d3790,
                    0xc947563b131a126c,
                    0x52c19607bb4b6640,
                    0xc4604a460df1c57,
                ])),
                TweedleFr::new(BigInteger256([
                    0x7d8f3c1679a9cbe2,
                    0xb09fdc38ee15fe77,
                    0x810720bf23be8578,
                    0x2ab876d1a0abfa95,
                ])),
            ],
            vec![
                TweedleFr::new(BigInteger256([
                    0xc4a37b8664180077,
                    0xd8390d652933725e,
                    0xaafa5d29eb656edb,
                    0x296682761320f48c,
                ])),
                TweedleFr::new(BigInteger256([
                    0x2fffbed47e729020,
                    0x6d243b1d399f42dd,
                    0x2bcea2d0461856d7,
                    0x2fc6f9c7c62a5088,
                ])),
                TweedleFr::new(BigInteger256([
                    0x8b617097039cbf5f,
                    0xc3e9594e65f53809,
                    0x96f163d2a6e08e55,
                    0x1283bbfbfafe0185,
                ])),
            ],
            vec![
                TweedleFr::new(BigInteger256([
                    0xb0e21925172f0ba3,
                    0x22bb8d3720914af7,
                    0x31ee2b9a26424619,
                    0x2184d5590df49e25,
                ])),
                TweedleFr::new(BigInteger256([
                    0x4f525fe270112fb8,
                    0x59d975c2bc66f456,
                    0x1740475c80005233,
                    0x3f44acd2d334fee9,
                ])),
                TweedleFr::new(BigInteger256([
                    0xda02921fa73b4778,
                    0xb9b7c2742272dbeb,
                    0xb3491dacb990965c,
                    0x3cffd4206f4264e,
                ])),
            ],
            vec![
                TweedleFr::new(BigInteger256([
                    0x9a5d804c8f8980d7,
                    0x60f4ba8f01fccce4,
                    0x95428b68f3a9eba3,
                    0x3108ed7e0636e1e7,
                ])),
                TweedleFr::new(BigInteger256([
                    0xf5e24f59c7e404d7,
                    0xf4a10531d95222b1,
                    0xb55cfa77a621836f,
                    0x15f7c485bf9b2bf1,
                ])),
                TweedleFr::new(BigInteger256([
                    0xf65bd157052e1b45,
                    0x180aa5b7e51b8a46,
                    0xe451d510b5cf9dae,
                    0x7cdd9f00493bc73,
                ])),
            ],
            vec![
                TweedleFr::new(BigInteger256([
                    0x7c080f4b62e78aab,
                    0xc6294e279a622677,
                    0xcabd73efb2584d6d,
                    0x10186a71cc08159e,
                ])),
                TweedleFr::new(BigInteger256([
                    0xdb3d4f4a63e1324d,
                    0x6705ae25ff9b471f,
                    0xccae1d131341f589,
                    0x1b31cd963165eccc,
                ])),
                TweedleFr::new(BigInteger256([
                    0x9860019e6edc3f2f,
                    0x14ca7a30bb1a5c36,
                    0xf4e9f4abe3f7ef0c,
                    0x143d7bf07e7f54c7,
                ])),
            ],
        ];

        poseidon_permutation_regression_test::<
            TweedleFr,
            TweedleFrPoseidonParameters,
            TweedleFrQuinticSbox,
        >(start_states, end_states);
        test_routine::<TweedleFr, TweedleFrPoseidonHash>(3)
    }

    #[cfg(feature = "tweedle")]
    #[test]
    fn test_poseidon_hash_tweedle_fq() {
        use crate::crh::poseidon::parameters::tweedle_dum::{
            TweedleFqPoseidonHash, TweedleFqPoseidonParameters, TweedleFqQuinticSbox,
        };
        use algebra::{biginteger::BigInteger256, fields::tweedle::Fq as TweedleFq};
        use num_traits::Zero;

        // Test vectors are computed via the script in ./parameters/scripts/permutation_dumfr.sage
        let start_states = vec![
            vec![TweedleFq::zero(); 3],
            vec![
                TweedleFq::new(BigInteger256([
                    0x530261dfc524611d,
                    0xebde2e5e0c454577,
                    0x31c9a2fd3288dbd8,
                    0x22faf97cf0bfa8ed,
                ])),
                TweedleFq::new(BigInteger256([
                    0x25f47e32d936f0c0,
                    0x9c88b0ffb8d56acc,
                    0x3c1a4050825c76ac,
                    0xf81aaaddfb679df,
                ])),
                TweedleFq::new(BigInteger256([
                    0x129cb322f4812820,
                    0x5b218d2750d9cc33,
                    0x5baa3f8af95e185b,
                    0xf5713c92c9b59a5,
                ])),
            ],
            vec![
                TweedleFq::new(BigInteger256([
                    0x8c70fb5700e28179,
                    0x58d04dff4aeb7baa,
                    0x7d229f69585bbc4c,
                    0x1a53f352bbb741f,
                ])),
                TweedleFq::new(BigInteger256([
                    0x983971f4bc40e955,
                    0xf9c4aa245dc69370,
                    0xc90afb10e865d7fa,
                    0x25c68f3eda91e782,
                ])),
                TweedleFq::new(BigInteger256([
                    0x553902e820896d7e,
                    0xea7238f532c5b890,
                    0x66c31bc5cacadbb5,
                    0x11fbf51d7acd7811,
                ])),
            ],
            vec![
                TweedleFq::new(BigInteger256([
                    0x8c5101f47ede0f2b,
                    0xdde609c8ee90d5e9,
                    0xf53611e4c9658d0b,
                    0x9b8ad64dd287d37,
                ])),
                TweedleFq::new(BigInteger256([
                    0xe79daeebc658d0a,
                    0x3019b7ed8cae3dd8,
                    0xe4966f5f01879f27,
                    0x2f1328f79025e70c,
                ])),
                TweedleFq::new(BigInteger256([
                    0x49ad0534394806ae,
                    0x6ab073974f741a93,
                    0x3e043b146513dfe5,
                    0x29b158cd24e843e4,
                ])),
            ],
            vec![
                TweedleFq::new(BigInteger256([
                    0x3a410990938e76ed,
                    0x4bd4f247c6c2215b,
                    0xe815c6d61abfe6f9,
                    0x94daa5bcfb9eb6f,
                ])),
                TweedleFq::new(BigInteger256([
                    0x3787fbb0c8dcfe1a,
                    0xf67406e5daf43fae,
                    0x7a5fc8f335f28767,
                    0x18ff0f241943eec8,
                ])),
                TweedleFq::new(BigInteger256([
                    0xc72a940881085fd6,
                    0x7096ba03e87353af,
                    0x32decb002f5a4e83,
                    0x492cc5ac858b06a,
                ])),
            ],
        ];

        let end_states = vec![
            vec![
                TweedleFq::new(BigInteger256([
                    0x46ef7b471f039f54,
                    0x7516283cc67869f2,
                    0x561a6334ba7a39f1,
                    0x293842a1538ac01b,
                ])),
                TweedleFq::new(BigInteger256([
                    0x6f10ff3b97995e3b,
                    0x7650f70901d51a88,
                    0x9f13555ea4caf2eb,
                    0x14ed7f5560a0a1e1,
                ])),
                TweedleFq::new(BigInteger256([
                    0x815126351fe00f44,
                    0x921a5f3ad5a6e83c,
                    0x5f614c0b1bdaf5f7,
                    0x7733c69a8892f0e,
                ])),
            ],
            vec![
                TweedleFq::new(BigInteger256([
                    0xf39ca6429f499eb1,
                    0x69657c642b509baa,
                    0xbb0a2f6bb3a44a7b,
                    0x1b0f054ee6b06ee5,
                ])),
                TweedleFq::new(BigInteger256([
                    0x9eab499dc61a7d92,
                    0x457d1a9027e66bd4,
                    0x74f80311cef652a5,
                    0x2f0dc832cc821ed,
                ])),
                TweedleFq::new(BigInteger256([
                    0xe5949837b34cdd97,
                    0x2fdd08e41ac8e36f,
                    0xbfcb6768fbb981d,
                    0x1521b70d21fc43fb,
                ])),
            ],
            vec![
                TweedleFq::new(BigInteger256([
                    0x21fb36a475c20033,
                    0x6a938adf93ceda77,
                    0xa05bc36806e89296,
                    0x1cd7a0d468136dd3,
                ])),
                TweedleFq::new(BigInteger256([
                    0x6295c60c77022ca5,
                    0x440a39652987ef94,
                    0xbe9a8f921e81b656,
                    0x3ade3ff16b820c56,
                ])),
                TweedleFq::new(BigInteger256([
                    0x62f4df55b1158a3d,
                    0x6787fff1b51e08ed,
                    0x47b46cd1709e9d30,
                    0x3c4bbad805b5838c,
                ])),
            ],
            vec![
                TweedleFq::new(BigInteger256([
                    0xf0b39ffa74b62183,
                    0x9c87a4fea04e092a,
                    0xe7ef4462efcf6492,
                    0x1495692d563b0275,
                ])),
                TweedleFq::new(BigInteger256([
                    0x1758eeffd0793b03,
                    0x37e1f13b2b104aa,
                    0x71c181dd5d62c9d,
                    0x3448bf7ebad19d00,
                ])),
                TweedleFq::new(BigInteger256([
                    0x63feeddf9fd791f,
                    0xcf11513a74efebf6,
                    0xc046e6ff5b45f4af,
                    0x13a773bcdaabf9b1,
                ])),
            ],
            vec![
                TweedleFq::new(BigInteger256([
                    0x6f2ad1eed8b08a65,
                    0x23e051559fea114f,
                    0x6e9855acf367f614,
                    0x1f6ff3e5034d9adb,
                ])),
                TweedleFq::new(BigInteger256([
                    0xc76c27513034009f,
                    0xf08aae84a5bdaf00,
                    0xb4614eed8e6839d5,
                    0x18b4587f29cdb052,
                ])),
                TweedleFq::new(BigInteger256([
                    0xa5a9c19386d171db,
                    0x57321c0b6d91fa65,
                    0xaa19cb2f60d37e5b,
                    0x12a05d4caaa7d0ca,
                ])),
            ],
        ];

        poseidon_permutation_regression_test::<
            TweedleFq,
            TweedleFqPoseidonParameters,
            TweedleFqQuinticSbox,
        >(start_states, end_states);
        test_routine::<TweedleFq, TweedleFqPoseidonHash>(3)
    }
}
