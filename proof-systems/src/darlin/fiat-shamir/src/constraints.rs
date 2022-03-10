use algebra::PrimeField;
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use r1cs_std::{to_field_gadget_vec::ToConstraintFieldGadget, fields::fp::FpGadget, boolean::Boolean};

/// the trait for Fiat-Shamir RNG Gadget
pub trait FiatShamirRngGadget<ConstraintF: PrimeField>:
    Sized
    + Clone
{
    /// initialize an empty transcript
    fn init<CS: ConstraintSystemAbstract<ConstraintF>>(cs: CS) -> Result<Self, SynthesisError>;

    /// initialize from a seed
    fn init_from_seed<CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        seed: Vec<u8>
    ) -> Result<Self, SynthesisError>;

    /// take in field elements
    fn enforce_record<CS, RG>(
        &mut self,
        cs: CS,
        data: RG
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystemAbstract<ConstraintF>,
        RG: ToConstraintFieldGadget<ConstraintF, FieldGadget = FpGadget<ConstraintF>>;

    /// Output a single N bits challenge
    fn enforce_get_challenge<CS: ConstraintSystemAbstract<ConstraintF>, const N: usize>(
        &mut self,
        cs: CS,
    ) -> Result<[Boolean; N], SynthesisError>;

    /// Output N bits challenges
    fn enforce_get_many_challenges<CS: ConstraintSystemAbstract<ConstraintF>, const N: usize>(
        &mut self,
        mut cs: CS,
        num: usize
    ) -> Result<Vec<[Boolean; N]>, SynthesisError> {
        (0..num)
            .map(|i| self
                .enforce_get_challenge(
                    cs.ns(|| format!("get challenge {}", i)
                )
            )
        ).collect()
    }

    fn reset<CS: ConstraintSystemAbstract<ConstraintF>>(
        &mut self,
        cs: CS
    ) -> Result<(), SynthesisError> {
        *self = Self::init(cs)?;
        Ok(())
    }
}

#[cfg(test)]
pub(crate) mod test {
    use r1cs_std::uint8::UInt8;
    use r1cs_std::fields::nonnative::nonnative_field_gadget::NonNativeFieldGadget;
    use r1cs_std::fields::fp::FpGadget;
    use r1cs_std::alloc::AllocGadget;
    use r1cs_core::{ConstraintSystem, ConstraintSystemDebugger, SynthesisMode};
    use rand::{Rng, RngCore};
    use crate::FiatShamirRng;
    use super::*;
    use algebra::{UniformRand, Group};

    pub(crate) fn test_native_result<
        G:   Group,
        FS:  FiatShamirRng,
        FSG: FiatShamirRngGadget<G::BaseField>,
        R: RngCore,
        const N: usize,
    >(
        rng: &mut R,
        num_inputs: usize,
        initial_seed: Option<Vec<u8>>
    )
    {
        // Generate test data
        let native_inputs: Vec<G::BaseField> = (0..num_inputs).map(|_| G::BaseField::rand(rng)).collect();
        let nonnative_inputs: Vec<G::ScalarField> = (0..num_inputs).map(|_| G::ScalarField::rand(rng)).collect();
        let byte_inputs: Vec<u8> = (0..num_inputs * 10).map(|_| rng.gen()).collect();

        let mut cs = ConstraintSystem::<G::BaseField>::new(SynthesisMode::Debug);

        // Alloc data
        let native_inputs_g = native_inputs
            .iter()
            .enumerate()
            .map(|(i, fe)| 
                FpGadget::<G::BaseField>::alloc(
                    cs.ns(|| format!("alloc native input {}", i)),
                    || Ok(fe)
                ).unwrap()
            ).collect::<Vec<_>>();

        let nonnative_inputs_g = nonnative_inputs
            .iter()
            .enumerate()
            .map(|(i, fe)| 
                NonNativeFieldGadget::<G::ScalarField, G::BaseField>::alloc(
                    cs.ns(|| format!("alloc nonnative input {}", i)),
                    || Ok(fe)
                ).unwrap()
            ).collect::<Vec<_>>();

        let byte_inputs_g = byte_inputs
        .iter()
        .enumerate()
        .map(|(i, fe)| 
            UInt8::alloc(
                cs.ns(|| format!("alloc byte input {}", i)),
                || Ok(fe)
            ).unwrap()
        ).collect::<Vec<_>>();

        // Test Non Native inputs

        // Create a primitive FS rng and record nonnative inputs
        let mut fs_rng = if let Some(seed) = initial_seed.clone() {
            FS::from_seed(seed).unwrap()
        } else {
            FS::default()
        };
        fs_rng.record(nonnative_inputs).unwrap();

        // Create a circuit FS rng and record nonnative inputs
        let mut fs_rng_g = if let Some(seed) = initial_seed.clone() {
            FSG::init_from_seed(cs.ns(|| "new fs_rng_g from seed for non native inputs"), seed).unwrap()
        } else {
            FSG::init(cs.ns(|| "new fs_rng_g for non native inputs")).unwrap()
        };
        fs_rng_g.enforce_record(cs.ns(|| "enforce record non native field elements"), nonnative_inputs_g.as_slice()).unwrap();

        // Get challenge from primitive and circuit FS rng and assert equality
        assert_eq!(
            fs_rng
                .get_challenge::<N>()
                .unwrap()
                .to_vec()
            ,
            fs_rng_g.enforce_get_many_challenges::<_, N>(
                cs.ns(|| "Get N bits challenges given non native record"), 1
            )
                .unwrap()[0]
                .iter()
                .map(|bit_g| bit_g.get_value().unwrap())
                .collect::<Vec<_>>()
        );

        // Test Native inputs

        // Create a primitive FS rng and record native inputs
        let mut fs_rng = if let Some(seed) = initial_seed.clone() {
            FS::from_seed(seed).unwrap()
        } else {
            FS::default()
        };
        fs_rng.record(native_inputs).unwrap();   

        // Create a circuit FS rng and record native inputs
        let mut fs_rng_g = if let Some(seed) = initial_seed.clone() {
            FSG::init_from_seed(cs.ns(|| "new fs_rng_g from seed for native inputs"), seed).unwrap()
        } else {
            FSG::init(cs.ns(|| "new fs_rng_g for native inputs")).unwrap()
        };
        fs_rng_g.enforce_record(cs.ns(|| "enforce record native field elements"), native_inputs_g).unwrap();

        // Get challenge from primitive and circuit FS rng and assert equality
        assert_eq!(
            fs_rng
                .get_challenge::<N>()
                .unwrap()
                .to_vec()
            ,
            fs_rng_g.enforce_get_many_challenges::<_, N>(
                cs.ns(|| "Get N bits challenges given native record"), 1
            )
                .unwrap()[0]
                .iter()
                .map(|bit_g| bit_g.get_value().unwrap())
                .collect::<Vec<_>>()
        );

        // Test byte inputs

        // Create a primitive FS rng and record byte inputs
        let mut fs_rng = if let Some(seed) = initial_seed.clone() {
            FS::from_seed(seed).unwrap()
        } else {
            FS::default()
        };
        fs_rng.record::<G::BaseField, _>(byte_inputs.as_slice()).unwrap();

        // Create a circuit FS rng and record byte inputs
        let mut fs_rng_g = if let Some(seed) = initial_seed {
            FSG::init_from_seed(cs.ns(|| "new fs_rng_g from seed for byte inputs"), seed).unwrap()
        } else {
            FSG::init(cs.ns(|| "new fs_rng_g for byte inputs")).unwrap()
        };
        fs_rng_g.enforce_record(cs.ns(|| "enforce record byte elements"), byte_inputs_g.as_slice()).unwrap();

        // Get challenges from primitive and circuit FS rng and assert equality
        assert_eq!(
            fs_rng
                .get_challenge::<N>()
                .unwrap()
                .to_vec()
            ,
            fs_rng_g.enforce_get_many_challenges::<_, N>(
                cs.ns(|| "Get N bits challenges given byte record"), 1
            )
                .unwrap()[0]
                .iter()
                .map(|bit_g| bit_g.get_value().unwrap())
                .collect::<Vec<_>>()
        );

        if !cs.is_satisfied(){
            println!("{:?}", cs.which_is_unsatisfied());
        }

        assert!(cs.is_satisfied());
    }

    pub(crate) fn fs_rng_consistency_test<
        G: Group,
        FSG: FiatShamirRngGadget<G::BaseField>,
        R: RngCore,
        const N: usize,
    >(rng: &mut R)
    {
        let mut cs = ConstraintSystem::<G::BaseField>::new(SynthesisMode::Debug);
        let mut fs_rng = FSG::init(cs.ns(|| "init fs_rng_g")).unwrap();
    
        // record random native field elements and check everything is fine
        let to_record = (0..10).map(|i| {
            let random_fe = G::BaseField::rand(rng);
            FpGadget::<G::BaseField>::alloc(
                cs.ns(|| format!("alloc native fe {}", i)),
                || Ok(random_fe)
            ).unwrap()
        }).collect::<Vec<_>>();
        fs_rng.enforce_record(cs.ns(|| "record native"), to_record).unwrap();
    
        // record random non native field elements and check everything is fine
        let to_record = (0..10).map(|i| {
            let random_nonnative_fe = G::ScalarField::rand(rng);
            NonNativeFieldGadget::<G::ScalarField, G::BaseField>::alloc(
                cs.ns(|| format!("alloc non native fe {}", i)),
                || Ok(random_nonnative_fe)
            ).unwrap()
        }).collect::<Vec<_>>();
        fs_rng.enforce_record(cs.ns(|| "record non native"), to_record.as_slice()).unwrap();
    
        // record random bytes and check everything is fine
        let to_record = (0..100).map(|i| {
            let random_byte: u8 = rng.gen();
            UInt8::alloc(
                cs.ns(|| format!("Alloc random byte {}", i)),
                || Ok(random_byte)
            ).unwrap()
        }).collect::<Vec<UInt8>>();
        fs_rng.enforce_record(cs.ns(|| "record bytes"), to_record.as_slice()).unwrap();
    
        // Check that calling get_challenge::<N>() multiple times without recording
        // changes the output
        let out = fs_rng.enforce_get_challenge::<_, N>(cs.ns(|| "test 1 - get init challenge")).unwrap();
        let mut prev = out;
        for i in 0..100 {
            let curr = fs_rng.enforce_get_challenge::<_, N>(
                cs.ns(|| format!("test 1 - get challenge {}", i))
            ).unwrap();
            assert!(prev != curr);
            prev = curr;
        }
    
        // Record field elements and check that get_challenge:
        // -  outputs the correct number of challenges all different from each other
        // -  outputs challenges different from the previous ones if more data has been recorded
        fs_rng.reset(cs.ns(|| " test 2 - initial reset")).unwrap();
        let mut set = std::collections::HashSet::new();

        let insert_chal_into_set = |chal: [Boolean; N], set: &mut std::collections::HashSet<Vec<bool>>| -> bool {
            set.insert(
                chal
                .iter()
                .map(|bit_g| {
                    bit_g.get_value().unwrap()
                })
                .collect::<Vec<bool>>()
            )
        };

        insert_chal_into_set(
            fs_rng
                .enforce_get_challenge::<_, N>(
                    cs.ns(|| "test 2 - get init challenge")
                )
                .unwrap()
            ,
            &mut set
        );

        let random_fes = (0..10).map(|i| {
            let random_fe = G::BaseField::rand(rng);
            FpGadget::<G::BaseField>::alloc(
                cs.ns(|| format!("test 2 - alloc init native fe {}", i)),
                || Ok(random_fe)
            ).unwrap()
        }).collect::<Vec<_>>();

        for i in 1..=10 {
            fs_rng.reset(cs.ns(|| format!("test 2 - reset {}", i))).unwrap();

            let random_fes = random_fes[..i].to_vec();
            fs_rng.enforce_record(
                cs.ns(|| format!("test 2 - enforce record {}", i)),
                random_fes
            ).unwrap();
    
            // Native get_many_challenges::<N> test
            let outs = fs_rng.enforce_get_many_challenges::<_, N>(
                cs.ns(|| format!("test 2 - enforce enforce_get_many_challenges {}", i)),
                i
            )
            .unwrap();

            // Bits shouldn't be all 0 with overwhelming probability
            outs
                .iter()
                .for_each(|out_bits| { assert!(!out_bits.iter().all(|bit_g| !bit_g.get_value().unwrap())); });

            // Bits shouldn't be all 1 with overwhelming probability
            outs
                .iter()
                .for_each(|out_bits| { assert!(!out_bits.iter().all(|&bit| bit.get_value().unwrap())); });

            // HashSet::insert(val) returns false if val was already present, so to check
            // that all the elements output by the fs_rng are different, we assert insert()
            // returning always true
            outs
                .into_iter()
                .for_each(|chal| assert!(insert_chal_into_set(chal, &mut set)));
        }

        if !cs.is_satisfied(){
            println!("{:?}", cs.which_is_unsatisfied());
        }

        assert!(cs.is_satisfied());
    }
}