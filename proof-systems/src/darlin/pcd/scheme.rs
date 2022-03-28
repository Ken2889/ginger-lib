use crate::darlin::pcd::{PCD, PCDCircuit, PCDNode, error::PCDError};
use algebra::{serialize::*, serialize, EndoMulCurve, Group, ToConstraintField};
use primitives::{crh::FieldBasedHash, merkle_tree::*};
use poly_commit::{
    PCKey, ipa_pc::CommitterKey as DLogCommitterKey
};
use std::{
    marker::PhantomData,
    collections::HashMap,
    convert::TryInto,
};
use digest::Digest;

pub const VK_TREE_HEIGHT: usize = 6;

/// Storage for verification keys of circuits defined on G.
/// Each vk must be associated to a specific String, which represents the
/// circuit through which has been produced a PCD of type String.
pub struct PCDVerificationKeyRing<G: EndoMulCurve, T: BatchFieldBasedMerkleTreeParameters<Data = G::BaseField>> {
    /// Stores, as leaves, hashes of the vks contained in vk_map.
    vk_tree: FieldBasedAppendOnlyMHT<T>,
    /// Stores vks and their index inside the tree.
    /// Each vk must be associated to a single String.
    vk_map: HashMap<String, (usize, Vec<u8>)>,
    _curve: PhantomData<G>
}

impl<G: EndoMulCurve, T: BatchFieldBasedMerkleTreeParameters<Data = G::BaseField>> PCDVerificationKeyRing<G, T> 
{
    fn init(tree_height: usize) -> Result<Self, PCDError> {
        let vk_tree = FieldBasedAppendOnlyMHT::<T>::init(tree_height, 1 << tree_height)
            .map_err(|e| PCDError::SchemeSetupError(format!("Unable to initialize vk_tree {:?}", e)))?;

        Ok(
            Self {
                vk_tree,
                vk_map: HashMap::new(),
                _curve: PhantomData
            }
        )
    }

    /// Stores a new vk `raw_vk" for the given `pcd_type`.
    /// Return PCDError if a vk was already associated to the given `pcd_type`.
    fn add_vk(
        &mut self,
        pcd_type: String,
        raw_vk: Vec<u8>
    ) -> Result<(), PCDError>
    {
        // Add vk to vk_tree

        // (Safely) convert vk to field elements
        let vk_as_fe: Vec<G::BaseField> = raw_vk
            .as_slice()
            .to_field_elements()
            .map_err(|e| PCDError::SchemeSetupError(format!("Unable to convert vk to fe: {:?}", e)))?;

        // Compute vk hash
        let vk_hash = {
            let mut digest = <T::H as FieldBasedHash>::init_variable_length(false, None);
            vk_as_fe
                .into_iter()
                .for_each(|fe| { digest.update(fe); });
            digest
                .finalize()
        }.map_err(|e| PCDError::SchemeSetupError(format!("Unable to compute vk hash: {:?}", e)))?;

        // Add to tree
        self
            .vk_tree
            .append(vk_hash)
            .map_err(|e| PCDError::SchemeSetupError(format!("Unable to add vk to merkle tree: {:?}", e)))?;

        // Add vk to the map
        let num_keys = self.vk_map.len();
        self
            .vk_map
            .insert(pcd_type.clone(), (num_keys, raw_vk.clone()))
            .ok_or(PCDError::SchemeSetupError(format!("Vk already defined for PCD type: {:?}", pcd_type)))?;

        Ok(())
    }

    /// Get the raw vk associated to `pcd_type`. Return PCDError if no vk was found.
    pub fn get_raw_vk(&self, pcd_type: String) -> Result<&Vec<u8>, PCDError> {
        let vk = self
            .vk_map
            .get(&pcd_type)
            .ok_or(PCDError::SchemeSetupError(format!("Unable to find vk for PCD type: {:?}", pcd_type)))?;

        Ok(&vk.1)
    }

    /// Get the vk associated to `pcd_type`. Return PCDError if no vk was found.
    pub fn get_vk<P: PCD>(&self, pcd_type: String) -> Result<&Vec<u8>, PCDError> {
        let vk = self
            .vk_map
            .get(&pcd_type)
            .ok_or(PCDError::SchemeSetupError(format!("Unable to find vk for PCD type: {:?}", pcd_type)))?;

        Ok(&vk.1)
    }

    /// Get the merkle path to the vk associated to `pcd_type`.
    /// Return PCDError if no vk was found or it has not been possible to retrieve vk path in the MerkleTree.
    pub fn get_vk_merkle_path(&self, pcd_type: String) -> Result<FieldBasedBinaryMHTPath<T>, PCDError> {
        let vk_leaf_index = self
            .vk_map
            .get(&pcd_type)
            .ok_or(PCDError::SchemeSetupError(format!("Unable to find vk for PCD type: {:?}", pcd_type)))?
            .0;

        let path = self
            .vk_tree
            .get_merkle_path(vk_leaf_index)
            .ok_or(PCDError::SchemeSetupError("Unable to get vk path".to_string()))?;

        Ok(
            path
                .try_into()
                .expect("A binary merkle tree shall be used !")
        )
    }

    /// Get the root of the MerkleTree of vks
    pub fn get_vk_tree_root(&self) -> Result<T::Data, PCDError> {
        let root = self
            .vk_tree
            .root()
            .ok_or(PCDError::SchemeSetupError("Unable to get vk tree root".to_string()))?;

        Ok(root)
    }
}

/// Provides the utilities to bootstrap the PCD scheme, e.g. generating and
/// storing the keys required to verify all the PCDs.
/// TODO: An alternative is making this more abstract, e.g. a trait with a setup()
///       function to be implemented
pub struct PCDScheme<G1, G2, T1, T2>
where
    G1: EndoMulCurve<BaseField = <G2 as Group>::ScalarField>
        + ToConstraintField<<G2 as Group>::ScalarField>,
    G2: EndoMulCurve<BaseField = <G1 as Group>::ScalarField>
        + ToConstraintField<<G1 as Group>::ScalarField>,
    T1: BatchFieldBasedMerkleTreeParameters<Data = G1::BaseField>,
    T2: BatchFieldBasedMerkleTreeParameters<Data = G2::BaseField>,
{
    committer_key_g1: DLogCommitterKey<G1>,
    committer_key_g2: DLogCommitterKey<G2>,
    vks_g1: PCDVerificationKeyRing<G1, T1>,
    vks_g2: PCDVerificationKeyRing<G2, T2>,
}

impl<G1, G2, T1, T2> PCDScheme<G1, G2, T1, T2> 
where
    G1: EndoMulCurve<BaseField = <G2 as Group>::ScalarField>
        + ToConstraintField<<G2 as Group>::ScalarField>,
    G2: EndoMulCurve<BaseField = <G1 as Group>::ScalarField>
        + ToConstraintField<<G1 as Group>::ScalarField>,
    T1: BatchFieldBasedMerkleTreeParameters<Data = G1::BaseField>,
    T2: BatchFieldBasedMerkleTreeParameters<Data = G2::BaseField>,
{
    /// Initialize the PCDScheme with the parameters required to generate
    /// the PCDVerificationKeyRing
    pub fn init(
        segment_size: usize,
        num_circuits: usize,
        ck_g1: &DLogCommitterKey<G1>,
        ck_g2: &DLogCommitterKey<G2>
    ) -> Result<Self, PCDError> 
    {
        let proof_tree_height = algebra::log2(num_circuits) as usize;
        Ok(
            Self {
                committer_key_g1: ck_g1
                    .trim(segment_size - 1)
                    .map_err(|e| PCDError::SchemeSetupError(e.to_string()))?,
                committer_key_g2: ck_g2
                    .trim(segment_size - 1)
                    .map_err(|e| PCDError::SchemeSetupError(e.to_string()))?,
                vks_g1: PCDVerificationKeyRing::<G1, T1>::init(proof_tree_height)?,
                vks_g2: PCDVerificationKeyRing::<G2, T2>::init(proof_tree_height)?,
            }
        )
    }

    /// Add a new verification key to the PCD scheme.
    /// The vk is the one associated to the circuit P::Circuit used by P to produce a new PCD of type P::OutputPCD
    /// and that will be used, by another PCDNode P1 (s.t. P1::InputPCD == P::OutputPCD),
    /// to verify it.
    pub fn add_vk_g1<
        P: PCDNode<G1, G2>,
        D: Digest,
    >
    (
        &mut self,
        config: <P::Circuit as PCDCircuit<G1>>::SetupData,
    )  -> Result<&mut Self, PCDError>
    {
        let vk = P::index::<D>(&self.committer_key_g1, config)
            .map_err(|e| PCDError::SchemeSetupError(e.to_string()))?;

        let raw_vk = serialize!(vk)
            .map_err(|e| PCDError::SchemeSetupError(e.to_string()))?;

        self
            .vks_g1
            .add_vk(<P::OutputPCD as PCD>::get_id(), raw_vk)?;

        Ok(self)
    }

    /// Add a new verification key to the PCD scheme.
    /// The vk is the one associated to the circuit P::Circuit used by P to produce a new PCD of type P::OutputPCD
    /// and that will be used, by another PCDNode P1 (s.t. P1::InputPCD == P::OutputPCD),
    /// to verify it.
    pub fn add_vk_g2<
        C: PCDCircuit<G2>,
        P: PCDNode<G2, G1>,
        D: Digest,
    >
    (
        &mut self,
        config: <P::Circuit as PCDCircuit<G2>>::SetupData,
    )  -> Result<&mut Self, PCDError>
    {
        let vk = P::index::<D>(&self.committer_key_g2, config)
            .map_err(|e| PCDError::SchemeSetupError(e.to_string()))?;

        let raw_vk = serialize!(vk)
            .map_err(|e| PCDError::SchemeSetupError(e.to_string()))?;

        self
            .vks_g2
            .add_vk(<P::OutputPCD as PCD>::get_id(), raw_vk)?;

        Ok(self)
    }

    /// Return the key rings in both curves, consuming `self`.
    pub fn finalize(self) -> (PCDVerificationKeyRing<G1, T1>, PCDVerificationKeyRing<G2, T2>) {
        (self.vks_g1, self.vks_g2)
    }
}