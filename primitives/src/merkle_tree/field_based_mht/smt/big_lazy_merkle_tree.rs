use crate::{
    crh::{BatchFieldBasedHash, FieldBasedHash, FieldBasedHashParameters},
    merkle_tree::{
        field_based_mht::{
            check_precomputed_parameters, BatchFieldBasedMerkleTreeParameters,
            FieldBasedBinaryMHTPath, FieldBasedMerkleTreePath, OperationLeaf,
        },
        MerkleTreeError,
    },
    ActionLeaf, Error, FieldBasedMerkleTree, FieldBasedSparseMerkleTree,
};

use std::collections::{HashMap, HashSet};

/// An in-memory, sparse, Merkle Tree with lazy leaves evaluation.
/// "Lazy" means that leaves are inserted/removed in batch, and the nodes
/// and root computation is triggered only by explicit calls to finalize()
/// and finalize_in_place().
#[derive(Derivative)]
#[derivative(Clone(bound = ""), Debug(bound = ""))]
pub struct FieldBasedSparseMHT<T: BatchFieldBasedMerkleTreeParameters> {
    /// the height of this tree
    pub(crate) height: u8,
    /// number of leaves
    pub(crate) width: u32,
    /// stores the non-empty leaves of the tree, along with a bool
    /// indicating if they have been updated since the previous
    /// root computation or not.
    /// We don't save the empty leaves, that's why we use a Map,
    /// but the leaves are still identified uniquely by their
    /// index (otherwise we would've need to store an additional
    /// byte to specify its height).
    pub(crate) leaves: HashMap<u32, (T::Data, bool)>,
    /// stores the non-empty nodes of the tree.
    /// We don't save the empty nodes, that's why we use a Map,
    /// but the nodes are still identified uniquely by their
    /// index (otherwise we would've need to store an additional
    /// byte to specify its height).
    pub(crate) nodes: HashMap<u32, T::Data>,
    /// stores the root of the tree as well as a boolean indicating
    /// if the tree has been modified since the last root computation,
    /// thus the root must be recomputed, or not, so it can be immediately
    /// returned.
    pub(crate) root: (T::Data, bool),
}

impl<T: BatchFieldBasedMerkleTreeParameters> FieldBasedSparseMHT<T> {
    /// Creates a new tree of specified `height`.
    pub fn init(height: u8) -> Self {
        assert!(check_precomputed_parameters::<T>(height as usize));

        let rate = <<T::H as FieldBasedHash>::Parameters as FieldBasedHashParameters>::R;

        assert_eq!(T::MERKLE_ARITY, 2); // For now we support only arity 2
                                        // Rate may also be smaller than the arity actually, but this assertion
                                        // is reasonable and simplify the design.
        assert_eq!(rate, T::MERKLE_ARITY);

        // If height is 0 it must not be possible to add any leaf, so we'll set width to 0.
        let width: u32 = if height != 0 {
            T::MERKLE_ARITY.pow(height as u32) as u32
        } else {
            0
        };

        Self {
            height,
            width,
            leaves: HashMap::new(),
            nodes: HashMap::new(),
            root: (T::ZERO_NODE_CST.unwrap().nodes[height as usize], false),
        }
    }

    /// Return true if there are uncommited changes in the tree (leaves added/removed but root not yet updated),
    /// false otherwise.
    fn pending_changes(&self) -> bool {
        self.root.1
    }

    /// Return true if leaf at 'idx' is empty, false otherwise.
    /// The tree doesn't need to be finalized before calling this function.
    pub fn is_leaf_empty(&self, idx: u32) -> Result<bool, Error> {
        // check that the index of the leaf is less than the width of the Merkle tree
        if idx >= self.width {
            return Err(MerkleTreeError::IncorrectLeafIndex(
                idx as usize,
                format!(
                    "Leaf index out of range. Max: {}, got: {}",
                    self.width - 1,
                    idx
                ),
            ))?;
        }

        let leaf = self.leaves.get(&idx);
        Ok(
            leaf.is_none() || leaf.unwrap().0 == T::ZERO_NODE_CST.unwrap().nodes[0], // Leaf waiting to be removed
        )
    }

    /// Return the last non empty leaf position of the tree.
    /// The tree doesn't need to be finalized before calling this function.
    fn get_last_non_empty_position(&self) -> u32 {
        assert!(!self.is_tree_empty());
        let mut last_idx = 0;
        self.leaves
            .iter()
            .filter(|(_, (data, _))| data != &T::ZERO_NODE_CST.unwrap().nodes[0])
            .for_each(|(idx, (_, _))| {
                if idx > &last_idx {
                    last_idx = *idx;
                }
            });

        last_idx
    }

    fn batch_hash(input: &[T::Data]) -> Vec<T::Data> {
        <T::BH as BatchFieldBasedHash>::batch_evaluate(input)
            .expect("Should be able to compute batch hash")
    }

    /// Return true if the tree is empty, false otherwise.
    /// Emptiness of the tree is checked by checking no leaf is present.
    /// The tree doesn't need to be finalized before calling this function
    pub fn is_tree_empty(&self) -> bool {
        debug_assert!(self.nodes.is_empty());
        self.leaves.is_empty()
            || self
                .leaves
                .iter()
                .all(|(_, (data, _))| data == &T::ZERO_NODE_CST.unwrap().nodes[0])
    }

    /// Get the node at the corresponding height and idx, and return its value and 'true' if it exists;
    /// otherwise return empty node and 'false'
    fn get_node_at_height_and_idx(&self, height: usize, idx: u32) -> (T::Data, bool) {
        if height == 0 {
            self.leaves.get(&idx).map_or_else(
                || (T::ZERO_NODE_CST.unwrap().nodes[height], false),
                |&(data, _)| {
                    debug_assert!(data != T::ZERO_NODE_CST.unwrap().nodes[0]);
                    (data, true)
                },
            )
        } else {
            self.nodes.get(&idx).map_or_else(
                || (T::ZERO_NODE_CST.unwrap().nodes[height], false),
                |&data| {
                    debug_assert!(data != T::ZERO_NODE_CST.unwrap().nodes[0]);
                    (data, true)
                },
            )
        }
    }

    /// Update the nodes and the root of the tree according to the changed leaves.
    fn process_leaves(&mut self) -> Result<T::Data, Error> {
        // Collect nodes to (re)compute for each level of the tree
        let mut nodes_to_recompute_by_level: Vec<HashSet<u32>> =
            Vec::with_capacity(self.height as usize);

        // Collect leaves in the first level
        let mut modified_leaves_pos = HashSet::<u32>::new();

        // Collect leaves to be removed from leaves Map
        let mut leaves_to_be_removed = Vec::new();

        self.leaves
            .iter_mut()
            .filter(|(_, (_, updated))| *updated)
            .for_each(|(idx, (data, updated))| {
                // Collect leaves whose value has changed since previous 'process_leaves' call, and set
                // their state to unchanged.
                modified_leaves_pos.insert(*idx);
                *updated = false;

                // We interpret removal as a leaf with updated state but value set to be empty node. For
                // such leaves, we need to actually remove them before proceeding in updating the tree.
                if data == &T::ZERO_NODE_CST.unwrap().nodes[0] {
                    leaves_to_be_removed.push(*idx);
                }
            });

        nodes_to_recompute_by_level.push(modified_leaves_pos);

        // Remove all leaves marked for removal
        leaves_to_be_removed.into_iter().for_each(|idx| {
            self.leaves.remove(&idx);
        });

        // We have taken all the leaves to be inserted and removed the ones supposed to be removed.
        // There shouldn't be any leaf with !updated stated and empty value
        debug_assert!(self
            .leaves
            .iter()
            .all(|(_, (data, updated))| !*updated && data != &T::ZERO_NODE_CST.unwrap().nodes[0]));

        // Find all the nodes that must be recomputed following the
        // additional/removal of leaves
        for height in 0..self.height as usize {
            // Keeps track (uniquely) of the nodes to be processed at the level above
            let mut visited_nodes: HashSet<u32> = HashSet::new();

            nodes_to_recompute_by_level[height]
                .iter()
                .for_each(|&child_idx| {
                    // Compute parent idx
                    let parent_idx = self.width + (child_idx / T::MERKLE_ARITY as u32);
                    visited_nodes.insert(parent_idx);
                });

            nodes_to_recompute_by_level.push(visited_nodes);
        }

        // Compute hashes of the affected nodes (ignoring leaf nodes)
        for height in 1..=self.height as usize {
            let mut input_vec = Vec::new(); // Leaves to be hashed
            let mut empty_node = Vec::new(); // Keep track of which node is empty

            // Collect leaves to be hashed in parallel
            nodes_to_recompute_by_level[height]
                .iter()
                .for_each(|&parent_idx| {
                    // Compute children coords and get corresponding values
                    let left_child_idx = (parent_idx - self.width) * T::MERKLE_ARITY as u32;
                    let right_child_idx = left_child_idx + 1;

                    let (left_hash, is_left_full) =
                        self.get_node_at_height_and_idx(height - 1, left_child_idx);
                    let (right_hash, is_right_full) =
                        self.get_node_at_height_and_idx(height - 1, right_child_idx);

                    let is_node_full = is_left_full || is_right_full;

                    // Must compute hash iff node will be non-empty, otherwise
                    // we have already its value precomputed
                    if is_node_full {
                        input_vec.push(left_hash);
                        input_vec.push(right_hash);
                    } else {
                        // If the node was present in self.nodes we must remove it,
                        // as it has become empty due to some leaf removal operation
                        self.nodes.remove(&parent_idx);
                    }

                    empty_node.push(!is_node_full);
                });

            // Process the input_vec of the nodes that will be non-empty
            // (i.e. the ones who have at least one non-empty children)
            // using batch Poseidon hash
            if !input_vec.is_empty() {
                let output_vec = Self::batch_hash(input_vec.as_slice());

                // Update the nodes map with the new values
                let mut output_vec_index = 0;
                for (&idx, is_empty) in nodes_to_recompute_by_level[height].iter().zip(empty_node) {
                    if !is_empty {
                        self.nodes.insert(idx, output_vec[output_vec_index]);
                        output_vec_index += 1;
                    }
                }
            }
        }

        // Update root
        let root_idx: u32 = (1 << (self.height + 1)) - 2;
        let new_root = self.nodes.get(&root_idx).map_or_else(
            || T::ZERO_NODE_CST.unwrap().nodes[self.height as usize], // If not in nodes, then the root is empty
            |&data| data,
        );

        self.root.0 = new_root;
        self.root.1 = false;
        Ok(new_root)
    }
}

impl<T: BatchFieldBasedMerkleTreeParameters> FieldBasedMerkleTree for FieldBasedSparseMHT<T> {
    type Position = u32;
    type Parameters = T;
    type MerklePath = FieldBasedBinaryMHTPath<T>;

    fn append(&mut self, leaf: T::Data) -> Result<&mut Self, Error> {
        // Cannot append in a tree of height 0
        if self.height == 0 {
            Err(MerkleTreeError::TooManyLeaves(0))?
        }

        // It doesn't really make sense to define an append operation in a SparseMerkleTree,
        // but let's interpret it as adding a single leaf in the last empty position.
        let last_pos = if !self.is_tree_empty() {
            let pos = self.get_last_non_empty_position();

            // If the last non empty position is the final one of the tree, we forbid "appending"
            if pos == self.width - 1 {
                Err(MerkleTreeError::TooManyLeaves(self.height as usize))?
            }

            pos + 1
        } else {
            0
        };

        // Insert leaves inside tree
        let mut leaves_to_insert = HashMap::new();
        leaves_to_insert.insert(last_pos, leaf);
        self.insert_leaves(leaves_to_insert)
    }

    fn finalize(&self) -> Result<Self, Error> {
        let mut copy = self.clone();
        if self.pending_changes() {
            copy.process_leaves()?;
        }
        Ok(copy)
    }

    /// Finalize in place allows to continue updating the tree
    fn finalize_in_place(&mut self) -> Result<&mut Self, Error> {
        if self.pending_changes() {
            self.process_leaves()?;
        }
        Ok(self)
    }

    fn reset(&mut self) -> &mut Self {
        self.leaves = HashMap::new();
        self.nodes = HashMap::new();
        self.root = (T::ZERO_NODE_CST.unwrap().nodes[self.height as usize], false);
        self
    }

    fn root(&self) -> Option<T::Data> {
        if self.pending_changes() {
            None
        } else {
            Some(self.root.0)
        }
    }

    fn get_merkle_path(&self, idx: u32) -> Option<Self::MerklePath> {
        // if root has changed then we cannot get valid merkle path until we finalize it
        if self.pending_changes() {
            eprintln!("Identified pending changes: unable to get path before pending changes are applied to the tree.");
            return None;
        }

        // check that the index of the leaf is less than the width of the Merkle tree
        if idx >= self.width {
            eprintln!(
                "Leaf index out of range. Max: {}, got: {}",
                self.width - 1,
                idx
            );
            return None;
        }

        let mut path = Vec::with_capacity(self.height as usize);
        let mut node_idx = idx;
        let mut height = 0usize;
        while height != self.height as usize {
            // Estabilish if sibling is a left or right child
            let (sibling_idx, direction) = if node_idx % T::MERKLE_ARITY as u32 == 0 {
                (node_idx + 1, false)
            } else {
                (node_idx - 1, true)
            };

            // Get its hash
            let (sibling, _) = self.get_node_at_height_and_idx(height, sibling_idx);

            // Push info to path
            path.push((sibling, direction));

            height += 1; // go up one level
            node_idx = self.width + (node_idx / T::MERKLE_ARITY as u32); // compute the index of the parent
        }
        debug_assert!(self.get_node_at_height_and_idx(height, node_idx).0 == self.root.0);

        Some(FieldBasedBinaryMHTPath::<T>::new(path))
    }

    fn height(&self) -> usize {
        self.height as usize
    }
}

impl<T: BatchFieldBasedMerkleTreeParameters> FieldBasedSparseMerkleTree for FieldBasedSparseMHT<T> {
    /// Perform insertion/removals of the leaves as specified by 'leaves_set'.
    /// This function will return Error in the following situations:
    /// - Invalid leaf idx (leaf.coord.position > self.width);
    /// - Remove a non existing leaf
    /// No guarantee is provided to the state of the tree in case the execution of this function
    /// terminates abruptly.
    fn update_leaves(
        &mut self,
        leaves: Vec<OperationLeaf<Self::Position, T::Data>>,
    ) -> Result<&mut Self, Error> {
        // Update internal leaves
        if !leaves.is_empty() {
            // Can't perform any leaf update operation in a tree of height 0.
            if self.height == 0 {
                return Err(MerkleTreeError::TooManyLeaves(0))?;
            }

            for leaf in leaves.into_iter() {
                let idx = leaf.position;

                // Check that the index of the leaf is less than the width of the Merkle tree
                if idx >= self.width {
                    return Err(MerkleTreeError::IncorrectLeafIndex(
                        idx as usize,
                        format!(
                            "Leaf index out of range. Max: {}, got: {}",
                            self.width - 1,
                            idx
                        ),
                    ))?;
                }

                // Forbid attempt to remove a non-existing leaf (or ones waiting for removal)
                let leaf_to_remove = self.leaves.get(&idx);
                if matches!(leaf.action, ActionLeaf::Remove)
                    && (leaf_to_remove.is_none()
                        || leaf_to_remove.unwrap().0 == T::ZERO_NODE_CST.unwrap().nodes[0])
                {
                    return Err(MerkleTreeError::IncorrectLeafIndex(
                        idx as usize,
                        format!("Leaf with index {} doesn't exist", idx),
                    ))?;
                }

                // For convenience, removal is performed by replacing the leaf value with the empty one, otherwise set it to the proper insertion value
                let val = if matches!(leaf.action, ActionLeaf::Remove) {
                    T::ZERO_NODE_CST.unwrap().nodes[0]
                } else {
                    leaf.hash.unwrap()
                };

                // Update leaves Map accordingly
                self.leaves.insert(idx, (val, true));
            }

            // Set root to be recomputed
            self.root.1 = true;
        }

        Ok(self)
    }
}

#[cfg(test)]
mod test {

    use std::collections::{BTreeMap, HashMap};

    use algebra::{Field, UniformRand};

    use crate::{
        merkle_tree::field_based_mht::{
            smt::FieldBasedSparseMHT, ActionLeaf, BatchFieldBasedMerkleTreeParameters,
            FieldBasedAppendOnlyMHT, FieldBasedBinaryMHTPath, FieldBasedMerkleTree,
            FieldBasedMerkleTreeParameters, FieldBasedMerkleTreePath,
            FieldBasedMerkleTreePrecomputedZeroConstants,
        },
        FieldBasedSparseMerkleTree, NaiveMerkleTree, OperationLeaf,
    };

    use rand::{prelude::SliceRandom, Rng, RngCore};

    const TEST_HEIGHT: u8 = 10;
    const NUM_SAMPLES: usize = 10;

    /// Return (in order) the non empty leaves of the tree.
    /// The tree doesn't need to be finalized before calling this function.
    /// Used mainly for testing purposes.
    fn get_non_empty_leaves<T: BatchFieldBasedMerkleTreeParameters>(
        smt: &FieldBasedSparseMHT<T>,
    ) -> BTreeMap<u32, T::Data> {
        let mut non_empty_leaves = BTreeMap::new();
        smt.leaves
            .iter()
            .filter(|(_, (data, _))| data != &T::ZERO_NODE_CST.unwrap().nodes[0])
            .for_each(|(&idx, (data, _))| {
                non_empty_leaves.insert(idx, *data);
            });
        non_empty_leaves
    }

    fn compute_append_only_tree_root<T: BatchFieldBasedMerkleTreeParameters>(
        smt: &FieldBasedSparseMHT<T>,
    ) -> T::Data {
        let mut optimized =
            FieldBasedAppendOnlyMHT::<T>::init(smt.height as usize, smt.width as usize).unwrap();
        let mut last_idx = 0;
        get_non_empty_leaves(smt).iter().for_each(|(&idx, leaf)| {
            for _ in last_idx..idx {
                optimized
                    .append(T::ZERO_NODE_CST.unwrap().nodes[0])
                    .unwrap();
            }
            optimized.append(*leaf).unwrap();
            last_idx = idx + 1;
        });
        optimized.finalize().unwrap().root().unwrap()
    }

    fn compare_append_only_and_smt_roots<T: BatchFieldBasedMerkleTreeParameters>(
        smt: &mut FieldBasedSparseMHT<T>,
    ) {
        // Insert into optimized and get root
        let optimized_root = compute_append_only_tree_root(smt);

        // Roots must be equal
        assert!(
            smt.root().is_none(),
            "Must be unable to get root if tree has not been finalized"
        );
        smt.finalize_in_place().unwrap();
        assert_eq!(smt.root().unwrap(), optimized_root, "Roots are not equal");
    }

    fn assert_tree_empty<T: BatchFieldBasedMerkleTreeParameters>(smt: &FieldBasedSparseMHT<T>) {
        // Tree must be finalized before calling this function
        assert!(!smt.pending_changes());

        // We must have an empty root...
        assert_eq!(
            smt.root().unwrap(),
            T::ZERO_NODE_CST.unwrap().nodes[smt.height as usize],
            "Root after removal of all leaves must be equal to empty root"
        );

        // ...and tree must be empty
        assert!(smt.is_tree_empty());

        // Additional sanity checks
        assert!(smt.leaves.is_empty());
        assert!(smt.nodes.is_empty());
    }

    /// Test correct behavior of the SMT (compared with respect to a FieldBasedAppendOnlyMHT) by processing batches
    /// of all leaves additions and all leaves removals.
    /// If 'adjacent_leaves' is enabled, the batches will be made up of leaves with subsequent indices;
    /// If 'finalize_in_the_end' is enabled, the "finalize_in_place()" function of FieldBasedSparseMHT
    /// will be called only after having appended/removed all the leaves
    fn test_batch_all_additions_removals<T: BatchFieldBasedMerkleTreeParameters, R: RngCore>(
        height: u8,
        rng: &mut R,
        adjacent_leaves: bool,
        finalize_in_the_end: bool,
    ) {
        // Initialize trees
        let mut smt = FieldBasedSparseMHT::<T>::init(height);
        let num_leaves = smt.width;

        // Initialize leaves
        let mut leaves = (0..num_leaves)
            .map(|idx| (idx, T::Data::rand(rng)))
            .collect::<Vec<_>>();

        if !adjacent_leaves {
            leaves.shuffle(rng);
        }

        // Test insertions
        let chunk_size = rng.gen_range(1..num_leaves + 1) as usize;
        leaves.chunks(chunk_size).for_each(|leaves| {
            // Insert all leaves into smt and get root
            let mut leaves_map = HashMap::new();
            leaves.iter().for_each(|(idx, data)| {
                leaves_map.insert(*idx, *data);
            });
            smt.insert_leaves(leaves_map).unwrap();

            if !finalize_in_the_end {
                compare_append_only_and_smt_roots(&mut smt)
            }
        });

        if finalize_in_the_end {
            compare_append_only_and_smt_roots(&mut smt)
        }

        // Leaves and Nodes map must be full
        assert_eq!(smt.leaves.len() as u32, num_leaves);
        assert_eq!(smt.nodes.len() as u32, num_leaves - 1);

        // Test removals
        // Remove all leaves and update smt
        leaves.chunks(chunk_size).for_each(|leaves_chunk| {
            // Remove leaves from smt and get root
            smt.remove_leaves(leaves_chunk.iter().map(|(idx, _)| *idx).collect())
                .unwrap();

            if !finalize_in_the_end {
                compare_append_only_and_smt_roots(&mut smt)
            }
        });

        if finalize_in_the_end {
            compare_append_only_and_smt_roots(&mut smt)
        }

        assert_tree_empty(&smt);
    }

    /// Test correct behavior of the SMT (compared with respect to a FieldBasedAppendOnlyMHT) by processing batches
    /// of leaves additions and removals, in mixed order.
    /// If 'finalize_in_the_end' is enabled, the "finalize_in_place()" function of FieldBasedSparseMHT
    /// will be called only after having appended/removed all the leaves
    fn test_batch_mixed_additions_removals<T: BatchFieldBasedMerkleTreeParameters, R: RngCore>(
        height: u8,
        rng: &mut R,
        finalize_in_the_end: bool,
    ) {
        // Initialize trees: fill half of the SMT
        let mut smt = FieldBasedSparseMHT::<T>::init(height);
        let num_leaves = smt.width;
        let mut leaves = (0..num_leaves / 2)
            .map(|idx| OperationLeaf::new(idx, ActionLeaf::Insert, Some(T::Data::rand(rng))))
            .collect::<Vec<_>>();
        smt.update_leaves(leaves.clone()).unwrap();

        // Test batches of mixed insertions/removals: fill the other half of the tree and remove the first half.

        // Remove previously inserted leaves
        leaves
            .iter_mut()
            .for_each(|leaf| (*leaf).action = ActionLeaf::Remove);

        // Fill the other half of the tree
        leaves.append(
            &mut (num_leaves / 2..num_leaves)
                .map(|idx| OperationLeaf::new(idx, ActionLeaf::Insert, Some(T::Data::rand(rng))))
                .collect::<Vec<_>>(),
        );

        // Mix the leaves
        leaves.shuffle(rng);

        // Test
        let chunk_size = rng.gen_range(1..num_leaves + 1) as usize;
        leaves.chunks(chunk_size).for_each(|leaves| {
            smt.update_leaves(leaves.to_vec()).unwrap();
            if !finalize_in_the_end {
                compare_append_only_and_smt_roots(&mut smt)
            }
        });

        if finalize_in_the_end {
            compare_append_only_and_smt_roots(&mut smt)
        }

        // Nodes map must be half full
        assert_eq!(smt.leaves.len() as u32, num_leaves / 2);
        assert_eq!(smt.nodes.len() as u32, num_leaves / 2);
    }

    fn test_error_cases<T: BatchFieldBasedMerkleTreeParameters>(height: u8) {
        // Initialize tree
        let mut smt = FieldBasedSparseMHT::<T>::init(height);

        let mut dummy_leaf = OperationLeaf::new(0, ActionLeaf::Remove, Some(T::Data::one()));

        // Remove leaf from an empty tree
        assert!(smt
            .update_leaves(vec![dummy_leaf])
            .unwrap_err()
            .to_string()
            .contains("Leaf with index 0 doesn't exist"));

        // Remove a leaf out of range
        dummy_leaf.position = smt.width;
        assert!(smt
            .update_leaves(vec![dummy_leaf])
            .unwrap_err()
            .to_string()
            .contains(
                format!(
                    "Leaf index out of range. Max: {}, got: {}",
                    smt.width - 1,
                    smt.width
                )
                .as_str()
            ));

        // Add a leaf out of range
        dummy_leaf.action = ActionLeaf::Insert;
        assert!(smt
            .update_leaves(vec![dummy_leaf])
            .unwrap_err()
            .to_string()
            .contains(
                format!(
                    "Leaf index out of range. Max: {}, got: {}",
                    smt.width - 1,
                    smt.width
                )
                .as_str()
            ));

        // Add a correct leaf
        dummy_leaf.position -= 1;
        smt.update_leaves(vec![dummy_leaf]).unwrap();
        smt.finalize_in_place().unwrap();
        let smt_root = smt.root().unwrap();
        assert_eq!(smt_root, compute_append_only_tree_root(&smt));
        assert_eq!(smt.leaves.len(), 1);
        assert_eq!(smt.nodes.len() as u8, height);

        // Replace previously added leaf with a new value and check correct replacement
        dummy_leaf.hash = Some(T::Data::from(2u8));
        smt.update_leaves(vec![dummy_leaf]).unwrap();
        let new_smt_root = smt.finalize_in_place().unwrap().root().unwrap();
        assert_ne!(new_smt_root, smt_root);
        assert_eq!(new_smt_root, compute_append_only_tree_root(&smt));
        assert_eq!(smt.leaves.len(), 1);
        assert_eq!(smt.nodes.len() as u8, height);

        // Perform removal then insertion of the same leaf at the same time and check correct result
        let mut dummy_leaf_removal = dummy_leaf.clone();
        dummy_leaf_removal.action = ActionLeaf::Remove;
        smt.update_leaves(vec![dummy_leaf_removal, dummy_leaf])
            .unwrap();

        // Situation must be unchanged with respect to before
        assert_eq!(
            new_smt_root,
            smt.finalize_in_place().unwrap().root().unwrap()
        );
        assert_eq!(smt.leaves.len(), 1);
        assert_eq!(smt.nodes.len() as u8, height);

        // Perform insertion then removal of the same leaf at the same time and check correct result
        let new_dummy_leaf = OperationLeaf::new(0, ActionLeaf::Insert, Some(T::Data::one()));
        let mut new_dummy_leaf_removal = new_dummy_leaf.clone();
        new_dummy_leaf_removal.action = ActionLeaf::Remove;
        smt.update_leaves(vec![new_dummy_leaf, new_dummy_leaf_removal])
            .unwrap();

        // Situation must be unchanged with respect to before
        assert_eq!(
            new_smt_root,
            smt.finalize_in_place().unwrap().root().unwrap()
        );
        assert_eq!(smt.leaves.len(), 1);
        assert_eq!(smt.nodes.len() as u8, height);

        // Remove non existing leaf with non empty tree
        dummy_leaf.position -= 1;
        dummy_leaf.action = ActionLeaf::Remove;
        assert!(smt
            .update_leaves(vec![dummy_leaf])
            .unwrap_err()
            .to_string()
            .contains(format!("Leaf with index {} doesn't exist", smt.width - 2).as_str()));

        // Remove leaf
        dummy_leaf.position += 1;
        dummy_leaf.action = ActionLeaf::Remove;
        smt.update_leaves(vec![dummy_leaf]).unwrap();

        // Remove same leaf as before: should be the same as trying to remove a non existing leaf
        assert!(smt
            .update_leaves(vec![dummy_leaf])
            .unwrap_err()
            .to_string()
            .contains(format!("Leaf with index {} doesn't exist", smt.width - 1).as_str()));

        // Tree must be empty now
        smt.finalize_in_place().unwrap();
        assert_tree_empty(&smt);
    }

    fn test_edge_cases<T: BatchFieldBasedMerkleTreeParameters>() {
        let dummy_leaf = OperationLeaf::new(0, ActionLeaf::Insert, Some(T::Data::one()));

        // HEIGHT > 1
        {
            // Generate empty tree and get the root
            let mut smt = FieldBasedSparseMHT::<T>::init(TEST_HEIGHT);
            let root = smt.root().unwrap();
            assert_eq!(root, T::ZERO_NODE_CST.unwrap().nodes[TEST_HEIGHT as usize]);

            // Get merkle path on an empty tree should work
            for i in 0..smt.width {
                let leaf = smt.get_node_at_height_and_idx(0, i).0;
                let path = smt.get_merkle_path(i).unwrap();
                assert!(path.verify(smt.height as usize, &leaf, &root).unwrap());
            }

            // Generate tree with only 1 leaf and attempt to get the root
            assert!(smt.update_leaves(vec![dummy_leaf]).is_ok());
            smt.finalize_in_place().unwrap();
            let new_root = smt.root().unwrap();
            assert_ne!(new_root, root);
            assert_ne!(
                new_root,
                T::ZERO_NODE_CST.unwrap().nodes[TEST_HEIGHT as usize]
            );
        }

        // HEIGHT == 1
        {
            // Generate empty tree and get the root
            let mut smt = FieldBasedSparseMHT::<T>::init(1);
            let mut root = smt.root().unwrap();
            assert_eq!(root, T::ZERO_NODE_CST.unwrap().nodes[1]);

            // Get merkle path on an empty tree should work
            for i in 0..smt.width {
                let leaf = smt.get_node_at_height_and_idx(0, i).0;
                let path = smt.get_merkle_path(i).unwrap();
                assert!(path.verify(smt.height as usize, &leaf, &root).unwrap());
            }

            // Generate tree with only 1 leaf and attempt to get the root
            assert!(smt.update_leaves(vec![dummy_leaf]).is_ok());
            smt.finalize_in_place().unwrap();
            let new_root = smt.root().unwrap();
            assert_ne!(new_root, root);
            assert_ne!(new_root, T::ZERO_NODE_CST.unwrap().nodes[1]);
            root = new_root;

            // Generate tree with exactly 2 leaves and attempt to get the root.
            // Assert error if trying to add another leaf
            assert!(smt
                .update_leaves(vec![OperationLeaf::new(
                    1,
                    ActionLeaf::Insert,
                    Some(T::Data::one())
                )])
                .is_ok());
            smt.finalize_in_place().unwrap();
            let new_root = smt.root().unwrap();
            assert_ne!(new_root, root);
            assert_ne!(new_root, T::ZERO_NODE_CST.unwrap().nodes[1]);

            assert!(smt
                .update_leaves(vec![OperationLeaf::new(
                    2,
                    ActionLeaf::Insert,
                    Some(T::Data::one())
                )])
                .is_err());
        }

        // HEIGHT == 0
        {
            // Generate empty tree and get the root
            let mut smt = FieldBasedSparseMHT::<T>::init(0);
            let root = smt.root().unwrap();
            assert_eq!(root, T::ZERO_NODE_CST.unwrap().nodes[0]);

            // Get merkle path on an empty tree should work
            for i in 0..smt.width {
                let leaf = smt.get_node_at_height_and_idx(0, i).0;
                let path = smt.get_merkle_path(i).unwrap();
                assert!(path.verify(smt.height as usize, &leaf, &root).unwrap());
            }

            // Generate tree with only 1 leaf and assert error
            assert!(smt
                .update_leaves(vec![dummy_leaf])
                .unwrap_err()
                .to_string()
                .contains("Reached maximum number of leaves for a tree of height 0"));
        }
    }

    fn test_merkle_path<T: BatchFieldBasedMerkleTreeParameters, R: RngCore>(
        height: u8,
        rng: &mut R,
    ) {
        use std::convert::TryInto;

        let mut smt = FieldBasedSparseMHT::<T>::init(height);
        let num_leaves = smt.width;
        let mut optimized =
            FieldBasedAppendOnlyMHT::<T>::init(smt.height as usize, num_leaves as usize).unwrap();
        let mut leaves_for_lazy_smt = Vec::with_capacity(num_leaves as usize);

        // Generate random leaves, half of which empty
        for i in 0..num_leaves / 2 {
            let leaf = T::Data::rand(rng);
            optimized.append(leaf).unwrap();
            leaves_for_lazy_smt.push(OperationLeaf::new(i, ActionLeaf::Insert, Some(leaf)));
        }
        optimized.finalize_in_place().unwrap();

        // Compute the root of the tree, and do the same for a FieldBasedAppendOnlyMHT, used here as reference
        smt.update_leaves(leaves_for_lazy_smt).unwrap();
        smt.finalize_in_place().unwrap();
        let optimized_root = optimized.root().unwrap();
        let root = smt.root().unwrap();
        assert_eq!(root, optimized_root);

        // Check paths also for empty leaves
        for i in 0..smt.width {
            // Get leaf at that idx if existing
            let leaf = smt.get_node_at_height_and_idx(0, i).0;

            // Create and verify a FieldBasedMHTPath
            let path = smt.get_merkle_path(i).unwrap();
            assert!(path.verify(smt.height as usize, &leaf, &root).unwrap());

            // Create and verify a path from FieldBasedAppendOnlyMHT
            let optimized_path = optimized.get_merkle_path(i as usize).unwrap();
            assert!(optimized_path
                .verify(optimized.height(), &leaf, &optimized_root)
                .unwrap());

            // Assert the two paths are equal
            let optimized_path: FieldBasedBinaryMHTPath<T> = optimized_path.try_into().unwrap();
            assert_eq!(optimized_path, path);

            // Check leaf index is the correct one
            assert_eq!(i as usize, path.leaf_index());

            if i == 0 {
                assert!(path.is_leftmost());
            }
            // leftmost check
            else if i == num_leaves - 1 {
                assert!(path.is_rightmost())
            }
            //rightmost check
            else {
                assert!(!path.is_leftmost());
                assert!(!path.is_rightmost());
            } // other cases check

            // Serialization/deserialization test
            algebra::serialize::test_canonical_serialize_deserialize(true, &path);
        }
    }

    // Tests below stress the functionality inherited from FieldBasedMerkleTree trait
    fn merkle_tree_root_test<T: BatchFieldBasedMerkleTreeParameters, R: RngCore>(
        height: usize,
        num_leaves: usize,
        expected_root: T::Data,
        mut rng: &mut R,
    ) {
        // Init smt
        let mut tree = FieldBasedSparseMHT::<T>::init(height as u8);

        // Init naive merkle tree used as comparison
        let mut naive_mt = NaiveMerkleTree::<T>::new(height);

        // Create leaves at random
        let leaves = (0..num_leaves)
            .map(|_| T::Data::rand(&mut rng))
            .collect::<Vec<_>>();

        // Append leaves to tree
        leaves.iter().for_each(|leaf| {
            tree.append(leaf.clone()).unwrap();
        });

        // Append leaves to naive_mt
        naive_mt.append(leaves.as_slice()).unwrap();

        // Exceeding maximum leaves will result in an error
        assert!(tree.append(leaves[0].clone()).is_err());

        // Finalize tree and get roots of both
        tree.finalize_in_place().unwrap();

        let optimized_root = tree.root().unwrap();
        let naive_root = naive_mt.root().unwrap();
        assert_eq!(naive_root, optimized_root);
        assert_eq!(tree.root().unwrap(), expected_root,);
    }

    /// Tests that effectively all the nodes of the tree are zeroed after a reset
    fn merkle_tree_reset_test<T: BatchFieldBasedMerkleTreeParameters, R: RngCore>(
        height: usize,
        num_leaves: usize,
        mut rng: &mut R,
    ) {
        // Init in memory optimized tree
        let mut tree = FieldBasedSparseMHT::<T>::init(height as u8);

        // Create leaves at random
        let leaves = (0..num_leaves)
            .map(|_| T::Data::rand(&mut rng))
            .collect::<Vec<_>>();

        // Add leaves to tree (don't fill the tree completely)
        leaves[..num_leaves / 2].iter().for_each(|leaf| {
            tree.append(leaf.clone()).unwrap();
        });

        // This is the root we should get after having reset the tree if all the nodes
        // have been zeroed.
        let expected_root = tree.finalize().unwrap().root().unwrap();

        // Finish filling the tree
        leaves[num_leaves / 2..].iter().for_each(|leaf| {
            tree.append(leaf.clone()).unwrap();
        });

        // Reset the tree
        tree.finalize_in_place().unwrap().reset();

        // Add the same leaves as we did initially
        leaves[..num_leaves / 2].iter().for_each(|leaf| {
            tree.append(leaf.clone()).unwrap();
        });

        // Now, if all the nodes have been zeroed, than the assertion below will pass;
        // otherwise, this means that nodes still retained their old values, so the
        // computed root will be different.
        assert_eq!(expected_root, tree.finalize().unwrap().root().unwrap());
    }

    #[cfg(feature = "tweedle")]
    #[test]
    fn test_tweedle_fr() {
        use crate::{
            crh::{TweedleFrBatchPoseidonHash, TweedleFrPoseidonHash},
            merkle_tree::TWEEDLE_DEE_MHT_POSEIDON_PARAMETERS,
        };
        use algebra::fields::tweedle::Fr;
        use rand::SeedableRng;
        use rand_xorshift::XorShiftRng;

        #[derive(Clone, Debug)]
        struct TweedleFrFieldBasedMerkleTreeParams;
        impl FieldBasedMerkleTreeParameters for TweedleFrFieldBasedMerkleTreeParams {
            type Data = Fr;
            type H = TweedleFrPoseidonHash;
            const MERKLE_ARITY: usize = 2;
            const ZERO_NODE_CST: Option<
                FieldBasedMerkleTreePrecomputedZeroConstants<'static, Self::H>,
            > = Some(TWEEDLE_DEE_MHT_POSEIDON_PARAMETERS);
        }
        impl BatchFieldBasedMerkleTreeParameters for TweedleFrFieldBasedMerkleTreeParams {
            type BH = TweedleFrBatchPoseidonHash;
        }

        let rng = &mut XorShiftRng::seed_from_u64(1234567890u64);

        // FieldBasedSparseMerkleTree related tests
        {
            for _ in 0..NUM_SAMPLES {
                test_batch_all_additions_removals::<TweedleFrFieldBasedMerkleTreeParams, _>(
                    TEST_HEIGHT,
                    rng,
                    true,
                    true,
                );
                test_batch_all_additions_removals::<TweedleFrFieldBasedMerkleTreeParams, _>(
                    TEST_HEIGHT,
                    rng,
                    true,
                    false,
                );
                test_batch_all_additions_removals::<TweedleFrFieldBasedMerkleTreeParams, _>(
                    TEST_HEIGHT,
                    rng,
                    false,
                    false,
                );
                test_batch_all_additions_removals::<TweedleFrFieldBasedMerkleTreeParams, _>(
                    TEST_HEIGHT,
                    rng,
                    false,
                    true,
                );
                test_batch_mixed_additions_removals::<TweedleFrFieldBasedMerkleTreeParams, _>(
                    TEST_HEIGHT,
                    rng,
                    false,
                );
                test_batch_mixed_additions_removals::<TweedleFrFieldBasedMerkleTreeParams, _>(
                    TEST_HEIGHT,
                    rng,
                    true,
                );
            }
            test_merkle_path::<TweedleFrFieldBasedMerkleTreeParams, _>(TEST_HEIGHT, rng);
            test_error_cases::<TweedleFrFieldBasedMerkleTreeParams>(TEST_HEIGHT);
            test_edge_cases::<TweedleFrFieldBasedMerkleTreeParams>();
        }

        // FieldBasedMerkleTree related tests
        {
            use algebra::biginteger::BigInteger256;

            let num_leaves = 1 << TEST_HEIGHT;
            let expected_output = Fr::new(BigInteger256([
                11933684180736631717,
                15667815332281652135,
                15034947218494079148,
                4006611621480566003,
            ]));

            merkle_tree_root_test::<TweedleFrFieldBasedMerkleTreeParams, _>(
                TEST_HEIGHT as usize,
                num_leaves,
                expected_output,
                rng,
            );
            merkle_tree_reset_test::<TweedleFrFieldBasedMerkleTreeParams, _>(
                TEST_HEIGHT as usize,
                num_leaves,
                rng,
            );
        }
    }
}
