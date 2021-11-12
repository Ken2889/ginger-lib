use crate::{
    crh::{FieldBasedHash, BatchFieldBasedHash, FieldBasedHashParameters},
    merkle_tree::{
        field_based_mht::{
            BatchFieldBasedMerkleTreeParameters, check_precomputed_parameters,
            FieldBasedMerkleTreePath, FieldBasedBinaryMHTPath,
            smt::{
                Coord, OperationLeaf, ActionLeaf::Remove,
            },
        },
    }
};

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

#[derive(Debug)]
pub struct LazyBigMerkleTree<T: BatchFieldBasedMerkleTreeParameters> {
    // the height of this tree
    pub(crate) height: usize,
    // number of leaves = T::ARITY^height
    pub(crate) width: usize,
    // stores the non-empty nodes of the tree
    pub(crate) nodes: HashMap<Coord, T::Data>,
}

impl<T: BatchFieldBasedMerkleTreeParameters> LazyBigMerkleTree<T> {
    /// Creates a new tree of specified `height`.
    pub fn new(
        height: usize,
    ) -> Self 
    {
        assert!(check_precomputed_parameters::<T>(height));

        let rate = <<T::H  as FieldBasedHash>::Parameters as FieldBasedHashParameters>::R;

        assert_eq!(T::MERKLE_ARITY, 2); // For now we support only arity 2
        // Rate may also be smaller than the arity actually, but this assertion
        // is reasonable and simplify the design.
        assert_eq!(rate, T::MERKLE_ARITY);

        let width = T::MERKLE_ARITY.pow(height as u32);

        Self {
            height,
            width,
            nodes: HashMap::new(),
        }
    }

    pub fn get_root(&self) -> T::Data {
        self.nodes
            .get(&Coord { height: self.height, idx: 0 })
            .map_or_else(
                || T::ZERO_NODE_CST.unwrap().nodes[self.height], // If not in nodes, then the root is empty
                |&data| data
            )
    }

    /// Used for testing purposes: return (in order) the non empty leaves of the tree
    pub(crate) fn get_non_empty_leaves(&self) -> BTreeMap<Coord, T::Data> {
        let mut sorted_non_empty_leaves = BTreeMap::new();
        self.nodes.iter().for_each(|(coord, data)| {
            if coord.height == 0 {
                sorted_non_empty_leaves.insert(*coord, *data);
            }
        });
        sorted_non_empty_leaves
    }

    pub fn height(&self) -> usize { self.height }

    fn batch_hash(input: &[T::Data]) -> Vec<T::Data> {
        <T::BH as BatchFieldBasedHash>::batch_evaluate(input)
            .expect("Should be able to compute batch hash")
    }

    pub fn is_leaf_empty(&self, coord: Coord) -> bool {
        // check that the index of the leaf is less than the width of the Merkle tree
        assert!(coord.idx < self.width, "Leaf index out of bound.");
        // check that the coordinates of the node corresponds to the leaf level
        assert_eq!(coord.height, 0, "Coord of the node does not correspond to leaf level");

        !self.nodes.contains_key(&coord)
    }

    pub fn process_leaves (&mut self, vec_leaf_op: &[OperationLeaf<T::Data>]) -> T::Data {

        assert_eq!(T::MERKLE_ARITY, 2, "Arity of the Merkle tree is not 2.");

        // Collect nodes to (re)compute for each level of the tree
        // TODO: Enforce not duplicated leaves when calling process leaves
        // (it's also not allowed to insert and remove the same leaf at the same time)
        let mut nodes_to_process_in_parallel: Vec<HashSet<Coord>> = Vec::with_capacity(self.height);

        // Collect leaves in the first level and contextually add/remove them to/from self.nodes
        nodes_to_process_in_parallel.push(
            vec_leaf_op
                .iter()
                .map(|leaf| {
                    assert!(leaf.coord.idx < self.width, "Leaf index out of range. Max: {}, got: {}", self.width, leaf.coord.idx);
                    if leaf.action == Remove {
                        self.nodes.remove(&leaf.coord);
                    } else {
                        self.nodes.insert(leaf.coord, leaf.hash.unwrap());
                    }
                    leaf.coord
            }).collect::<HashSet<Coord>>()
        );

        // Find all the nodes that must be recomputed following the
        // additional/removal of leaves
        for height in 0..self.height {
            // Keeps track (uniquely) of the nodes to be processed at the level above
            let mut visited_nodes: HashSet<Coord> = HashSet::new();

            nodes_to_process_in_parallel[height]
                .iter()
                .for_each(|coord| {

                    // Compute parent coord
                    let height_parent = coord.height + 1;
                    let idx_parent = coord.idx / T::MERKLE_ARITY;
                    let parent_coord = Coord { height: height_parent, idx: idx_parent };
                    visited_nodes.insert(parent_coord);
                });

            nodes_to_process_in_parallel.push(visited_nodes);
        }

        // Compute hashes of the affected nodes (ignoring leaf nodes)
        for height in 1..=self.height {
            let mut input_vec = Vec::new(); // Leaves to be hashed
            let mut empty_node = Vec::new(); // Keep track of which node is empty
    
            // Collect leaves to be hashed in parallel
            nodes_to_process_in_parallel[height]
                .iter()
                .for_each(|coord| {    

                    // Compute children coords and get corresponding values
                    let idx = coord.idx;
                    let left_child_idx = idx * T::MERKLE_ARITY;
                    let right_child_idx= left_child_idx + 1;
                    let left_child_coord = Coord { height: coord.height - 1, idx: left_child_idx};
                    let right_child_coord = Coord { height: coord.height - 1, idx: right_child_idx};
        
                    let mut is_node_empty = true;
                    let left_hash = self.nodes
                        .get(&left_child_coord)
                        .map_or_else(
                            || T::ZERO_NODE_CST.unwrap().nodes[height - 1],
                            |&data| {
                                is_node_empty = false;
                                data
                            }
                        );
        
                    let right_hash = self.nodes
                        .get(&right_child_coord)
                        .map_or_else(
                            || T::ZERO_NODE_CST.unwrap().nodes[height - 1],
                            |&data| {
                                is_node_empty = false;
                                data
                            }
                        );
        
                    // Must compute hash iff node will be non-empty, otherwise
                    // we have already its value precomputed
                    if !is_node_empty {
                        input_vec.push(left_hash);
                        input_vec.push(right_hash);
                    } else {
                        // If the node was present in self.nodes we must remove it,
                        // as it has become empty due to some leaf removal operation
                        self.nodes.remove(coord);
                    }
        
                    empty_node.push(is_node_empty);
                });
    
            // Process the input_vec of the nodes that will be non-empty
            // (i.e. the ones who have at least one non-empty children)
            // using batch Poseidon hash
            if !input_vec.is_empty() {
                let output_vec = Self::batch_hash(input_vec.as_slice());
    
                // Update the nodes map with the new values
                let mut output_vec_index = 0;
                for (coord, is_empty) in nodes_to_process_in_parallel[height].iter().zip(empty_node) {
                    if !is_empty {
                        self.nodes.insert(*coord, output_vec[output_vec_index]);
                        output_vec_index += 1;
                    }
                }
            }
        }

        // Return root (which should have been already updated)
        self.get_root()
    }

    // NB. Allows to get Merkle Path of empty leaves too
    pub fn get_merkle_path(&mut self, leaf_coord: Coord) -> FieldBasedBinaryMHTPath<T>
    {
        // check that the index of the leaf is less than the width of the Merkle tree
        assert!(leaf_coord.idx < self.width, "Leaf index out of bound.");

        // check that the coordinates of the node corresponds to the leaf level
        assert_eq!(leaf_coord.height, 0, "Coord of the node does not correspond to leaf level");

        let mut path = Vec::with_capacity(self.height);
        let mut node_idx = leaf_coord.idx;
        let mut height = 0;
        while height != self.height {

            // Estabilish if sibling is a left or right child
            let (sibling_idx, direction) = if node_idx % T::MERKLE_ARITY == 0 {
                (node_idx + 1, false)
            } else {
                (node_idx - 1, true)
            };

            // Get its hash
            let sibling_coord = Coord { height, idx: sibling_idx };
            let sibling = self.nodes
                .get(&sibling_coord)
                .map_or_else(
                    || T::ZERO_NODE_CST.unwrap().nodes[height],
                    |&data| data
                );
                
            // Push info to path
            path.push((sibling, direction));

            height += 1; // go up one level
            node_idx = node_idx / T::MERKLE_ARITY; // compute the index of the parent
        }
        assert_eq!(self.nodes.get(&Coord { height, idx: node_idx }).unwrap(), &self.get_root());

        FieldBasedBinaryMHTPath::<T>::new(path)
    }
}

#[cfg(test)]
mod test {

    use algebra::{
        fields::{
          mnt4753::Fr as MNT4753Fr, mnt6753::Fr as MNT6753Fr
        },
        biginteger::BigInteger768,
        Field, UniformRand,
        ToBytes, to_bytes, FromBytes,
    };

    use crate::{FieldBasedOptimizedMHT, crh::{
            MNT4PoseidonHash, MNT6PoseidonHash,
            MNT4BatchPoseidonHash, MNT6BatchPoseidonHash,
        }, merkle_tree::field_based_mht::{
            naive:: NaiveMerkleTree,
            smt::{OperationLeaf, Coord, ActionLeaf, LazyBigMerkleTree},
            parameters::{MNT4753_MHT_POSEIDON_PARAMETERS, MNT6753_MHT_POSEIDON_PARAMETERS},
            FieldBasedMerkleTreeParameters, BatchFieldBasedMerkleTreeParameters,
            FieldBasedMerkleTreePath, FieldBasedMerkleTreePrecomputedZeroConstants,
            FieldBasedBinaryMHTPath, FieldBasedMerkleTree,
        }};

    use std::{
        str::FromStr, path::Path, time::Instant
    };

    use rand::{Rng, RngCore, SeedableRng, prelude::SliceRandom, thread_rng};
    use rand_xorshift::XorShiftRng;

    #[derive(Clone, Debug)]
    struct MNT4753FieldBasedMerkleTreeParams;
    impl FieldBasedMerkleTreeParameters for MNT4753FieldBasedMerkleTreeParams {
        type Data = MNT4753Fr;
        type H = MNT4PoseidonHash;
        const MERKLE_ARITY: usize = 2;
        const ZERO_NODE_CST: Option<FieldBasedMerkleTreePrecomputedZeroConstants<'static, Self::H>> =
            Some(MNT4753_MHT_POSEIDON_PARAMETERS);
    }
    impl BatchFieldBasedMerkleTreeParameters for MNT4753FieldBasedMerkleTreeParams {
        type BH = MNT4BatchPoseidonHash;
    }
    type MNT4753FieldBasedMerkleTree = NaiveMerkleTree<MNT4753FieldBasedMerkleTreeParams>;
    type MNT4PoseidonSMTLazy = LazyBigMerkleTree<MNT4753FieldBasedMerkleTreeParams>;
    type MNT4MerklePath = FieldBasedBinaryMHTPath<MNT4753FieldBasedMerkleTreeParams>;

    #[derive(Clone, Debug)]
    struct MNT6753FieldBasedMerkleTreeParams;
    impl FieldBasedMerkleTreeParameters for MNT6753FieldBasedMerkleTreeParams {
        type Data = MNT6753Fr;
        type H = MNT6PoseidonHash;
        const MERKLE_ARITY: usize = 2;
        const ZERO_NODE_CST: Option<FieldBasedMerkleTreePrecomputedZeroConstants<'static, Self::H>> =
            Some(MNT6753_MHT_POSEIDON_PARAMETERS);
    }
    impl BatchFieldBasedMerkleTreeParameters for MNT6753FieldBasedMerkleTreeParams {
        type BH = MNT6BatchPoseidonHash;
    }
    type MNT6753FieldBasedMerkleTree = NaiveMerkleTree<MNT6753FieldBasedMerkleTreeParams>;
    type MNT6PoseidonSMTLazy = LazyBigMerkleTree<MNT6753FieldBasedMerkleTreeParams>;
    type MNT6MerklePath = FieldBasedBinaryMHTPath<MNT6753FieldBasedMerkleTreeParams>;

    const TEST_HEIGHT_1: usize = 5;
    const NUM_SAMPLES: usize = 1;

    fn merkle_tree_root_test<T: BatchFieldBasedMerkleTreeParameters, R: RngCore>(
        height: usize,
        rng: &mut R,
        adjacent_leaves: bool,
    ) 
    {
        // Initialize trees
        let mut smt = LazyBigMerkleTree::<T>::new(height);
        let num_leaves = smt.width;

        let mut optimized = FieldBasedOptimizedMHT::<T>::init(height, num_leaves);

        // Initialize leaves
        let mut leaves = (0..num_leaves)
            .map(|idx| OperationLeaf { coord: Coord { height: 0, idx }, action: ActionLeaf::Insert, hash: Some(T::Data::rand(rng)) })
            .collect::<Vec<_>>();

        if !adjacent_leaves {
            leaves.shuffle(rng);
        }

        // Test insertions
        let chunk_size = rng.gen_range(1, num_leaves + 1);
        leaves
            .chunks(chunk_size)
            .for_each(|leaves| {
                // Insert all leaves into smt and get root
                let smt_root = smt.process_leaves(leaves);

                // Insert into optimized and get root
                let mut last_idx = 0;
                smt.get_non_empty_leaves().iter().for_each(|(coord, leaf)| {
                    for _ in last_idx..coord.idx {
                        optimized.append(T::ZERO_NODE_CST.unwrap().nodes[0]).unwrap();
                    }
                    optimized.append(*leaf);
                    last_idx = coord.idx + 1;
                });
                let optimized_root = optimized.finalize().root().unwrap();
                optimized.reset();

                // Roots must be equal
                assert_eq!(smt_root, optimized_root, "Roots are not equal");
            });
        
        // Nodes map must be full
        assert_eq!(smt.nodes.len(), (num_leaves * 2) - 1);

        optimized.reset();

        // Test removals
        // Remove all leaves and update smt
        leaves
            .iter_mut()
            .for_each(|leaf| leaf.action = ActionLeaf::Remove);

        leaves
            .chunks(chunk_size)
            .enumerate()
            .for_each(|(chunk_num, leaves_chunk)| {
                println!("Chunk size: {}, Chunk num: {}", chunk_size, chunk_num);
                // Remove leaves from smt and get root
                let smt_root = smt.process_leaves(leaves_chunk);

                // "Remove" from optimized and get root
                let mut last_idx = 0;
                smt.get_non_empty_leaves().iter().for_each(|(coord, leaf)| {
                    for _ in last_idx..coord.idx {
                        optimized.append(T::ZERO_NODE_CST.unwrap().nodes[0]).unwrap();
                    }
                    optimized.append(*leaf);
                    last_idx = coord.idx + 1;
                });
                
                let optimized_root = optimized.finalize().root().unwrap();
                optimized.reset();

                // Roots must be equal
                assert_eq!(smt_root, optimized_root, "Roots are not equal");
        });

        // In the end, we must have an empty root...
        assert_eq!(smt.get_root(), T::ZERO_NODE_CST.unwrap().nodes[height], "Root after removal of all leaves must be equal to empty root");

        // ...and nodes map must be empty
        assert!(smt.nodes.is_empty());
    }

    #[test]
    fn process_leaves_mnt4() {
        for _ in 0..NUM_SAMPLES {
            //merkle_tree_root_test::<MNT4753FieldBasedMerkleTreeParams, _>(TEST_HEIGHT_1, &mut thread_rng(), false);
            merkle_tree_root_test::<MNT4753FieldBasedMerkleTreeParams, _>(TEST_HEIGHT_1, &mut thread_rng(), false);
            merkle_tree_root_test::<MNT4753FieldBasedMerkleTreeParams, _>(TEST_HEIGHT_1, &mut thread_rng(), true);
        }
        
        /*let mut leaves_to_process: Vec<OperationLeaf<MNT4753Fr>> = Vec::new();

        leaves_to_process.push(OperationLeaf { coord: Coord { height: 0, idx: 0 }, action: ActionLeaf::Insert, hash: Some(MNT4753Fr::from_str("1").unwrap()) });
        leaves_to_process.push(OperationLeaf { coord: Coord { height: 0, idx: 9 }, action: ActionLeaf::Insert, hash: Some(MNT4753Fr::from_str("2").unwrap()) });
        leaves_to_process.push(OperationLeaf { coord: Coord { height: 0, idx: 16 }, action: ActionLeaf::Insert, hash: Some(MNT4753Fr::from_str("3").unwrap()) });
        leaves_to_process.push(OperationLeaf { coord: Coord { height: 0, idx: 29 }, action: ActionLeaf::Insert, hash: Some(MNT4753Fr::from_str("3").unwrap()) });
        leaves_to_process.push(OperationLeaf { coord: Coord { height: 0, idx: 16 }, action: ActionLeaf::Remove, hash: Some(MNT4753Fr::from_str("3").unwrap()) });

        let mut smt = MNT4PoseidonSMTLazy::new(
            TEST_HEIGHT_1,
        );
        smt.process_leaves(leaves_to_process.as_slice());

        //=============================================

        let mut leaves = Vec::new();
        leaves.push(MNT4753Fr::from_str("1").unwrap());
        for _ in 1..9 {
            let f = MNT4753Fr::zero();
            leaves.push(f);
        }
        leaves.push(MNT4753Fr::from_str("2").unwrap());
        for _ in 10..29 {
            let f = MNT4753Fr::zero();
            leaves.push(f);
        }
        leaves.push(MNT4753Fr::from_str("3").unwrap());
        for _ in 30..31 {
            let f = MNT4753Fr::zero();
            leaves.push(f);
        }
        let mut tree = MNT4753FieldBasedMerkleTree::new(TEST_HEIGHT_1);
        tree.append(&leaves).unwrap();

        assert_eq!(tree.root(), smt.get_root(), "Roots are not equal");*/

    }

    #[test]
    fn process_leaves_mnt6() {

        let mut leaves_to_process: Vec<OperationLeaf<MNT6753Fr>> = Vec::new();

        leaves_to_process.push(OperationLeaf { coord: Coord { height: 0, idx: 0 }, action: ActionLeaf::Insert, hash: Some(MNT6753Fr::from_str("1").unwrap()) });
        leaves_to_process.push(OperationLeaf { coord: Coord { height: 0, idx: 9 }, action: ActionLeaf::Insert, hash: Some(MNT6753Fr::from_str("2").unwrap()) });
        leaves_to_process.push(OperationLeaf { coord: Coord { height: 0, idx: 16 }, action: ActionLeaf::Remove, hash: Some(MNT6753Fr::from_str("3").unwrap()) });
        leaves_to_process.push(OperationLeaf { coord: Coord { height: 0, idx: 29 }, action: ActionLeaf::Insert, hash: Some(MNT6753Fr::from_str("3").unwrap()) });
        leaves_to_process.push(OperationLeaf { coord: Coord { height: 0, idx: 16 }, action: ActionLeaf::Remove, hash: Some(MNT6753Fr::from_str("3").unwrap()) });

        let mut smt = MNT6PoseidonSMTLazy::new(
            TEST_HEIGHT_1,
        );
        smt.process_leaves(leaves_to_process.as_slice());

        //=============================================

        let mut leaves = Vec::new();
        leaves.push(MNT6753Fr::from_str("1").unwrap());
        for _ in 1..9 {
            let f = MNT6753Fr::zero();
            leaves.push(f);
        }
        leaves.push(MNT6753Fr::from_str("2").unwrap());
        for _ in 10..29 {
            let f = MNT6753Fr::zero();
            leaves.push(f);
        }
        leaves.push(MNT6753Fr::from_str("3").unwrap());
        for _ in 30..31 {
            let f = MNT6753Fr::zero();
            leaves.push(f);
        }
        let mut tree = MNT6753FieldBasedMerkleTree::new(TEST_HEIGHT_1);
        tree.append(&leaves).unwrap();

        assert_eq!(tree.root(), smt.get_root(), "Roots are not equal");
    }

    #[test]
    fn merkle_tree_path_test_mnt4() {

        let num_leaves = 32;
        let mut leaves = Vec::with_capacity(num_leaves);
        let mut leaves_for_lazy_smt = Vec::with_capacity(num_leaves);
        let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

        let mut smt = MNT4PoseidonSMTLazy::new(
            TEST_HEIGHT_1,
        );

        // Generate random leaves, half of which empty
        for i in 0..num_leaves/2 {
            let leaf = MNT4753Fr::rand(&mut rng);
            leaves.push(leaf);
            leaves_for_lazy_smt.push(OperationLeaf { coord: Coord { height: 0, idx: i }, action: ActionLeaf::Insert, hash: Some(leaf)});
        }

        for i in num_leaves/2..num_leaves {
            let leaf = MNT4753Fr::zero();
            leaves.push(leaf);
            leaves_for_lazy_smt.push(OperationLeaf { coord: Coord { height: 0, idx: i }, action: ActionLeaf::Insert, hash: Some(leaf)});
        }

        // Compute the root of the tree, and do the same for a NaiveMHT, used here as reference
        let mut naive_tree = MNT4753FieldBasedMerkleTree::new(TEST_HEIGHT_1);
        naive_tree.append(&leaves).unwrap();
        let root = smt.process_leaves(leaves_for_lazy_smt.as_slice());
        let naive_root = naive_tree.root();
        assert_eq!(root, naive_root);

        for i in 0..num_leaves {

            // Create and verify a FieldBasedMHTPath
            let path = smt.get_merkle_path(Coord{height: 0, idx: i});
            assert!(path.verify(smt.height(), &leaves[i], &root).unwrap());

            // Create and verify a Naive path
            let naive_path = naive_tree.generate_proof(i, &leaves[i]).unwrap();
            assert!(naive_path.verify(naive_tree.height(), &leaves[i], &naive_root ).unwrap());

            // Assert the two paths are equal
            assert_eq!(naive_path, path);

            // Check leaf index is the correct one
            assert_eq!(i, path.leaf_index());

            if i == 0 { assert!(path.is_leftmost()); } // leftmost check
            else if i == 2usize.pow(TEST_HEIGHT_1 as u32) - 1 { assert!(path.is_rightmost()) }  //rightmost check
            else { assert!(!path.is_leftmost()); assert!(!path.is_rightmost()); } // other cases check

            // Serialization/deserialization test
            let path_serialized = to_bytes!(path).unwrap();
            let path_deserialized = MNT4MerklePath::read(path_serialized.as_slice()).unwrap();
            assert_eq!(path, path_deserialized);
        }
    }

    #[test]
    fn merkle_tree_path_test_mnt6() {

        let num_leaves = 32;
        let mut leaves = Vec::with_capacity(num_leaves);
        let mut leaves_for_lazy_smt = Vec::with_capacity(num_leaves);
        let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

        let mut smt = MNT6PoseidonSMTLazy::new(
            TEST_HEIGHT_1,
        );

        // Generate random leaves, half of which empty
        for i in 0..num_leaves/2 {
            let leaf = MNT6753Fr::rand(&mut rng);
            leaves.push(leaf);
            leaves_for_lazy_smt.push(OperationLeaf { coord: Coord { height: 0, idx: i }, action: ActionLeaf::Insert, hash: Some(leaf)});
        }

        for i in num_leaves/2..num_leaves {
            let leaf = MNT6753Fr::zero();
            leaves.push(leaf);
            leaves_for_lazy_smt.push(OperationLeaf { coord: Coord { height: 0, idx: i }, action: ActionLeaf::Insert, hash: Some(leaf)});
        }

        // Compute the root of the tree, and do the same for a NaiveMHT, used here as reference
        let mut naive_tree = MNT6753FieldBasedMerkleTree::new(TEST_HEIGHT_1);
        naive_tree.append(&leaves).unwrap();
        let root = smt.process_leaves(leaves_for_lazy_smt.as_slice());
        let naive_root = naive_tree.root();
        assert_eq!(root, naive_root);

        for i in 0..num_leaves {

            // Create and verify a FieldBasedMHTPath
            let path = smt.get_merkle_path(Coord{height: 0, idx: i});
            assert!(path.verify(smt.height(), &leaves[i], &root).unwrap());

            // Create and verify a Naive path
            let naive_path = naive_tree.generate_proof(i, &leaves[i]).unwrap();
            assert!(naive_path.verify(naive_tree.height(), &leaves[i], &naive_root ).unwrap());

            // Assert the two paths are equal
            assert_eq!(naive_path, path);

            // Check leaf index is the correct one
            assert_eq!(i, path.leaf_index());

            if i == 0 { assert!(path.is_leftmost()); } // leftmost check
            else if i == 2usize.pow(TEST_HEIGHT_1 as u32) - 1 { assert!(path.is_rightmost()) }  //rightmost check
            else { assert!(!path.is_leftmost()); assert!(!path.is_rightmost()); } // other cases check

            // Serialization/deserialization test
            let path_serialized = to_bytes!(path).unwrap();
            let path_deserialized = MNT6MerklePath::read(path_serialized.as_slice()).unwrap();
            assert_eq!(path, path_deserialized);
        }
    }
}