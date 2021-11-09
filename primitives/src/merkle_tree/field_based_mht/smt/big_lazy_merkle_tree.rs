use algebra::{ToBytes, to_bytes, FromBytes};

use crate::{crh::{FieldBasedHash, BatchFieldBasedHash, FieldBasedHashParameters}, merkle_tree::{
    field_based_mht::{
        BatchFieldBasedMerkleTreeParameters, check_precomputed_parameters,
        FieldBasedMerkleTreePath, FieldBasedBinaryMHTPath,
        smt::{
            Coord, OperationLeaf, ActionLeaf::Remove, BigMerkleTreeState
        },
    },
}, ActionLeaf};

use std::{collections::{HashMap, HashSet}, fs, io::{Error, ErrorKind}, marker::PhantomData, path::Path, sync::Arc};

#[derive(Debug)]
pub struct LazyBigMerkleTree<T: BatchFieldBasedMerkleTreeParameters> {
    // tree in-memory state
    pub(crate) state: BigMerkleTreeState<T>,
    // the number of leaves
    pub(crate) width: usize,
    // stores the leaves
    pub(crate) leaves: HashMap<usize, T::Data>,
    // stores the cached nodes
    pub(crate) cached_nodes: HashMap<Coord, T::Data>,
}

impl<T: BatchFieldBasedMerkleTreeParameters> LazyBigMerkleTree<T> {
    // Creates a new tree of specified `height`.
    // If `persistent` is specified, then DBs will be kept on disk and the tree state will be saved
    // so that the tree can be restored any moment later. Otherwise, no state will be saved on file
    // and the DBs will be deleted.
    pub fn new(
        height: usize,
    ) -> Result<Self, Error> {
        assert!(check_precomputed_parameters::<T>(height));

        let rate = <<T::H  as FieldBasedHash>::Parameters as FieldBasedHashParameters>::R;

        assert_eq!(T::MERKLE_ARITY, 2); // For now we support only arity 2
        // Rate may also be smaller than the arity actually, but this assertion
        // is reasonable and simplify the design.
        assert_eq!(rate, T::MERKLE_ARITY);

        let state = BigMerkleTreeState::<T>::get_default_state(height);
        let width = T::MERKLE_ARITY.pow(height as u32);

        Ok(Self {
            state,
            width,
            leaves: HashMap::new(),
            cached_nodes: HashMap::new(),
        })
    }

    fn insert_to_cache(&mut self, coord: Coord, data:T::Data) {
        self.cached_nodes.insert(coord, data);
    }

    fn contains_key_in_cache(&self, coord: Coord) -> bool {
        self.cached_nodes.get(&coord).is_some()
    }

    fn get_from_cache(&self, coord: Coord) -> Option<T::Data> {
        self.cached_nodes.get(&coord).and_then(|data| Some(*data))
    }

    fn remove_from_cache(&mut self, coord: Coord) -> Option<T::Data>{
        self.cached_nodes.remove(&coord)
    }

    fn insert_to_db(&mut self, idx: usize, data: T::Data) {
        self.leaves.insert(idx, data);
    }

    fn get_from_db(&self, idx: usize) -> Option<T::Data>{
        self.leaves.get(&idx).and_then(|data| Some(*data))
    }

    fn remove_from_db(&mut self, idx: usize) -> Option<T::Data>{
        self.leaves.remove(&idx)
    }

    fn check_b_plus_caching_level_down(&mut self, coord: Coord) {

        let left_child_idx = coord.idx * T::MERKLE_ARITY;
        let left_child_height = 0;
        let left_coord = Coord { height: left_child_height, idx: left_child_idx };

        let right_child_idx = left_child_idx + 1;
        let right_child_height = 0;
        let right_coord = Coord { height: right_child_height, idx: right_child_idx };

        if (!self.state.present_node.contains(&left_coord)) | (!self.state.present_node.contains(&right_coord)) {
            if self.contains_key_in_cache(coord) {
                LazyBigMerkleTree::remove_node_from_cache(self, coord);
            }
        }
        return;
    }

    fn check_b_plus_caching(&mut self, coord: Coord) {
        assert_eq!(T::MERKLE_ARITY, 2, "Arity of the Merkle tree is not 2.");

        if coord.height <= 1 {
            return;
        }

        let left_child_idx = coord.idx * T::MERKLE_ARITY;
        let left_child_height = coord.height - 1;
        let left_coord = Coord { height: left_child_height, idx: left_child_idx };

        let right_child_idx = left_child_idx + 1;
        let right_child_height = left_child_height;
        let right_coord = Coord { height: right_child_height, idx: right_child_idx };

        if left_child_height == 1 {
            self.check_b_plus_caching_level_down(left_coord);
            self.check_b_plus_caching_level_down(right_coord);
            return;
        }
    }

    // Returns the hash value associated to the node.
    // If the node is in the cache, it retrieves from it.
    // If not, recomputes it.
    // Only used for nodes of level >= 1 (not for leaves).
    fn node(&mut self, coord: Coord) -> T::Data {

        assert_eq!(T::MERKLE_ARITY,2, "Arity of the Merkle tree is not 2.");

        //let coord = Coord{height, idx};
        // if the node is an empty node return the hash constant
        if !self.state.present_node.contains(&coord) {
            return T::ZERO_NODE_CST.unwrap().nodes[coord.height];
        }
        let res = self.get_from_cache(coord);

        // if not in the cache, recompute it
        if res == None {
            /* the node is not in the cache, compute it */
            let node_hash;
            if coord.height == 1 {
                /* get leaves to compute */
                let left_child_idx = coord.idx * T::MERKLE_ARITY;
                let left_child = self.get_from_db(left_child_idx);
                let left_hash: T::Data;
                if let Some(i) = left_child {
                    left_hash = i;
                } else {
                    left_hash = T::ZERO_NODE_CST.unwrap().nodes[0];
                }

                let right_child_idx = left_child_idx + 1;
                let right_child = self.get_from_db(right_child_idx);
                let right_hash: T::Data;
                if let Some(i) = right_child {
                    right_hash = i;
                } else {
                    right_hash = T::ZERO_NODE_CST.unwrap().nodes[0];
                }
                node_hash = Self::field_hash(&left_hash, &right_hash);
            } else {
                let height_child = coord.height - 1;
                let left_child_idx = coord.idx * T::MERKLE_ARITY;
                let coord_left = Coord { height: height_child, idx: left_child_idx };
                let left_child_hash = LazyBigMerkleTree::node(self, coord_left);

                let right_child_idx = left_child_idx + 1;
                let coord_right = Coord { height: height_child, idx: right_child_idx };
                let right_child_hash = LazyBigMerkleTree::node(self, coord_right);

                node_hash = Self::field_hash(&left_child_hash, &right_child_hash);
            }
            return node_hash;
        }

        res.unwrap()
    }

    pub fn get_root(&self) -> T::Data {
        self.state.root.clone()
    }

    pub fn height(&self) -> usize { self.state.height }

    fn remove_node_from_cache(&mut self, coord: Coord) {
        self.remove_from_cache(coord);
    }

    fn field_hash(x: &T::Data, y: &T::Data) -> T::Data{
        <T::H as FieldBasedHash>::init_constant_length(2, None)
            .update(x.clone())
            .update(y.clone())
            .finalize()
            .unwrap()
    }

    fn batch_hash(input: &[T::Data]) -> Vec<T::Data> {
        <T::BH as BatchFieldBasedHash>::batch_evaluate(input)
            .expect("Should be able to compute batch hash")
    }

    pub fn is_leaf_empty(&self, coord: Coord) -> bool {
        // check that the index of the leaf is less than the width of the Merkle tree
        assert!(coord.idx < self.width, "Leaf index out of bound.");
        // check that the coordinates of the node corresponds to the leaf level
        assert_eq!(coord.height, 0, "Coord of the node does not correspond to leaf level");

        !self.state.present_node.contains(&coord)
    }

    pub fn process_leaves (&mut self, vec_leaf_op: &[OperationLeaf<T::Data>]) -> T::Data {

        assert_eq!(T::MERKLE_ARITY, 2, "Arity of the Merkle tree is not 2.");

        // Validate inputs
        for i in 0..vec_leaf_op.len() {
            // check that the index of the leaf to be inserted/removed is in range
            assert!(vec_leaf_op[i].coord.idx < self.width, "Leaf index out of bound.");
        }

        // Mark nodes to recompute
        let mut visited_nodes: HashSet<Coord> = HashSet::new();
        let mut nodes_to_process_in_parallel:Vec<Vec<Coord>> = Vec::new();

        // process the first level
        let mut first_level_nodes:Vec<Coord> = Vec::new();
        for j in 0..vec_leaf_op.len() {
            let x = vec_leaf_op[j];
            let coord = x.coord;
            // visit parent
            let height_parent = coord.height + 1;
            let idx_parent = coord.idx / T::MERKLE_ARITY;
            let parent_coord = Coord {height: height_parent, idx: idx_parent};
            if !visited_nodes.contains(&parent_coord) {
                // parent node not visited yet
                visited_nodes.insert(parent_coord);
                // insert node to process in parallel
                first_level_nodes.push(parent_coord);
            }
        }
        nodes_to_process_in_parallel.push(first_level_nodes);

        // got to the upper levels until the root
        let mut height = 1;
        while height < self.state.height {

            visited_nodes.clear();
            let mut higher_level_nodes:Vec<Coord> = Vec::new();

            for j in 0..nodes_to_process_in_parallel[height - 1].len() {
                let coord = nodes_to_process_in_parallel[height - 1][j];
                let height_parent = coord.height + 1;
                let idx_parent = coord.idx / T::MERKLE_ARITY;
                let parent_coord = Coord { height: height_parent, idx: idx_parent };
                if !visited_nodes.contains(&parent_coord) {
                    // parent node not visited yet
                    visited_nodes.insert(parent_coord);
                    // insert node to process in parallel
                    higher_level_nodes.push(parent_coord);
                }
            }
            nodes_to_process_in_parallel.push(higher_level_nodes);
            height += 1;
        }

        // Inserts leaves in the db and marks as present/not present.
        for i in 0..vec_leaf_op.len() {
            let x = vec_leaf_op[i];
            let action = x.action;
            let coord = x.coord;
            let hash = x.hash;
            let idx = coord.idx;

            if action == Remove {
                self.remove_from_db(idx);
                self.state.present_node.remove(&coord);
            } else {
                self.insert_to_db(idx, hash.unwrap());
                self.state.present_node.insert(coord);
            }
        }

        // Compute hashes in parallel - first level
        let mut input_vec = Vec::new();
        let mut both_children_present = Vec::new();

        for j in 0..nodes_to_process_in_parallel[0].len() {
            let coord = nodes_to_process_in_parallel[0][j];

            let idx = coord.idx;
            let left_child_idx = idx * T::MERKLE_ARITY;
            let right_child_idx= left_child_idx + 1;

            let mut left_child_present = true;
            let left_hash = self.get_from_db(left_child_idx).unwrap_or_else(|| {
                left_child_present = false;
                T::ZERO_NODE_CST.unwrap().nodes[0]
            });

            let mut right_child_present = true;
            let right_hash = self.get_from_db(right_child_idx).unwrap_or_else(|| {
                right_child_present = false;
                T::ZERO_NODE_CST.unwrap().nodes[0]
            });

            input_vec.push(left_hash);
            input_vec.push(right_hash);

            if left_child_present || right_child_present {
                self.state.present_node.insert(coord);
            }

            if left_child_present && right_child_present {
                both_children_present.push(true);
            } else {
                both_children_present.push(false);
            }
        }

        // Process the input_vec using batch Poseidon hash
        let output_vec = Self::batch_hash(input_vec.as_slice());

        // Place the computed hash in a cache_parallel
        let mut index_output_vec = 0;
        for coord in nodes_to_process_in_parallel[0].clone() {
            self.state.cache_path.insert(coord, output_vec[index_output_vec]);
            if both_children_present[index_output_vec] {
                self.insert_to_cache(coord,output_vec[index_output_vec]);
            } else {
                self.remove_from_cache(coord);
            }
            index_output_vec += 1;
        }

        // Compute hashes in parallel - level > 1
        let mut height = 2;
        while height <= self.state.height {
            let mut input_vec = Vec::new();
            let mut both_children_present = Vec::new();
            for j in 0..nodes_to_process_in_parallel[height-1].len() {
                let coord = nodes_to_process_in_parallel[height -1][j];

                let idx = coord.idx;
                let left_child_idx = idx * T::MERKLE_ARITY;
                let right_child_idx = left_child_idx + 1;

                let left_child_coord = Coord { height: coord.height - 1, idx: left_child_idx};
                let right_child_coord = Coord { height: coord.height - 1, idx: right_child_idx};

                let left_hash = if self.state.cache_path.contains_key(&left_child_coord) {
                    *self.state.cache_path.get(&left_child_coord).unwrap()
                } else {
                    self.node(left_child_coord)
                };

                let right_hash = if self.state.cache_path.contains_key(&right_child_coord) {
                    *self.state.cache_path.get(&right_child_coord).unwrap()
                } else {
                    self.node(right_child_coord)
                };
                input_vec.push(left_hash);
                input_vec.push(right_hash);

                if self.state.present_node.contains(&left_child_coord) || self.state.present_node.contains(&right_child_coord){
                    self.state.present_node.insert(coord);
                } else {
                    self.state.present_node.remove(&coord);
                }

                if self.state.present_node.contains(&left_child_coord) && self.state.present_node.contains(&right_child_coord){
                    both_children_present.push(true);
                } else {
                    both_children_present.push(false);
                }
            }

            // Process the input_vec using batch Poseidon hash
            let output_vec = Self::batch_hash(input_vec.as_slice());

            // Place the computed hash in a cache_parallel
            let mut index_output_vec = 0;
            for coord in nodes_to_process_in_parallel[height-1].clone() {
                self.state.cache_path.insert(coord, output_vec[index_output_vec]);
                if both_children_present[index_output_vec] == true {
                    self.insert_to_cache(coord,output_vec[index_output_vec]);
                } else {
                    self.remove_from_cache(coord);
                    self.check_b_plus_caching(coord);
                }
                index_output_vec += 1;
            }

            height += 1;
        }

        self.state.root = *self.state.cache_path.get(&Coord{height:self.state.height,idx:0}).unwrap();
        self.state.root.clone()
    }

    // NB. Allows to get Merkle Path of empty leaves too
    pub fn get_merkle_path(&mut self, leaf_coord: Coord) -> FieldBasedBinaryMHTPath<T>
    {
        // check that the index of the leaf is less than the width of the Merkle tree
        assert!(leaf_coord.idx < self.width, "Leaf index out of bound.");

        // check that the coordinates of the node corresponds to the leaf level
        assert_eq!(leaf_coord.height, 0, "Coord of the node does not correspond to leaf level");

        let mut path = Vec::with_capacity(self.state.height);
        let mut node_idx = leaf_coord.idx;
        let mut height = 0;
        while height != self.state.height {

            // Estabilish if sibling is a left or right child
            let (sibling_idx, direction) = if node_idx % T::MERKLE_ARITY == 0 {
                (node_idx + 1, false)
            } else {
                (node_idx - 1, true)
            };

            // Get its hash
            let sibling_coord = Coord { height, idx: sibling_idx };
            let sibling =
                // If it's not empty
                if self.state.present_node.contains(&sibling_coord) {
                // If it's a leaf, it's in the DB and we can get it from there
                if height == 0 {
                    self.get_from_db(sibling_idx).unwrap()
                } else { // Otherwise, we need to recompute it
                    self.node(sibling_coord)
                }
            } else { // If it's empty then we can directly get the precomputed empty at this height
                T::ZERO_NODE_CST.unwrap().nodes[height]
            };

            // Push info to path
            path.push((sibling, direction));

            height += 1; // go up one level
            node_idx = node_idx / T::MERKLE_ARITY; // compute the index of the parent
        }
        assert_eq!(self.node(Coord { height, idx: node_idx }), self.state.root);

        return FieldBasedBinaryMHTPath::<T>::new(path);
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

    use crate::{
        crh::{
            MNT4PoseidonHash, MNT6PoseidonHash,
            MNT4BatchPoseidonHash, MNT6BatchPoseidonHash,
        },
        merkle_tree::field_based_mht::{
            naive:: NaiveMerkleTree,
            smt::{OperationLeaf, Coord, ActionLeaf, LazyBigMerkleTree},
            parameters::{MNT4753_MHT_POSEIDON_PARAMETERS, MNT6753_MHT_POSEIDON_PARAMETERS},
            FieldBasedMerkleTreeParameters, BatchFieldBasedMerkleTreeParameters,
            FieldBasedMerkleTreePath, FieldBasedMerkleTreePrecomputedZeroConstants,
            FieldBasedBinaryMHTPath,
        },

    };

    use std::{
        str::FromStr, path::Path, time::Instant
    };

    use rand::{
        rngs::OsRng, SeedableRng, RngCore
    };
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

    #[test]
    fn process_leaves_mnt4() {

        let mut leaves_to_process: Vec<OperationLeaf<MNT4753Fr>> = Vec::new();

        leaves_to_process.push(OperationLeaf { coord: Coord { height: 0, idx: 0 }, action: ActionLeaf::Insert, hash: Some(MNT4753Fr::from_str("1").unwrap()) });
        leaves_to_process.push(OperationLeaf { coord: Coord { height: 0, idx: 9 }, action: ActionLeaf::Insert, hash: Some(MNT4753Fr::from_str("2").unwrap()) });
        leaves_to_process.push(OperationLeaf { coord: Coord { height: 0, idx: 16 }, action: ActionLeaf::Remove, hash: Some(MNT4753Fr::from_str("3").unwrap()) });
        leaves_to_process.push(OperationLeaf { coord: Coord { height: 0, idx: 29 }, action: ActionLeaf::Insert, hash: Some(MNT4753Fr::from_str("3").unwrap()) });
        leaves_to_process.push(OperationLeaf { coord: Coord { height: 0, idx: 16 }, action: ActionLeaf::Remove, hash: Some(MNT4753Fr::from_str("3").unwrap()) });

        let mut smt = MNT4PoseidonSMTLazy::new(
            TEST_HEIGHT_1,
        ).unwrap();
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

        assert_eq!(tree.root(), smt.state.root, "Roots are not equal");

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
        ).unwrap();
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

        assert_eq!(tree.root(), smt.state.root, "Roots are not equal");
    }

    #[test]
    fn merkle_tree_path_test_mnt4() {

        let num_leaves = 32;
        let mut leaves = Vec::with_capacity(num_leaves);
        let mut leaves_for_lazy_smt = Vec::with_capacity(num_leaves);
        let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

        let mut smt = MNT4PoseidonSMTLazy::new(
            TEST_HEIGHT_1,
        ).unwrap();

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
        ).unwrap();

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