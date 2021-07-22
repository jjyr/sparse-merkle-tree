use crate::{
    error::{Error, Result},
    merge::{align_with_zeros, hash_leaf, merge},
    merkle_proof::MerkleProof,
    traits::{Hasher, Store, Value},
    vec::Vec,
    EXPECTED_PATH_SIZE, H256, MAX_STACK_SIZE,
};
use core::cmp::max;
use core::cmp::Ordering;
use core::marker::PhantomData;
use std::collections::{BTreeMap, VecDeque};

pub type BranchKey = H256;

// /// The branch key
// #[derive(Debug, Clone, Eq, PartialEq, Hash)]
// pub struct BranchKey {
//     pub height: u8,
//     pub node_key: H256,
// }

// impl BranchKey {
//     pub fn new(height: u8, node_key: H256) -> BranchKey {
//         BranchKey { height, node_key }
//     }
// }

// impl PartialOrd for BranchKey {
//     fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
//         Some(self.cmp(other))
//     }
// }
// impl Ord for BranchKey {
//     fn cmp(&self, other: &Self) -> Ordering {
//         match self.height.cmp(&other.height) {
//             Ordering::Equal => self.node_key.cmp(&other.node_key),
//             ordering => ordering,
//         }
//     }
// }

// /// A branch in the SMT
// #[derive(Debug, Eq, PartialEq, Clone)]
// pub struct BranchNode {
//     pub left: H256,
//     pub right: H256,
// }

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct BranchNode {
    pub fork_height: u8,
    pub key: H256,
    pub node_type: NodeType,
}

impl BranchNode {
    // get node at a specific height
    fn node_at(&self, height: u8) -> NodeType {
        match self.node_type {
            NodeType::Pair(lhs, rhs) => {
                // let is_right = self.key.get_bit(height);
                // if is_right {
                //     NodeType::Pair(sibling, node)
                // } else {
                //     NodeType::Pair(node, sibling)
                // }
                NodeType::Pair(lhs, rhs)
            }
            NodeType::Single(node) => NodeType::Single(node),
        }
    }

    fn key(&self) -> &H256 {
        &self.key
    }
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum NodeType {
    Single(H256),
    Pair(H256, H256),
}

/// A leaf in the SMT
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct LeafNode<V> {
    pub key: H256,
    pub value: V,
}

#[derive(Debug, Default, Eq, PartialEq, Clone)]
pub struct RootNode {
    node_height: u8,
    node_key: H256,
    node: H256,
}

impl RootNode {
    fn root_hash<H: Hasher + Default>(&self) -> H256 {
        let merge_height = u8::MAX;
        let mut root_hash = self.node;
        // align node to merge_height
        if self.node_height < merge_height {
            let n_zeros = merge_height - self.node_height;
            root_hash =
                align_with_zeros::<H>(self.node_height, &self.node_key, &self.node, n_zeros);
        }
        root_hash
    }
}

/// Sparse merkle tree
#[derive(Default, Debug)]
pub struct SparseMerkleTree<H, V, S> {
    store: S,
    root: RootNode,
    phantom: PhantomData<(H, V)>,
}

impl<H: Hasher + Default, V: Value, S: Store<V>> SparseMerkleTree<H, V, S> {
    /// Build a merkle tree from root and store
    pub fn new(root: RootNode, store: S) -> SparseMerkleTree<H, V, S> {
        SparseMerkleTree {
            root,
            store,
            phantom: PhantomData,
        }
    }

    /// Merkle root
    pub fn root_node(&self) -> &RootNode {
        &self.root
    }

    /// Merkle root
    pub fn root(&self) -> H256 {
        self.root.root_hash::<H>()
    }

    /// Check empty of the tree
    pub fn is_empty(&self) -> bool {
        self.root().is_zero()
    }

    /// Destroy current tree and retake store
    pub fn take_store(self) -> S {
        self.store
    }

    /// Get backend store
    pub fn store(&self) -> &S {
        &self.store
    }

    /// Get mutable backend store
    pub fn store_mut(&mut self) -> &mut S {
        &mut self.store
    }

    // /// Update a leaf, return new merkle root
    // /// set to zero value to delete a key
    // pub fn update(&mut self, key: H256, value: V) -> Result<&H256> {
    //     // compute and store new leaf
    //     let node = value.to_h256();
    //     // notice when value is zero the leaf is deleted, so we do not need to store it
    //     if !node.is_zero() {
    //         self.store.insert_leaf(key, value)?;
    //     } else {
    //         self.store.remove_leaf(&key)?;
    //     }

    //     // recompute the tree from bottom to top
    //     let mut current_key = key;
    //     let mut current_node = node;
    //     for height in 0..=core::u8::MAX {
    //         let parent_key = current_key.parent_path(height);
    //         let parent_branch_key = BranchKey::new(height, parent_key);
    //         let (left, right) =
    //             if let Some(parent_branch) = self.store.get_branch(&parent_branch_key)? {
    //                 if current_key.is_right(height) {
    //                     (parent_branch.left, current_node)
    //                 } else {
    //                     (current_node, parent_branch.right)
    //                 }
    //             } else if current_key.is_right(height) {
    //                 (H256::zero(), current_node)
    //             } else {
    //                 (current_node, H256::zero())
    //             };

    //         if !left.is_zero() || !right.is_zero() {
    //             // insert or update branch
    //             self.store
    //                 .insert_branch(parent_branch_key, BranchNode { left, right })?;
    //         } else {
    //             // remove empty branch
    //             self.store.remove_branch(&parent_branch_key)?;
    //         }
    //         // prepare for next round
    //         current_key = parent_key;
    //         current_node = merge::<H>(height, &parent_key, &left, &right);
    //     }

    //     self.root = current_node;
    //     Ok(&self.root)
    // }

    // /// Get value of a leaf
    // /// return zero value if leaf not exists
    // pub fn get(&self, key: &H256) -> Result<V> {
    //     if self.is_empty() {
    //         return Ok(V::zero());
    //     }
    //     Ok(self
    //         .store
    //         .get_leaf(key)?
    //         .map(|l| l.value)
    //         .unwrap_or_else(V::zero))
    // }

    /// Get value of a leaf
    /// return zero value if leaf not exists
    pub fn get(&self, key: &H256) -> Result<V> {
        if self.is_empty() {
            return Ok(V::zero());
        }

        let mut node = self.root.node;
        loop {
            let branch_node = self
                .store
                .get_branch(&node)?
                .ok_or_else(|| Error::MissingBranch(node))?;

            match branch_node.node_at(branch_node.fork_height) {
                NodeType::Pair(left, right) => {
                    let is_right = key.get_bit(branch_node.fork_height);
                    node = if is_right { right } else { left };
                }
                NodeType::Single(node) => {
                    if key == branch_node.key() {
                        return Ok(self
                            .store
                            .get_leaf(&node)?
                            .ok_or_else(|| Error::MissingLeaf(node))?
                            .value);
                    } else {
                        return Ok(V::zero());
                    }
                }
            }
        }
    }

    // /// Generate merkle proof
    // pub fn merkle_proof(&self, mut keys: Vec<H256>) -> Result<MerkleProof> {
    //     if keys.is_empty() {
    //         return Err(Error::EmptyKeys);
    //     }

    //     // sort keys
    //     keys.sort_unstable();

    //     // Collect leaf bitmaps
    //     let mut leaves_bitmap: Vec<H256> = Default::default();
    //     for current_key in &keys {
    //         let mut bitmap = H256::zero();
    //         for height in 0..=core::u8::MAX {
    //             let parent_key = current_key.parent_path(height);
    //             let parent_branch_key = BranchKey::new(height, parent_key);
    //             if let Some(parent_branch) = self.store.get_branch(&parent_branch_key)? {
    //                 let sibling = if current_key.is_right(height) {
    //                     parent_branch.left
    //                 } else {
    //                     parent_branch.right
    //                 };
    //                 if !sibling.is_zero() {
    //                     bitmap.set_bit(height);
    //                 }
    //             } else {
    //                 // The key is not in the tree (support non-inclusion proof)
    //             }
    //         }
    //         leaves_bitmap.push(bitmap);
    //     }

    //     let mut proof: Vec<H256> = Default::default();
    //     let mut stack_fork_height = [0u8; MAX_STACK_SIZE]; // store fork height
    //     let mut stack_top = 0;
    //     let mut leaf_index = 0;
    //     while leaf_index < keys.len() {
    //         let leaf_key = keys[leaf_index];
    //         let fork_height = if leaf_index + 1 < keys.len() {
    //             leaf_key.fork_height(&keys[leaf_index + 1])
    //         } else {
    //             core::u8::MAX
    //         };
    //         for height in 0..=fork_height {
    //             if height == fork_height && leaf_index + 1 < keys.len() {
    //                 // If it's not final round, we don't need to merge to root (height=255)
    //                 break;
    //             }
    //             let parent_key = leaf_key.parent_path(height);
    //             let is_right = leaf_key.is_right(height);

    //             // has non-zero sibling
    //             if stack_top > 0 && stack_fork_height[stack_top - 1] == height {
    //                 stack_top -= 1;
    //             } else if leaves_bitmap[leaf_index].get_bit(height) {
    //                 let parent_branch_key = BranchKey::new(height, parent_key);
    //                 if let Some(parent_branch) = self.store.get_branch(&parent_branch_key)? {
    //                     let sibling = if is_right {
    //                         parent_branch.left
    //                     } else {
    //                         parent_branch.right
    //                     };
    //                     if !sibling.is_zero() {
    //                         proof.push(sibling);
    //                     } else {
    //                         unreachable!();
    //                     }
    //                 } else {
    //                     // The key is not in the tree (support non-inclusion proof)
    //                 }
    //             }
    //         }
    //         debug_assert!(stack_top < MAX_STACK_SIZE);
    //         stack_fork_height[stack_top] = fork_height;
    //         stack_top += 1;
    //         leaf_index += 1;
    //     }
    //     assert_eq!(stack_top, 1);
    //     Ok(MerkleProof::new(leaves_bitmap, proof))
    // }

    /// Update a leaf, return new merkle root
    /// set to zero value to delete a key
    pub fn update(&mut self, mut key: H256, value: V) -> Result<H256> {
        // store the path, sparse index will ignore zero members
        let mut path = Vec::new();
        if !self.is_empty() {
            let mut node = self.root.node;
            loop {
                let branch_node = self
                    .store
                    .get_branch(&node)?
                    .ok_or_else(|| Error::MissingBranch(node))?;
                let height = max(key.fork_height(branch_node.key()), branch_node.fork_height);
                match branch_node.node_at(height) {
                    NodeType::Pair(left, right) => {
                        if height > branch_node.fork_height {
                            // the merge height is higher than node, so we do not need to remove node's branch
                            path.push((height, branch_node.key, branch_node.fork_height, node));
                            break;
                        } else {
                            self.store.remove_branch(&node)?;
                            let is_right = key.get_bit(height);
                            let sibling;
                            if is_right {
                                node = right;
                                sibling = left;
                            } else {
                                node = left;
                                sibling = right;
                            }
                            path.push((height, branch_node.key, branch_node.fork_height, sibling));
                        }
                    }
                    NodeType::Single(node) => {
                        if &key == branch_node.key() {
                            self.store.remove_leaf(&node)?;
                            self.store.remove_branch(&node)?;
                        } else {
                            path.push((height, branch_node.key, branch_node.fork_height, node));
                        }
                        break;
                    }
                }
            }
        }

        // compute and store new leaf
        let mut node = hash_leaf::<H>(&key, &value.to_h256());
        // notice when value is zero the leaf is deleted, so we do not need to store it
        if !node.is_zero() {
            self.store.insert_leaf(node, LeafNode { key, value })?;

            // build at least one branch for leaf
            self.store.insert_branch(
                node,
                BranchNode {
                    key,
                    fork_height: 0,
                    node_type: NodeType::Single(node),
                },
            )?;
        }

        let mut node_height = 0;

        // recompute the tree from bottom to top
        for (merge_height, sibling_key, mut sibling_height, mut sibling) in path.into_iter().rev() {
            // make sure merge height is correct
            {
                let fork_height = key.fork_height(&sibling_key);
                if fork_height == 0 {
                    ()
                }
                // assert_eq!(fork_height, merge_height);
            }

            assert!(!node.is_zero() || !sibling.is_zero(), "does this happen?");
            // set sibling as node, then continue
            if node.is_zero() {
                let fork_height  = key.fork_height(&sibling_key);
                node = sibling;
                if key.get_bit(sibling_height) {
                    key.clear_bit(sibling_height)
                } else {
                    key.set_bit(sibling_height)
                }
                continue;
            }

            let origin_node = node;
            let origin_sibling = sibling;

            // align node to merge_height
            if node_height < merge_height {
                let node_key = key.parent_path(node_height);
                let n_zeros = merge_height - node_height;
                node = align_with_zeros::<H>(node_height, &node_key, &node, n_zeros);
                node_height = merge_height;
            }

            // align sibling to merge_height
            if sibling_height < merge_height {
                let node_key = sibling_key.parent_path(sibling_height);
                let n_zeros = merge_height - sibling_height;
                sibling = align_with_zeros::<H>(sibling_height, &node_key, &sibling, n_zeros);
                sibling_height = merge_height;
            }

            let is_right = key.get_bit(merge_height);
            let node_key = key.parent_path(merge_height);
            let (lhs, rhs, origin_lhs, origin_rhs) = if is_right {
                (sibling, node, origin_sibling, origin_node)
            } else {
                (node, sibling, origin_node, origin_sibling)
            };

            let parent = merge::<H>(merge_height, &node_key, &lhs, &rhs);

            if !node.is_zero() {
                // node is exists
                let parent_key = key.parent_path(merge_height);
                let branch_node = BranchNode {
                    key: parent_key,
                    fork_height: merge_height,
                    node_type: NodeType::Pair(origin_lhs, origin_rhs),
                };
                self.store.insert_branch(parent, branch_node)?;
            }
            node = parent;
            node_height += 1;
        }

        let merge_height = u8::MAX;
        let node_key = key.parent_path(node_height);
        let root = RootNode {
            node_height,
            node_key,
            node,
        };

        self.root = root;

        // align node to merge_height
        if node_height < merge_height {
            let n_zeros = merge_height - node_height;
            node = align_with_zeros::<H>(node_height, &node_key, &node, n_zeros);
            node_height = merge_height;
        }

        debug_assert_eq!(self.root.root_hash::<H>(), node);

        Ok(node)
    }

    /// fetch merkle path of key into cache
    /// cache: (height, key) -> node
    fn fetch_merkle_path(
        &self,
        key: &H256,
        cache: &mut BTreeMap<(u8, H256), (H256, u8)>,
    ) -> Result<()> {
        let mut node = self.root.node;
        loop {
            let branch_node = self
                .store
                .get_branch(&node)?
                .ok_or_else(|| Error::MissingBranch(node))?;
            let height = max(key.fork_height(branch_node.key()), branch_node.fork_height);
            let is_right = key.get_bit(height);
            let mut sibling_key = key.parent_path(height);
            if !is_right {
                // mark sibling's index, sibling on the right path.
                sibling_key.set_bit(height);
            };

            match branch_node.node_at(height) {
                NodeType::Pair(left, right) => {
                    if height > branch_node.fork_height {
                        cache
                            .entry((height, sibling_key))
                            .or_insert((node, branch_node.fork_height));
                        break;
                    } else {
                        let sibling;
                        if is_right {
                            if node == right {
                                break;
                            }
                            sibling = left;
                            node = right;
                        } else {
                            if node == left {
                                break;
                            }
                            sibling = right;
                            node = left;
                        }
                        cache.insert((height, sibling_key), (sibling, branch_node.fork_height));
                    }
                }
                NodeType::Single(node) => {
                    if key != branch_node.key() {
                        cache.insert((height, sibling_key), (node, branch_node.fork_height));
                    }
                    break;
                }
            }
        }

        Ok(())
    }

    /// Generate merkle proof
    pub fn merkle_proof(&self, mut keys: Vec<H256>) -> Result<MerkleProof> {
        if keys.is_empty() {
            return Err(Error::EmptyKeys);
        }

        // sort keys
        keys.sort_unstable();

        // fetch all merkle path
        let mut cache: BTreeMap<(u8, H256), (H256, u8)> = Default::default();
        if !self.is_empty() {
            for k in &keys {
                self.fetch_merkle_path(k, &mut cache)?;
            }
        }

        // (sibling_key, height)
        let mut proof: Vec<(H256, u8)> = Vec::with_capacity(EXPECTED_PATH_SIZE * keys.len());
        // key_index -> merkle path height
        let mut leaves_path: Vec<Vec<u8>> = Vec::with_capacity(keys.len());
        leaves_path.resize_with(keys.len(), Default::default);

        let keys_len = keys.len();
        // build merkle proofs from bottom to up
        // (key, height, key_index)
        let mut queue: VecDeque<(H256, u8, usize)> = keys
            .into_iter()
            .enumerate()
            .map(|(i, k)| (k, 0, i))
            .collect();

        while let Some((key, node_height, leaf_index)) = queue.pop_front() {
            if queue.is_empty() && cache.is_empty() {
                // tree only contains one leaf
                if leaves_path[leaf_index].is_empty() {
                    leaves_path[leaf_index].push(core::u8::MAX);
                }
                break;
            }
            // compute sibling key
            let mut sibling_key = key.parent_path(node_height);

            let is_right = key.get_bit(node_height);
            if is_right {
                // sibling on left
                sibling_key.clear_bit(node_height);
            } else {
                // sibling on right
                sibling_key.set_bit(node_height);
            }

            // merge with another leaf
            if Some((&sibling_key, &node_height))
                == queue
                    .front()
                    .map(|(sibling_key, height, _leaf_index)| (sibling_key, height))
            {
                // drop the sibling, mark sibling's merkle path
                let (_sibling_key, height, leaf_index) = queue.pop_front().unwrap();
                leaves_path[leaf_index].push(height);
            } else {
                match cache.remove(&(node_height, sibling_key)) {
                    Some((mut sibling, sibling_height)) => {
                        // align sibling to node_height
                        if sibling_height < node_height {
                            let node_key = sibling_key.parent_path(sibling_height);
                            let n_zeros = node_height - sibling_height;
                            sibling =
                                align_with_zeros::<H>(sibling_height, &node_key, &sibling, n_zeros);
                        }
                        // save first non-zero sibling's height for leaves
                        proof.push((sibling, node_height));
                    }
                    None => {
                        // skip zero siblings
                        if !is_right {
                            sibling_key.clear_bit(node_height);
                        }
                        if node_height == core::u8::MAX {
                            if leaves_path[leaf_index].is_empty() {
                                leaves_path[leaf_index].push(node_height);
                            }
                            break;
                        } else {
                            let parent_key = sibling_key;
                            queue.push_back((parent_key, node_height + 1, leaf_index));
                            continue;
                        }
                    }
                }
            }
            // find new non-zero sibling, append to leaf's path
            leaves_path[leaf_index].push(node_height);
            if node_height == core::u8::MAX {
                break;
            } else {
                // get parent_key, which k.get_bit(height) is false
                let parent_key = if is_right { sibling_key } else { key };
                queue.push_back((parent_key, node_height + 1, leaf_index));
            }
        }
        debug_assert_eq!(leaves_path.len(), keys_len);
        Ok(MerkleProof::new(leaves_path, proof))
    }
}
