use crate::{
    error::{Error, Result},
    merge::{merge, merge_zeros},
    merkle_proof::MerkleProof,
    traits::{Hasher, Store, Value},
    vec::Vec,
    EXPECTED_PATH_SIZE, H256, MAX_STACK_SIZE,
};
use core::cmp::Ordering;
use core::marker::PhantomData;
use std::collections::{BTreeMap, VecDeque};

/// The branch key
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct BranchKey {
    pub height: u8,
    pub node_key: H256,
}

impl BranchKey {
    pub fn new(height: u8, node_key: H256) -> BranchKey {
        BranchKey { height, node_key }
    }
}

impl PartialOrd for BranchKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for BranchKey {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.height.cmp(&other.height) {
            Ordering::Equal => self.node_key.cmp(&other.node_key),
            ordering => ordering,
        }
    }
}

/// A branch in the SMT
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct BranchNode {
    pub fork_height: u8,
    pub fork_key: H256,
    pub children: Children,
}

impl BranchNode {
    // get node at a specific height
    fn children_at_height(&self, height: u8) -> Children {
        match &self.children {
            Children::Pair(node, sibling) => {
                let is_right = self.fork_key.get_bit(height);
                if is_right {
                    Children::Pair(*sibling, *node)
                } else {
                    Children::Pair(*node, *sibling)
                }
            }
            other => other.clone(),
        }
    }
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Children {
    WithZero(H256, u8),
    Pair(H256, H256),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MerkleNode {
    Sibling {
        merge_height: u8,
        sibling: H256,
    },
    Zeros {
        merge_height: u8,
        fork_key: H256,
        sibling: H256,
        n_zeros: u8,
    },
}

impl MerkleNode {
    pub fn merge_height(&self) -> u8 {
        match self {
            Self::Sibling { merge_height, .. } => *merge_height,
            Self::Zeros { merge_height, .. } => *merge_height,
        }
    }
}

/// Sparse merkle tree
#[derive(Default, Debug)]
pub struct SparseMerkleTree<H, V, S> {
    store: S,
    root: H256,
    phantom: PhantomData<(H, V)>,
}

impl<H: Hasher + Default, V: Value, S: Store<V>> SparseMerkleTree<H, V, S> {
    /// Build a merkle tree from root and store
    pub fn new(root: H256, store: S) -> SparseMerkleTree<H, V, S> {
        SparseMerkleTree {
            root,
            store,
            phantom: PhantomData,
        }
    }

    /// Merkle root
    pub fn root(&self) -> &H256 {
        &self.root
    }

    /// Check empty of the tree
    pub fn is_empty(&self) -> bool {
        self.root.is_zero()
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

    /// Update a leaf, return new merkle root
    /// set to zero value to delete a key
    pub fn update(&mut self, key: H256, value: V) -> Result<&H256> {
        let mut path = Vec::new();
        if !self.is_empty() {
            // traveling the tree from top to bottom
            // 1. delete merkle path node
            // 2. push non-zero node into path vector
            // TODO refactor to support delete branch
            let mut removed = Vec::with_capacity(EXPECTED_PATH_SIZE);
            self.travel_merkle_path(key, |parent, merkle_node| {
                removed.push(parent);
                path.push(merkle_node);
            })?;
            for node in removed {
                self.store.remove_branch(&node)?;
            }
        }

        // compute and store new leaf
        let mut node = value.to_h256();
        // notice when value is zero the leaf is deleted, so we do not need to store it
        // if !node.is_zero() {
        self.store.insert_leaf(key, value)?;

        // // build at least one branch for leaf
        // self.store.insert_branch(
        //     node,
        //     BranchNode {
        //         key,
        //         fork_height: 0,
        //         node_type: NodeType::Single(node),
        //     },
        // )?;
        // }

        // recompute the tree from bottom to top
        let mut current_height = 0;

        // dbg!(&path);

        let merge_zeros_to_height = |current_height, height, node: H256| -> (H256, BranchNode) {
            let parent_path = key.parent_path(current_height);
            assert!(height > current_height);
            let n_zeros = height - current_height;
            let parent_node = merge_zeros::<H>(current_height, &parent_path, &node, n_zeros);

            // insert branch
            let branch = BranchNode {
                fork_key: key,
                fork_height: height,
                children: Children::WithZero(node, n_zeros),
            };

            dbg!("merge with n zeros", node, n_zeros, &parent_node);
            (parent_node, branch)
        };

        if path.is_empty() {
            let merge_height = u8::MAX;
            // node
            let (parent_node, branch) = merge_zeros_to_height(current_height, merge_height, node);
            self.store.insert_branch(parent_node, branch)?;
            node = parent_node;
            current_height = merge_height;
            // // mock sibling
            // let (sibling, branch) = merge_zeros_to_height(0, merge_height, H256::zero());
            // self.store.insert_branch(sibling, branch)?;
            // // merge two children
            // let is_right = key.get_bit(current_height);
            // let node_key = key.parent_path(current_height);
            // let parent_node = if is_right {
            //     // dbg!("merge ", current_height, node_key, &sibling, &node);
            //     merge::<H>(current_height, &node_key, &sibling, &node)
            // } else {
            //     // dbg!("merge ", current_height, node_key, &node, &sibling);
            //     merge::<H>(current_height, &node_key, &node, &sibling)
            // };

            // debug_assert!(!node.is_zero(), "shouldn't be zero");

            // // node is exists
            // let branch = BranchNode {
            //     fork_key: key,
            //     fork_height: merge_height,
            //     children: Children::Pair(node, sibling),
            // };
            // // dbg!("insert", &branch);
            // self.store.insert_branch(parent_node, branch)?;
            // node = parent_node;
            // current_height = u8::MAX;
        }

        // merge siblings
        for merkle_node in path.into_iter().rev() {
            // align two children to same height
            let (merge_height, sibling) = match merkle_node {
                MerkleNode::Sibling {
                    merge_height,
                    sibling,
                } => {
                    // debug_assert!(
                    //     !sibling.is_zero(),
                    //     "path should only contains non-zero nodes"
                    // );
                    // debug_assert!(
                    //     current_height == merge_height,
                    //     "sibling height should be == current height"
                    // );

                    // align to the height of sibling if current height is lower
                    if current_height < merge_height {
                        let (parent_node, branch) =
                            merge_zeros_to_height(current_height, merge_height, node);
                        self.store.insert_branch(parent_node, branch)?;
                        node = parent_node;
                        current_height = merge_height;
                    }

                    (merge_height, sibling)
                }
                MerkleNode::Zeros {
                    merge_height: zero_node_merge_height,
                    fork_key,
                    mut sibling,
                    n_zeros,
                } => {
                    // debug_assert!(
                    //     current_height <= merge_height,
                    //     "sibling height should be <= current height"
                    // );

                    // calculate merge point
                    let merge_height = key.fork_height(&fork_key);

                    // align node to the merge point
                    if current_height < merge_height {
                        let (parent_node, branch) =
                            merge_zeros_to_height(current_height, merge_height, node);
                        self.store.insert_branch(parent_node, branch)?;
                        node = parent_node;
                        current_height = merge_height;
                    }

                    // align sibling to the merge point
                    let sibling_height = zero_node_merge_height - n_zeros;
                    if sibling_height < merge_height {
                        let (parent_node, branch) =
                            merge_zeros_to_height(sibling_height, merge_height, sibling);
                        self.store.insert_branch(parent_node, branch)?;
                        sibling = parent_node;
                    }

                    (merge_height, sibling)
                }
            };

            // merge two children
            let is_right = key.get_bit(current_height);
            let node_key = key.parent_path(current_height);
            let parent_node = if is_right {
                dbg!("merge ", current_height, node_key, &sibling, &node);
                merge::<H>(current_height, &node_key, &sibling, &node)
            } else {
                dbg!("merge ", current_height, node_key, &node, &sibling);
                merge::<H>(current_height, &node_key, &node, &sibling)
            };

            debug_assert!(!node.is_zero(), "shouldn't be zero");
            // node is exists
            let branch = BranchNode {
                fork_key: key,
                fork_height: merge_height,
                children: Children::Pair(node, sibling),
            };
            // dbg!("insert", &branch);
            self.store.insert_branch(parent_node, branch)?;
            node = parent_node;
            if merge_height == 255 {
                current_height = 255;
                break;
            }
            current_height = merge_height + 1;
        }

        if current_height < u8::MAX {
            let merge_height = u8::MAX;
            let (parent_node, branch) = merge_zeros_to_height(current_height, merge_height, node);
            self.store.insert_branch(parent_node, branch)?;
            node = parent_node;
            current_height = merge_height;
        }

        debug_assert_eq!(current_height, 255, "merge to root");
        // debug_assert!(path.is_empty(), "pop all merkle path");

        // // merge with zeros to the top
        // if current_height < 255 {
        //     let node_key = key.parent_path(current_height);
        //     let n_zeros = 255 - current_height;
        //     let parent_node = merge_zeros::<H>(current_height, &node_key, &node, n_zeros);
        //     current_height = 255;

        //     // insert branch
        //     let branch_node = BranchNode {
        //         fork_key: key,
        //         fork_height: current_height,
        //         children: Children::WithZero(node, n_zeros),
        //     };
        //     self.store.insert_branch(parent_node, branch_node)?;
        //     node = parent_node;
        // }
        self.root = node;
        Ok(&self.root)
    }

    /// Get value of a leaf
    /// return zero value if leaf not exists
    pub fn get(&self, key: &H256) -> Result<V> {
        if self.is_empty() {
            return Ok(V::zero());
        }
        Ok(self.store.get_leaf(key)?.unwrap_or_else(V::zero))
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

    /// travel merkle path
    /// return (current_height, node)
    fn travel_merkle_path<F: FnMut(H256, MerkleNode)>(&self, key: H256, mut f: F) -> Result<()> {
        let mut node = self.root;
        let mut current_height = u8::MAX;
        while current_height > 0 {
            // dbg!("wtf");
            let branch = self
                .store
                .get_branch(&node)?
                .ok_or_else(|| Error::MissingBranch(current_height, key))?;

            let parent = node;
            // get highest merge height of the branch node
            let merge_height =
                core::cmp::max(key.fork_height(&branch.fork_key), branch.fork_height);
            // fetch the childrens by key info
            match branch.children_at_height(merge_height) {
                Children::Pair(left, right) => {
                    if merge_height > branch.fork_height {
                        // know fork_height should through merge zeros to 254 height. thus, merge_height should never > fork_height
                        unreachable!();
                        // // the merge height is higher than node, so we do not need to remove node's branch
                        // path.push((merge_height, node));
                        // break;
                    } else {
                        let is_right = key.get_bit(merge_height);
                        let sibling;
                        if is_right {
                            node = right;
                            // path.push((merge_height, left));
                            sibling = left;
                        } else {
                            node = left;
                            // path.push((merge_height, right));
                            sibling = right;
                        }
                        f(
                            parent,
                            MerkleNode::Sibling {
                                merge_height,
                                sibling,
                            },
                        );
                    }
                    current_height = merge_height;
                    // dbg!(current_height);
                }
                Children::WithZero(origin_node, n_zeros) => {
                    // dbg!(&origin_node);
                    // dbg!(merge_height, key, branch.fork_key);
                    if merge_height == 0 && key == branch.fork_key {
                        // dbg!("skip leaf it self");
                        break;
                    }
                    // if merge_height != 0 || key != branch.fork_key {
                    // path.push((height, node));
                    let fork_key = key.parent_path(merge_height - n_zeros);
                    f(
                        parent,
                        MerkleNode::Zeros {
                            merge_height,
                            sibling: origin_node,
                            fork_key,
                            n_zeros,
                        },
                    );
                    // dbg!(current_height, merge_height);
                    current_height = merge_height - n_zeros;
                    node = origin_node;
                    // dbg!(current_height, merge_height, n_zeros);
                }
            }

            if merge_height == 0 {
                break;
            }
        }

        Ok(())
    }

    /// fetch non-zero merkle path of a key into cache
    /// cache: (height, key) -> node
    fn fetch_merkle_path(
        &self,
        key: &H256,
        cache: &mut BTreeMap<(u8, H256), MerkleNode>,
    ) -> Result<()> {
        // travel tree from top to bottom
        self.travel_merkle_path(*key, |_parent, merkle_node| {
            let height = match merkle_node {
                MerkleNode::Sibling { merge_height, .. } => merge_height,
                MerkleNode::Zeros {
                    merge_height,
                    n_zeros,
                    ..
                } => {
                    return;
                }
            };
            // let height = match merkle_node {
            //     MerkleNode::Sibling { merge_height, .. } => merge_height,
            //     MerkleNode::Zeros {
            //         merge_height,
            //         n_zeros,
            //         ..
            //     } => merge_height - n_zeros,
            // };
            let sibling_path = key.parent_path(height);
            // debug_assert!(
            //     cache.contains_key(&(merge_height, sibling_path)),
            //     "shouldn't duplicate"
            // );
            cache.entry((height, sibling_path)).or_insert(merkle_node);
        })?;
        Ok(())
    }

    /// Generate merkle proof
    pub fn merkle_proof(&self, mut keys: Vec<H256>) -> Result<MerkleProof> {
        if keys.is_empty() {
            return Err(Error::EmptyKeys);
        }

        // sort keys
        keys.sort_unstable();

        // dbg!(keys.len());

        // fetch all merkle path
        let mut cache: BTreeMap<(u8, H256), MerkleNode> = Default::default();
        if !self.is_empty() {
            for k in &keys {
                self.fetch_merkle_path(k, &mut cache)?;
            }
        }
        // dbg!(&cache);

        // (node, height)
        let mut proof: Vec<MerkleNode> = Vec::with_capacity(EXPECTED_PATH_SIZE * keys.len());
        // key_index -> merkle path height
        let mut leaves_path: Vec<Vec<u8>> = Vec::with_capacity(keys.len());
        leaves_path.resize_with(keys.len(), Default::default);

        let keys_len = keys.len();
        // build merkle proofs from bottom to up
        // (key, height, key_index)
        let mut queue: VecDeque<(H256, u8, usize)> = keys
            .into_iter()
            .enumerate()
            .map(|(i, k)| (k.parent_path(0), 0, i))
            .collect();

        // dbg!(&queue);

        let mut current_height = 0u8;
        while let Some((key, height, leaf_index)) = queue.pop_front() {
            // dbg!("pop leaf", leaf_index);
            // dbg!(key, height, leaf_index);
            if queue.is_empty() && cache.is_empty() {
                // tree only contains one leaf
                // if leaves_path[leaf_index].is_empty() {
                //     leaves_path[leaf_index].push(core::u8::MAX);
                // }
                break;
            }
            // compute sibling key
            let mut sibling_key = key.parent_path(height);

            // let is_right = key.get_bit(height);
            // if is_right {
            //     // sibling on left
            //     sibling_key.clear_bit(height);
            // } else {
            //     // sibling on right
            //     sibling_key.set_bit(height);
            // }
            if Some((&sibling_key, &height))
                == queue
                    .front()
                    .map(|(sibling_key, height, _leaf_index)| (sibling_key, height))
            {
                assert_eq!(current_height, 0);
                // drop the sibling, mark sibling's merkle path
                let (_sibling_key, height, _leaf_index) = queue.pop_front().unwrap();
                // delete duplicated sibling from cache
                // dbg!("delete sibling", (height, sibling_key));
                // cache.remove(&(height, sibling_key));
                // dbg!("merge with sibling", queue.len(), leaf_index);
                leaves_path[leaf_index].push(height);
                // current_height += 1;
                let parent_key = key.parent_path(height);
                queue.push_back((parent_key, height + 1, leaf_index));
            } else {
                // dbg!((height, sibling_key, leaf_index));
                // dbg!(&cache);
                match cache.remove(&(height, sibling_key)) {
                    Some(merkle_node) => {
                        let merge_height = match merkle_node {
                            MerkleNode::Sibling { merge_height, .. } => merge_height,
                            MerkleNode::Zeros { fork_key, .. } => key.fork_height(&fork_key),
                        };
                        leaves_path[leaf_index].push(merge_height);
                        current_height = merge_height;
                        // debug_assert_eq!(current_height, merkle_node.merge_height());
                        // current_height = merkle_node.merge_height() + 1;
                        // save first non-zero sibling's height for leaves
                        proof.push(merkle_node);
                    }
                    None => {
                        // dbg!(&cache);
                        // a leaf either merge with a zero or a non-zero, both we generate a sibling for it
                        // unreachable!();
                        // skip zero siblings
                        // if !is_right {
                        //     sibling_key.clear_bit(height);
                        // }
                        if height == core::u8::MAX {
                            if leaves_path[leaf_index].is_empty() {
                                leaves_path[leaf_index].push(height);
                            }
                            break;
                        } else {
                            break;
                            // // if the key not in the cache, means our sibling is zero
                            // // so we just pushing back
                            // let parent_key = sibling_key;
                            // queue.push_back((parent_key, height + 1, leaf_index));
                            // continue;
                        };
                    }
                }
                dbg!("push leaf path", leaf_index, height);
                // find new non-zero sibling, append to leaf's path
                // leaves_path[leaf_index].push(height);
                if height == core::u8::MAX {
                    break;
                }
                //  else {
                //     let next_height = height + 1;
                //     // get parent_key, which k.get_bit(height) is false
                //     let parent_key = key.parent_path(next_height);
                //     queue.push_back((parent_key, next_height, leaf_index));
                //     current_height = next_height;
                // }
            }
        }

        // merge with zeros if not match MAX
        if current_height < core::u8::MAX {
            leaves_path[0].push(core::u8::MAX);
        }
        // assert_eq!(current_height, core::u8::MAX);
        debug_assert_eq!(leaves_path.len(), keys_len);
        Ok(MerkleProof::new(leaves_path, proof))
    }
}
