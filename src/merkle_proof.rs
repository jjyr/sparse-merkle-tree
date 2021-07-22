use std::collections::{BTreeMap, VecDeque};

use crate::{
    error::{Error, Result},
    merge::{merge, merge_zeros},
    traits::Hasher,
    tree::MerkleNode,
    vec::Vec,
    H256, MAX_STACK_SIZE,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MerkleProof {
    // leaves merge height map
    leaves_merge_height: Vec<Vec<u8>>,
    // needed sibling node hash
    merkle_path: Vec<MerkleNode>,
}

impl MerkleProof {
    /// Create MerkleProof
    pub fn new(leaves_merge_height: Vec<Vec<u8>>, merkle_path: Vec<MerkleNode>) -> Self {
        MerkleProof {
            leaves_merge_height,
            merkle_path,
        }
    }

    /// Destruct the structure, useful for serialization
    pub fn take(self) -> (Vec<Vec<u8>>, Vec<MerkleNode>) {
        let MerkleProof {
            leaves_merge_height,
            merkle_path,
        } = self;
        (leaves_merge_height, merkle_path)
    }

    /// number of leaves required by this merkle proof
    pub fn leaves_count(&self) -> usize {
        self.leaves_merge_height.len()
    }

    /// return the leaves_merge_height vector
    pub fn leaves_merge_height(&self) -> &Vec<Vec<u8>> {
        &self.leaves_merge_height
    }

    /// return sibling node hashes
    pub fn merkle_path(&self) -> &Vec<MerkleNode> {
        &self.merkle_path
    }

    // pub fn compile(self, mut leaves: Vec<(H256, H256)>) -> Result<CompiledMerkleProof> {
    //     if leaves.is_empty() {
    //         return Err(Error::EmptyKeys);
    //     } else if leaves.len() != self.leaves_count() {
    //         return Err(Error::IncorrectNumberOfLeaves {
    //             expected: self.leaves_count(),
    //             actual: leaves.len(),
    //         });
    //     }
    //     // sort leaves
    //     leaves.sort_unstable_by_key(|(k, _v)| *k);

    //     let (leaves_merge_height, merkle_path) = self.take();

    //     let mut proof: Vec<u8> = Vec::with_capacity(merkle_path.len() * 33 + leaves.len());
    //     let mut stack_fork_height = [0u8; MAX_STACK_SIZE]; // store fork height
    //     let mut stack_top = 0;
    //     let mut leaf_index = 0;
    //     let mut merkle_path_index = 0;
    //     while leaf_index < leaves.len() {
    //         let (leaf_key, _value) = leaves[leaf_index];
    //         let fork_height = if leaf_index + 1 < leaves.len() {
    //             leaf_key.fork_height(&leaves[leaf_index + 1].0)
    //         } else {
    //             core::u8::MAX
    //         };
    //         proof.push(0x4C);
    //         let mut zero_count = 0u16;
    //         for height in 0..=fork_height {
    //             if height == fork_height && leaf_index + 1 < leaves.len() {
    //                 // If it's not final round, we don't need to merge to root (height=255)
    //                 break;
    //             }
    //             let (op_code_opt, sibling_node_opt) =
    //                 if stack_top > 0 && stack_fork_height[stack_top - 1] == height {
    //                     stack_top -= 1;
    //                     (Some(0x48), None)
    //                 } else if leaves_bitmap[leaf_index].get_bit(height) {
    //                     if merkle_path_index >= merkle_path.len() {
    //                         return Err(Error::CorruptedProof);
    //                     }
    //                     let node_hash = merkle_path[merkle_path_index];
    //                     merkle_path_index += 1;
    //                     (Some(0x50), Some(node_hash))
    //                 } else {
    //                     zero_count += 1;
    //                     if zero_count > 256 {
    //                         return Err(Error::CorruptedProof);
    //                     }
    //                     (None, None)
    //                 };
    //             if let Some(op_code) = op_code_opt {
    //                 if zero_count > 0 {
    //                     let n = if zero_count == 256 {
    //                         0
    //                     } else {
    //                         zero_count as u8
    //                     };
    //                     proof.push(0x4F);
    //                     proof.push(n);
    //                     zero_count = 0;
    //                 }
    //                 proof.push(op_code);
    //             }
    //             if let Some(hash) = sibling_node_opt {
    //                 proof.extend(hash.as_slice());
    //             }
    //         }
    //         if zero_count > 0 {
    //             let n = if zero_count == 256 {
    //                 0
    //             } else {
    //                 zero_count as u8
    //             };
    //             proof.push(0x4F);
    //             proof.push(n);
    //         }
    //         debug_assert!(stack_top < MAX_STACK_SIZE);
    //         stack_fork_height[stack_top] = fork_height;
    //         stack_top += 1;
    //         leaf_index += 1;
    //     }

    //     if stack_top != 1 {
    //         return Err(Error::CorruptedProof);
    //     }
    //     if leaf_index != leaves.len() {
    //         return Err(Error::CorruptedProof);
    //     }
    //     if merkle_path_index != merkle_path.len() {
    //         return Err(Error::CorruptedProof);
    //     }
    //     Ok(CompiledMerkleProof(proof))
    // }

    // /// Compute root from proof
    // /// leaves: a vector of (key, value)
    // ///
    // /// return EmptyProof error when proof is empty
    // /// return CorruptedProof error when proof is invalid
    // pub fn compute_root<H: Hasher + Default>(self, mut leaves: Vec<(H256, H256)>) -> Result<H256> {
    //     if leaves.is_empty() {
    //         return Err(Error::EmptyKeys);
    //     } else if leaves.len() != self.leaves_count() {
    //         return Err(Error::IncorrectNumberOfLeaves {
    //             expected: self.leaves_count(),
    //             actual: leaves.len(),
    //         });
    //     }
    //     // sort leaves
    //     leaves.sort_unstable_by_key(|(k, _v)| *k);

    //     let (leaves_merge_height, merkle_path) = self.take();

    //     let mut stack_fork_height = [0u8; MAX_STACK_SIZE]; // store fork height
    //     let mut stack = [H256::zero(); MAX_STACK_SIZE]; // store node hash
    //     let mut stack_top = 0;
    //     let mut leaf_index = 0;
    //     let mut merkle_path_index = 0;
    //     while leaf_index < leaves.len() {
    //         let (leaf_key, value) = leaves[leaf_index];
    //         let fork_height = if leaf_index + 1 < leaves.len() {
    //             leaf_key.fork_height(&leaves[leaf_index + 1].0)
    //         } else {
    //             core::u8::MAX
    //         };
    //         let mut current_node = value;
    //         for height in 0..=fork_height {
    //             if height == fork_height && leaf_index + 1 < leaves.len() {
    //                 // If it's not final round, we don't need to merge to root (height=255)
    //                 break;
    //             }
    //             let parent_key = leaf_key.parent_path(height);
    //             let is_right = leaf_key.is_right(height);
    //             let sibling_node = if stack_top > 0 && stack_fork_height[stack_top - 1] == height {
    //                 let node_hash = stack[stack_top - 1];
    //                 stack_top -= 1;
    //                 node_hash
    //             } else if leaves_bitmap[leaf_index].get_bit(height) {
    //                 if merkle_path_index >= merkle_path.len() {
    //                     return Err(Error::CorruptedProof);
    //                 }
    //                 let node_hash = merkle_path[merkle_path_index];
    //                 merkle_path_index += 1;
    //                 node_hash
    //             } else {
    //                 H256::zero()
    //             };
    //             let (left, right) = if is_right {
    //                 (sibling_node, current_node)
    //             } else {
    //                 (current_node, sibling_node)
    //             };
    //             current_node = merge::<H>(height, &parent_key, &left, &right);
    //         }
    //         debug_assert!(stack_top < MAX_STACK_SIZE);
    //         stack_fork_height[stack_top] = fork_height;
    //         stack[stack_top] = current_node;
    //         stack_top += 1;
    //         leaf_index += 1;
    //     }

    //     if stack_top != 1 {
    //         return Err(Error::CorruptedProof);
    //     }
    //     if leaf_index != leaves.len() {
    //         return Err(Error::CorruptedProof);
    //     }
    //     if merkle_path_index != merkle_path.len() {
    //         return Err(Error::CorruptedProof);
    //     }
    //     Ok(stack[0])
    // }

    /// Compute root from proof
    /// leaves: a vector of (key, value)
    ///
    /// return EmptyProof error when proof is empty
    /// return CorruptedProof error when proof is invalid
    pub fn compute_root<H: Hasher + Default>(self, mut leaves: Vec<(H256, H256)>) -> Result<H256> {
        if leaves.is_empty() {
            return Err(Error::EmptyKeys);
        } else if leaves.len() != self.leaves_count() {
            return Err(Error::IncorrectNumberOfLeaves {
                expected: self.leaves_count(),
                actual: leaves.len(),
            });
        }

        let (leaves_path, proof) = self.take();
        let mut leaves_path: Vec<VecDeque<_>> = leaves_path.into_iter().map(Into::into).collect();
        let mut proof: VecDeque<_> = proof.into();

        // sort leaves
        leaves.sort_unstable_by_key(|(k, _v)| *k);
        // tree_buf: (height, key) -> (key_index, node)
        let mut tree_buf: BTreeMap<_, _> = leaves
            .into_iter()
            .enumerate()
            .map(|(i, (k, v))| ((0, k), (i, v)))
            .collect();
        // rebuild the tree from bottom to top
        while !tree_buf.is_empty() {
            // pop_front from tree_buf, the API is unstable
            let (&(mut height, key), &(leaf_index, node)) = tree_buf.iter().next().unwrap();
            tree_buf.remove(&(height, key));

            if proof.is_empty() && tree_buf.is_empty() {
                // merge to height
                if height < u8::MAX {
                    let n_zeros = u8::MAX - height;
                    let node_key = key.parent_path(height);
                    dbg!(height, node_key, node, n_zeros);
                    let node = merge_zeros::<H>(height, &node_key, &node, n_zeros);
                    return Ok(node);
                }
                return Ok(node);
            }

            let parent_key = key.parent_path(height);

            let mut sibling_key = key.parent_path(height);
            if !key.get_bit(height) {
                sibling_key.set_bit(height)
            }
            let parent;
            if Some(&(height, sibling_key)) == tree_buf.keys().next() {
                // merge with siblings in the leaves
                let (_leaf_index, sibling) = tree_buf
                    .remove(&(height, sibling_key))
                    .expect("pop sibling");
                // (sibling, height)
                // skip zero merkle path

                dbg!("merge with sibling", height, parent_key, node, sibling);
                parent = if key.get_bit(height) {
                    merge::<H>(height, &parent_key, &sibling, &node)
                } else {
                    merge::<H>(height, &parent_key, &node, &sibling)
                };
                // dbg!(&parent);
                let next_height = height + 1;
                let parent_key = key.parent_path(next_height);
                // two leaves merged, so the height is still zero
                // here is a tricky point, 0 represent the lowest branch in SMT.
                // but a leaf get merged, we also use 0 to represent a branch for leaf, it should be -1 actually.
                tree_buf.insert((next_height, parent_key), (leaf_index, parent));
            } else {
                // merge with merkle siblings

                // let merge_height = leaves_path[leaf_index].front().copied().unwrap_or(height);
                // let merge_height = leaves_path[leaf_index]
                //     .front()
                //     .copied()
                //     .ok_or(Error::CorruptedProof)?;
                let merge_height = height;
                // TODO can we remove leaves_path from proof?
                assert_eq!(merge_height, height);
                // if height != merge_height {
                //     let parent_key = key.copy_bits(merge_height);
                //     // skip zeros
                //     tree_buf.insert((merge_height, parent_key), (leaf_index, node));
                //     continue;
                // }
                // dbg!("pop proof");
                match proof.pop_front().ok_or(Error::CorruptedProof)? {
                    MerkleNode::Sibling {
                        merge_height,
                        sibling,
                    } => {
                        assert_eq!(height, merge_height);

                        // dbg!("merge merkle sibling", merge_height);
                        parent = if key.get_bit(height) {
                            merge::<H>(height, &parent_key, &sibling, &node)
                        } else {
                            merge::<H>(height, &parent_key, &node, &sibling)
                        };
                        tree_buf.insert((height + 1, parent_key), (leaf_index, parent));
                    }
                    MerkleNode::Zeros {
                        merge_height,
                        n_zeros,
                        fork_key,
                        sibling,
                    } => {
                        // dbg!("merge zeros", merge_height, n_zeros);
                        assert_eq!(height, merge_height);
                        parent = merge_zeros::<H>(height, &parent_key, &node, n_zeros);
                        // dbg!(height, n_zeros);
                        tree_buf.insert((height + n_zeros, parent_key), (leaf_index, parent));
                    }
                }
            }

            if height == core::u8::MAX {
                if proof.is_empty() {
                    return Ok(parent);
                } else {
                    return Err(Error::CorruptedProof);
                }
            } else {
                // dbg!("pop leave height", leaf_index);
                // leaves_path[leaf_index].pop_front();
                // tree_buf.insert((height + 1, parent_key), (leaf_index, parent));
            }
        }

        Err(Error::CorruptedProof)
    }

    /// Verify merkle proof
    /// see compute_root_from_proof
    pub fn verify<H: Hasher + Default>(
        self,
        root: &H256,
        leaves: Vec<(H256, H256)>,
    ) -> Result<bool> {
        let calculated_root = self.compute_root::<H>(leaves)?;
        Ok(&calculated_root == root)
    }
}

/// An structure optimized for verify merkle proof
#[derive(Debug, Clone)]
pub struct CompiledMerkleProof(pub Vec<u8>);

impl CompiledMerkleProof {
    pub fn compute_root<H: Hasher + Default>(&self, mut leaves: Vec<(H256, H256)>) -> Result<H256> {
        leaves.sort_unstable_by_key(|(k, _v)| *k);
        let mut program_index = 0;
        let mut leaf_index = 0;
        let mut stack: Vec<(u16, H256, H256)> = Vec::new();
        while program_index < self.0.len() {
            let code = self.0[program_index];
            program_index += 1;
            match code {
                // L : push leaf value
                0x4C => {
                    if leaf_index >= leaves.len() {
                        return Err(Error::CorruptedStack);
                    }
                    let (k, v) = leaves[leaf_index];
                    stack.push((0, k, v));
                    leaf_index += 1;
                }
                // P : hash stack top item with sibling node in proof
                0x50 => {
                    if stack.is_empty() {
                        return Err(Error::CorruptedStack);
                    }
                    if program_index + 32 > self.0.len() {
                        return Err(Error::CorruptedProof);
                    }
                    let mut data = [0u8; 32];
                    data.copy_from_slice(&self.0[program_index..program_index + 32]);
                    program_index += 32;
                    let sibling_node = H256::from(data);
                    let (height_u16, key, value) = stack.pop().unwrap();
                    if height_u16 > 255 {
                        return Err(Error::CorruptedProof);
                    }
                    let height = height_u16 as u8;
                    let parent_key = key.parent_path(height);
                    let parent = if key.get_bit(height) {
                        merge::<H>(height, &parent_key, &sibling_node, &value)
                    } else {
                        merge::<H>(height, &parent_key, &value, &sibling_node)
                    };
                    stack.push((height_u16 + 1, parent_key, parent));
                }
                // H : pop 2 items in stack hash them then push the result
                0x48 => {
                    if stack.len() < 2 {
                        return Err(Error::CorruptedStack);
                    }
                    let (height_b, key_b, value_b) = stack.pop().unwrap();
                    let (height_a, key_a, value_a) = stack.pop().unwrap();
                    if height_a != height_b {
                        return Err(Error::CorruptedProof);
                    }
                    if height_a > 255 {
                        return Err(Error::CorruptedProof);
                    }
                    let height_u16 = height_a;
                    let height = height_u16 as u8;
                    let parent_key_a = key_a.parent_path(height);
                    let parent_key_b = key_b.parent_path(height);
                    if parent_key_a != parent_key_b {
                        return Err(Error::CorruptedProof);
                    }
                    let parent = if key_a.get_bit(height) {
                        merge::<H>(height, &parent_key_a, &value_b, &value_a)
                    } else {
                        merge::<H>(height, &parent_key_a, &value_a, &value_b)
                    };
                    stack.push((height_u16 + 1, parent_key_a, parent));
                }
                // O : hash stack top item with n zero values
                0x4F => {
                    if stack.is_empty() {
                        return Err(Error::CorruptedStack);
                    }
                    if program_index >= self.0.len() {
                        return Err(Error::CorruptedProof);
                    }
                    let n = self.0[program_index];
                    program_index += 1;
                    let zero_count: u16 = if n == 0 { 256 } else { n as u16 };
                    let (base_height, key, mut value) = stack.pop().unwrap();
                    if base_height > 255 {
                        return Err(Error::CorruptedProof);
                    }
                    let mut parent_key = key;
                    let mut height_u16 = base_height;
                    for idx in 0..zero_count {
                        if base_height + idx > 255 {
                            return Err(Error::CorruptedProof);
                        }
                        height_u16 = base_height + idx;
                        let height = height_u16 as u8;
                        parent_key = key.parent_path(height);
                        value = if key.get_bit(height) {
                            merge::<H>(height, &parent_key, &H256::zero(), &value)
                        } else {
                            merge::<H>(height, &parent_key, &value, &H256::zero())
                        };
                    }
                    stack.push((height_u16 + 1, parent_key, value));
                }
                _ => return Err(Error::InvalidCode(code)),
            }
            debug_assert!(stack.len() <= MAX_STACK_SIZE);
        }
        if stack.len() != 1 {
            return Err(Error::CorruptedStack);
        }
        if stack[0].0 != 256 {
            return Err(Error::CorruptedProof);
        }
        if leaf_index != leaves.len() {
            return Err(Error::CorruptedProof);
        }
        Ok(stack[0].2)
    }

    pub fn verify<H: Hasher + Default>(
        &self,
        root: &H256,
        leaves: Vec<(H256, H256)>,
    ) -> Result<bool> {
        let calculated_root = self.compute_root::<H>(leaves)?;
        Ok(&calculated_root == root)
    }
}

impl Into<Vec<u8>> for CompiledMerkleProof {
    fn into(self) -> Vec<u8> {
        self.0
    }
}
