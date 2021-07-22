use std::collections::{BTreeMap, VecDeque};

use crate::{
    error::{Error, Result},
    merge::{align_with_zeros, hash_leaf, merge},
    traits::Hasher,
    vec::Vec,
    H256, MAX_STACK_SIZE,
};

// #[derive(Debug, Clone, PartialEq, Eq)]
// pub struct MerkleProof {
//     // leaf bitmap, bitmap.get_bit(height) is true means there need a non zero sibling in this height
//     leaves_bitmap: Vec<H256>,
//     // needed sibling node hash
//     merkle_path: Vec<H256>,
// }

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MerkleProof {
    leaves_path: Vec<Vec<u8>>,
    proof: Vec<(H256, u8)>,
}

impl MerkleProof {
    /// Create MerkleProof
    /// leaves_path: contains height of non-zero siblings
    /// proof: contains merkle path for each leaves it's height
    pub fn new(leaves_path: Vec<Vec<u8>>, proof: Vec<(H256, u8)>) -> Self {
        MerkleProof { leaves_path, proof }
    }

    /// Destruct the structure, useful for serialization
    pub fn take(self) -> (Vec<Vec<u8>>, Vec<(H256, u8)>) {
        let MerkleProof { leaves_path, proof } = self;
        (leaves_path, proof)
    }

    /// number of leaves required by this merkle proof
    pub fn leaves_count(&self) -> usize {
        self.leaves_path.len()
    }

    /// return the inner leaves_path vector
    pub fn leaves_path(&self) -> &Vec<Vec<u8>> {
        &self.leaves_path
    }

    /// return proof merkle path
    pub fn proof(&self) -> &Vec<(H256, u8)> {
        &self.proof
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

    //     let (leaves_bitmap, merkle_path) = self.take();

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
            .map(|(i, (k, v))| ((0, k), (i, hash_leaf::<H>(&k, &v))))
            .collect();

        // rebuild the tree from bottom to top
        while !tree_buf.is_empty() {
            // pop_front from tree_buf, the API is unstable
            let (&(mut node_height, key), &(leaf_index, mut node)) =
                tree_buf.iter().next().unwrap();
            tree_buf.remove(&(node_height, key));

            if proof.is_empty() && tree_buf.is_empty() {
                return Ok(node);
            }

            let mut sibling_key = key.parent_path(node_height);
            if !key.get_bit(node_height) {
                sibling_key.set_bit(node_height)
            }

            let (sibling, merge_height) =
                if Some(&(node_height, sibling_key)) == tree_buf.keys().next() {
                    let (_leaf_index, sibling) = tree_buf
                        .remove(&(node_height, sibling_key))
                        .expect("pop sibling");
                    (sibling, node_height)
                } else {
                    let merge_height = leaves_path[leaf_index]
                        .front()
                        .copied()
                        .unwrap_or(node_height);
                    if node_height != merge_height {
                        let parent_key = key.copy_bits(merge_height);
                        // skip zeros
                        tree_buf.insert((merge_height, parent_key), (leaf_index, node));
                        continue;
                    }
                    let (node, height) = proof.pop_front().ok_or(Error::CorruptedProof)?;
                    (node, height)
                };

            // align node to merge_height
            if node_height < merge_height {
                let node_key = key.parent_path(node_height);
                let n_zeros = merge_height - node_height;
                node = align_with_zeros::<H>(node_height, &node_key, &node, n_zeros);
                node_height = merge_height;
            }

            let is_right = key.get_bit(merge_height);
            let node_key = key.parent_path(merge_height);
            let (lhs, rhs) = if is_right {
                (sibling, node)
            } else {
                (node, sibling)
            };
            let parent = merge::<H>(merge_height, &node_key, &lhs, &rhs);
            // // skip zero merkle path
            // let parent_key = key.parent_path(height);

            // let parent = if key.get_bit(height) {
            //     merge::<H>(&sibling, &node)
            // } else {
            //     merge::<H>(&node, &sibling)
            // };

            if node_height == core::u8::MAX {
                if proof.is_empty() {
                    return Ok(parent);
                } else {
                    return Err(Error::CorruptedProof);
                }
            } else {
                leaves_path[leaf_index].pop_front();
                tree_buf.insert((node_height + 1, node_key), (leaf_index, parent));
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

// /// An structure optimized for verify merkle proof
// #[derive(Debug, Clone)]
// pub struct CompiledMerkleProof(pub Vec<u8>);

// impl CompiledMerkleProof {
//     pub fn compute_root<H: Hasher + Default>(&self, mut leaves: Vec<(H256, H256)>) -> Result<H256> {
//         leaves.sort_unstable_by_key(|(k, _v)| *k);
//         let mut program_index = 0;
//         let mut leaf_index = 0;
//         let mut stack: Vec<(u16, H256, H256)> = Vec::new();
//         while program_index < self.0.len() {
//             let code = self.0[program_index];
//             program_index += 1;
//             match code {
//                 // L : push leaf value
//                 0x4C => {
//                     if leaf_index >= leaves.len() {
//                         return Err(Error::CorruptedStack);
//                     }
//                     let (k, v) = leaves[leaf_index];
//                     stack.push((0, k, v));
//                     leaf_index += 1;
//                 }
//                 // P : hash stack top item with sibling node in proof
//                 0x50 => {
//                     if stack.is_empty() {
//                         return Err(Error::CorruptedStack);
//                     }
//                     if program_index + 32 > self.0.len() {
//                         return Err(Error::CorruptedProof);
//                     }
//                     let mut data = [0u8; 32];
//                     data.copy_from_slice(&self.0[program_index..program_index + 32]);
//                     program_index += 32;
//                     let sibling_node = H256::from(data);
//                     let (height_u16, key, value) = stack.pop().unwrap();
//                     if height_u16 > 255 {
//                         return Err(Error::CorruptedProof);
//                     }
//                     let height = height_u16 as u8;
//                     let parent_key = key.parent_path(height);
//                     let parent = if key.get_bit(height) {
//                         merge::<H>(height, &parent_key, &sibling_node, &value)
//                     } else {
//                         merge::<H>(height, &parent_key, &value, &sibling_node)
//                     };
//                     stack.push((height_u16 + 1, parent_key, parent));
//                 }
//                 // H : pop 2 items in stack hash them then push the result
//                 0x48 => {
//                     if stack.len() < 2 {
//                         return Err(Error::CorruptedStack);
//                     }
//                     let (height_b, key_b, value_b) = stack.pop().unwrap();
//                     let (height_a, key_a, value_a) = stack.pop().unwrap();
//                     if height_a != height_b {
//                         return Err(Error::CorruptedProof);
//                     }
//                     if height_a > 255 {
//                         return Err(Error::CorruptedProof);
//                     }
//                     let height_u16 = height_a;
//                     let height = height_u16 as u8;
//                     let parent_key_a = key_a.parent_path(height);
//                     let parent_key_b = key_b.parent_path(height);
//                     if parent_key_a != parent_key_b {
//                         return Err(Error::CorruptedProof);
//                     }
//                     let parent = if key_a.get_bit(height) {
//                         merge::<H>(height, &parent_key_a, &value_b, &value_a)
//                     } else {
//                         merge::<H>(height, &parent_key_a, &value_a, &value_b)
//                     };
//                     stack.push((height_u16 + 1, parent_key_a, parent));
//                 }
//                 // O : hash stack top item with n zero values
//                 0x4F => {
//                     if stack.is_empty() {
//                         return Err(Error::CorruptedStack);
//                     }
//                     if program_index >= self.0.len() {
//                         return Err(Error::CorruptedProof);
//                     }
//                     let n = self.0[program_index];
//                     program_index += 1;
//                     let zero_count: u16 = if n == 0 { 256 } else { n as u16 };
//                     let (base_height, key, mut value) = stack.pop().unwrap();
//                     if base_height > 255 {
//                         return Err(Error::CorruptedProof);
//                     }
//                     let mut parent_key = key;
//                     let mut height_u16 = base_height;
//                     for idx in 0..zero_count {
//                         if base_height + idx > 255 {
//                             return Err(Error::CorruptedProof);
//                         }
//                         height_u16 = base_height + idx;
//                         let height = height_u16 as u8;
//                         parent_key = key.parent_path(height);
//                         value = if key.get_bit(height) {
//                             merge::<H>(height, &parent_key, &H256::zero(), &value)
//                         } else {
//                             merge::<H>(height, &parent_key, &value, &H256::zero())
//                         };
//                     }
//                     stack.push((height_u16 + 1, parent_key, value));
//                 }
//                 _ => return Err(Error::InvalidCode(code)),
//             }
//             debug_assert!(stack.len() <= MAX_STACK_SIZE);
//         }
//         if stack.len() != 1 {
//             return Err(Error::CorruptedStack);
//         }
//         if stack[0].0 != 256 {
//             return Err(Error::CorruptedProof);
//         }
//         if leaf_index != leaves.len() {
//             return Err(Error::CorruptedProof);
//         }
//         Ok(stack[0].2)
//     }

//     pub fn verify<H: Hasher + Default>(
//         &self,
//         root: &H256,
//         leaves: Vec<(H256, H256)>,
//     ) -> Result<bool> {
//         let calculated_root = self.compute_root::<H>(leaves)?;
//         Ok(&calculated_root == root)
//     }
// }

// impl Into<Vec<u8>> for CompiledMerkleProof {
//     fn into(self) -> Vec<u8> {
//         self.0
//     }
// }
