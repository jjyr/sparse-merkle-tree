use crate::h256::H256;
use crate::traits::Hasher;

pub const HASH_TYPE_MERGE: u8 = 0;
pub const HASH_TYPE_ALIGN: u8 = 1;

/// TODO try to remove this
/// hash_leaf = hash(key | value)
/// zero value represent delete the key, this function return zero for zero value
pub fn hash_leaf<H: Hasher + Default>(key: &H256, value: &H256) -> H256 {
    if value.is_zero() {
        return H256::zero();
    }
    let mut hasher = H::default();
    hasher.write_h256(key);
    hasher.write_h256(value);
    hasher.finish()
}

/// Merge two hash with node information
pub fn merge<H: Hasher + Default>(height: u8, node_key: &H256, lhs: &H256, rhs: &H256) -> H256 {
    if lhs.is_zero() && rhs.is_zero() {
        unreachable!();
        return H256::zero();
    }
    // Should use merge_zeros
    // debug_assert!(!lhs.is_zero(), "wrong merge type");
    // debug_assert!(!rhs.is_zero(), "wrong merge type");
    let mut hasher = H::default();
    hasher.write_byte(HASH_TYPE_MERGE);
    hasher.write_byte(height);
    hasher.write_h256(node_key);
    hasher.write_h256(lhs);
    hasher.write_h256(rhs);
    hasher.finish()
}

/// Merge a node with n zeros
pub fn align_with_zeros<H: Hasher + Default>(
    height: u8,
    node_key: &H256,
    node: &H256,
    n_zeros: u8,
) -> H256 {
    // can't merge with 0
    assert_ne!(n_zeros, 0);
    // Optimized for zero values
    if node.is_zero() {
        return H256::zero();
    }
    let mut hasher = H::default();
    hasher.write_byte(HASH_TYPE_ALIGN);
    hasher.write_byte(height);
    hasher.write_h256(node_key);
    hasher.write_h256(node);
    hasher.write_byte(n_zeros);
    hasher.finish()
}
