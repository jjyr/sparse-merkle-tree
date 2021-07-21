use crate::h256::H256;
use crate::traits::Hasher;

pub const MERGE_TYPE_ZEROS: u8 = 0;
pub const MERGE_TYPE_NODE: u8 = 1;

/// Merge two hash with node information
pub fn merge<H: Hasher + Default>(height: u8, node_key: &H256, lhs: &H256, rhs: &H256) -> H256 {
    // Should use merge_zeros
    debug_assert!(!lhs.is_zero(), "wrong merge type");
    debug_assert!(!rhs.is_zero(), "wrong merge type");
    let mut hasher = H::default();
    hasher.write_byte(MERGE_TYPE_NODE);
    hasher.write_byte(height);
    hasher.write_h256(node_key);
    hasher.write_h256(lhs);
    hasher.write_h256(rhs);
    hasher.finish()
}

/// Merge a node with n zeros
pub fn merge_zeros<H: Hasher + Default>(
    height: u8,
    node_key: &H256,
    value: &H256,
    n_zeros: u8,
) -> H256 {
    // Optimized for zero values
    if value.is_zero() {
        return H256::zero();
    }
    let mut hasher = H::default();
    hasher.write_byte(MERGE_TYPE_ZEROS);
    hasher.write_byte(height);
    hasher.write_h256(node_key);
    hasher.write_h256(value);
    hasher.write_byte(n_zeros);
    hasher.finish()
}
