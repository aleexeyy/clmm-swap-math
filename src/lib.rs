use alloy_primitives::U256;

pub mod error;
mod hash;
pub mod math;

pub use hash::FastMap;

pub mod pool;

pub use pool::v3_pool::V3Pool;

const U256_1: U256 = U256::from_limbs([1, 0, 0, 0]);
const U256_127: U256 = U256::from_limbs([127, 0, 0, 0]);
const U256_128: U256 = U256::from_limbs([128, 0, 0, 0]);

const U160_MAX: U256 = U256::from_limbs([0, 0, 4294967296, 0]);
const U256_10000: U256 = U256::from_limbs([10000, 0, 0, 0]);

pub const RESOLUTION: u8 = 96;
pub const Q96: U256 = U256::from_limbs([0, 4294967296, 0, 0]);
