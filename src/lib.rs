//! Uniswap V3–style math and swap simulation in pure Rust.
//!
//! This crate exposes:
//! - Low‑level math primitives (`math::*`) for ticks, prices and bitmaps.
//! - A lightweight in‑memory `V3Pool` that can execute Uniswap V3‑style swaps.
//! - Optional `onchain` helpers to hydrate the pool from a real on‑chain pool.
//!
//! # Examples
//!
//! ## Pure math
//! ```no_run
//! use clmm_swap_math::{math::tick_math, RESOLUTION, U256};
//!
//! let sqrt_price = tick_math::get_sqrt_ratio_at_tick(0).unwrap();
//! assert!(sqrt_price > U256::ZERO);
//! assert_eq!(RESOLUTION, 96);
//! ```
//!
//! ## Simulating a swap in an in‑memory pool
//! ```no_run
//! use clmm_swap_math::{
//!     math::tick_math::get_sqrt_ratio_at_tick,
//!     pool::swap::{SwapParams, calculate_sqrt_price_limit},
//!     V3Pool, FastMap, I256, U256,
//! };
//!
//! // Construct a simple in‑memory pool (no on‑chain provider).
//! # let pool_address = clmm_swap_math::Address::ZERO;
//! # let token0 = clmm_swap_math::Address::ZERO;
//! # let token1 = clmm_swap_math::Address::from([0u8; 20]);
//! let mut pool: V3Pool<()> = V3Pool::new(pool_address, token0, token1, 3000);
//! pool.slot0.sqrt_price_x96 = get_sqrt_ratio_at_tick(0).unwrap();
//! pool.slot0.tick = 0;
//! pool.liquidity = 1_000_000_000_000_000_000u128;
//! pool.tick_spacing = 1;
//! pool.bitmap = FastMap::default();
//!
//! let zero_for_one = true;
//! let amount_specified = I256::from_raw(U256::from(1_000_000_000_000_000_000u128)); // 1e18
//! let sqrt_price_limit_x96 =
//!     calculate_sqrt_price_limit(pool.slot0.sqrt_price_x96, zero_for_one, 1.0); // 1% slippage
//!
//! let params = SwapParams::new(zero_for_one, amount_specified, sqrt_price_limit_x96);
//! let result = pool.swap(params).unwrap();
//! println!("amount0: {}, amount1: {}", result.amount0_delta, result.amount1_delta);
//! ```

pub use alloy_primitives::{Address, I256, U256};

pub mod error;
mod hash;
pub mod math;

pub use hash::FastMap;

pub mod pool;

pub use pool::v3_pool::V3Pool;

const U256_1: U256 = U256::from_limbs([1, 0, 0, 0]);

const U160_MAX: U256 = U256::from_limbs([0, 0, 4294967296, 0]);
const U256_E4: U256 = U256::from_limbs([10000, 0, 0, 0]);
const U256_E6: U256 = U256::from_limbs([1000000, 0, 0, 0]);

pub const RESOLUTION: u8 = 96;
pub const Q96: U256 = U256::from_limbs([0, 4294967296, 0, 0]);
