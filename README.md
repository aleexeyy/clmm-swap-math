# clmm-swap-math

A small, focused Rust crate that implements the core Uniswap V3 pool math in a reusable, test‑driven way. It exposes:

- Pure math utilities (`math` module) for ticks, sqrt prices, liquidity and swap steps.
- A lightweight in‑memory `V3Pool` type for simulating swaps off‑chain.
- Optional on‑chain integration (behind a feature flag) to read pool state from an Ethereum provider.

The crate is designed to be embeddable in trading tools, research scripts, or other DeFi infrastructure.

## Project structure

- `src/lib.rs` – crate root, exports:
  - `math` – all core math modules.
  - `pool` – pool structs and swap logic.
  - `FastMap` – feature‑selectable hash map alias.
- `src/error.rs` – error types (`MathError`, `StateError`, `SwapError`, `OnchainError`, `Error`).
- `src/math/`
  - `bit_math.rs` – bit operations (MSB/LSB) on `U256`.
  - `tick_math.rs` – tick ↔ sqrt ratio conversions (`get_sqrt_ratio_at_tick`, `get_tick_at_sqrt_ratio`).
  - `tick_bitmap.rs` – tick bitmap operations for initialized ticks.
  - `sqrt_price_math.rs` – price movement and amount deltas.
  - `liquidity_math.rs` – liquidity add/remove with bounds checks.
  - `math_helpers.rs` – high‑precision `mul_div` helpers.
  - `swap_math.rs` – single‑step swap math (`compute_swap_step`).
- `src/pool/`
  - `swap.rs` – high‑level `V3Pool::swap` logic, `SwapParams`, `SwapResult`, `Slot0`.
  - `v3_pool.rs` – `V3Pool<P>` struct, tick/bitmap fetching, and optional on‑chain RPC integration.
- `src/hash.rs` – defines `FastMap<K, V>` as `HashMap`, `FxHashMap`, or `AHashMap` depending on enabled features.
- `benches/` – Criterion benchmarks for each math module and for all math combined.

## Features

Defined in `Cargo.toml`:

- `default = ["std-hash"]`  
  - Builds pure math + pool logic with a standard `HashMap` backend.
  - No on‑chain networking or provider code is pulled in.

- `onchain`  
  - Enables on‑chain integration via `alloy-provider` and `alloy-contract`.
  - Activates async methods on `V3Pool<P>` (e.g. `fetch_slot0`, `fetch_liquidity`, bitmap/tick loading).

- Hash backends (mutually exclusive in practice, but not enforced):
  - `std-hash` – `FastMap<K, V> = std::collections::HashMap<K, V>`.
  - `rustc-hash` – `FastMap<K, V> = rustc_hash::FxHashMap<K, V>`.
  - `ahash` – `FastMap<K, V> = ahash::AHashMap<K, V>`.

## Using the math modules

Add this crate to your `Cargo.toml` (local path or git, depending on your setup) and import the math functions:

```rust
use uniswap_v3_math::math::tick_math::{
    get_sqrt_ratio_at_tick,
    get_tick_at_sqrt_ratio,
    MIN_TICK,
    MAX_TICK,
};
use alloy_primitives::U256;

fn example_ticks() {
    let sqrt_min = get_sqrt_ratio_at_tick(MIN_TICK).unwrap();
    let sqrt_mid = get_sqrt_ratio_at_tick(0).unwrap();

    let tick_back = get_tick_at_sqrt_ratio(sqrt_mid).unwrap();
    assert_eq!(tick_back, 0);

    let _: U256 = sqrt_min;
}
```

Other commonly used modules:

- `math::sqrt_price_math` for `get_next_sqrt_price_from_input` / `get_next_sqrt_price_from_output`.
- `math::swap_math` for `compute_swap_step`.
- `math::liquidity_math` for liquidity deltas (`add_delta`).

## Simulating swaps with `V3Pool`

Without the `onchain` feature (pure in‑memory simulation):

```rust
use alloy_primitives::{I256, U256, address};
use uniswap_v3_math::V3Pool;
use uniswap_v3_math::pool::swap::{Slot0, SwapParams};

fn simulate_swap() {
    let pool_address = address!("0x1000000000000000000000000000000000000000");
    let token0 = address!("0x0000000000000000000000000000000000000001");
    let token1 = address!("0x0000000000000000000000000000000000000002");

    // math-only constructor: no provider, no RPC
    let mut pool: V3Pool<()> = V3Pool::new(pool_address, token0, token1, 3000);

    // manually seed state
    pool.slot0 = Slot0 {
        sqrt_price_x96: U256::from(1u128) << 96,
        tick: 0,
    };
    pool.liquidity = 1_000_000u128;
    pool.tick_spacing = 1;

    let params = SwapParams {
        zero_for_one: true,
        amount_specified: I256::from(1_000i64),
        sqrt_price_limit_x96: pool.slot0.sqrt_price_x96 - U256::from(1u8),
    };

    let result = pool.swap(params).unwrap();
    println!("amount0: {}, amount1: {}, fees: {}", result.amount0_delta, result.amount1_delta, result.fees_paid);
}
```

This path does not require any network access or `alloy-provider` at runtime.

## Using on-chain pool data (feature = "onchain")

When you enable `onchain`, you can construct `V3Pool<P>` with a real provider and call async methods to fetch state:

```rust
use std::sync::Arc;
use alloy_primitives::address;
use alloy_provider::{Provider, ProviderBuilder};
use uniswap_v3_math::V3Pool;

#[tokio::main]
async fn main() -> eyre::Result<()> {
    let provider = Arc::new(ProviderBuilder::new().on_http("https://rpc.example")?);

    let pool_address = address!("0x...");
    let token0 = address!("0x...");
    let token1 = address!("0x...");

    let mut pool: V3Pool<_> = V3Pool::new(pool_address, token0, token1, 3000, provider);

    // Fetch latest liquidity + slot0 + tick spacing in one shot
    pool.refresh_latest().await?;

    println!("liquidity: {}", pool.liquidity);
    println!("slot0.tick: {}", pool.slot0.tick);

    Ok(())
}
```

Compile with:

```bash
cargo build --features onchain
```

## Benchmarks

Criterion benchmarks live under `benches/` and are registered in `Cargo.toml`. You can:

- Run all math benchmarks (including v1 vs v2 tick comparison):

```bash
cargo bench --bench math_bench
```

- Or per‑module:

```bash
cargo bench --bench tick_math_bench
cargo bench --bench sqrt_price_math_bench
cargo bench --bench swap_math_bench
cargo bench --bench math_helpers_bench
cargo bench --bench tick_bitmap_bench
cargo bench --bench bit_math_bench
```

These benches are intended to catch regressions in the core hot paths (`get_tick_at_sqrt_ratio`, `get_next_sqrt_price_from_input`, `compute_swap_step`, `mul_div`, etc.).

