use crate::error::{Error, SwapError};
use crate::math::liquidity_math::add_delta;
use crate::math::math_helpers::{mul_div, unlikely};
use crate::math::sqrt_price_math::{get_amount_0_delta_base, get_amount_1_delta_base};
use crate::math::swap_math::compute_swap_step;
use crate::math::tick_bitmap::next_initialized_tick_within_one_word;
use crate::math::tick_math::{
    MAX_SQRT_RATIO, MAX_TICK, MIN_SQRT_RATIO, MIN_TICK, get_sqrt_ratio_at_tick,
    get_tick_at_sqrt_ratio,
};
use crate::{U256_E4, U256_E6};
use alloy_primitives::{I256, U256};
use std::ops::{Add, Sub};

/// Computes a conservative sqrt‑price limit for a swap given the current
/// price, swap direction, and a slippage tolerance in percent.
///
/// This is handy when building user‑facing APIs: you can derive a
/// `sqrt_price_limit_x96` from a human‑friendly percentage tolerance.
pub fn calculate_sqrt_price_limit(
    sqrt_price_x96: U256,
    zero_for_one: bool,
    tolerance: f32, // in percent
) -> U256 {
    let slippage_bps = tolerance * 10_000.0;

    if zero_for_one {
        (sqrt_price_x96 * U256::from(10000.0 - slippage_bps)) / U256_E4
    } else {
        (sqrt_price_x96 * U256::from(10000.0 + slippage_bps)) / U256_E4
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Slot0 {
    pub sqrt_price_x96: U256,
    pub tick: i32,
}

impl Default for Slot0 {
    fn default() -> Self {
        Self {
            sqrt_price_x96: U256::ZERO,
            tick: 0i32,
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub struct SwapParams {
    /// Swap direction: `true` for token0 → token1, `false` for token1 → token0.
    pub zero_for_one: bool,
    /// Signed amount being swapped. Positive means “exact in”, negative means “exact out”.
    pub amount_specified: I256,
    /// Sqrt‑price limit in Q96 that bounds how far the price is allowed to move.
    ///
    /// Use [`calculate_sqrt_price_limit`] to derive this from a percentage slippage tolerance.
    pub sqrt_price_limit_x96: U256,
}

impl SwapParams {
    /// Creates new swap parameters for a given direction, signed amount,
    /// and explicit sqrt‑price limit.
    #[inline]
    pub fn new(zero_for_one: bool, amount_specified: I256, sqrt_price_limit_x96: U256) -> Self {
        Self {
            zero_for_one,
            amount_specified,
            sqrt_price_limit_x96,
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub struct SwapResult {
    pub amount0_delta: I256,
    pub amount1_delta: I256,
    pub fees_paid: U256,
}

// the top level state of the swap, the results of which are recorded in storage at the end
pub struct SwapState {
    // the amount remaining to be swapped in/out of the input/output asset
    amount_specified_remaining: I256,
    // the amount already swapped out/in of the output/input asset
    amount_calculated: I256,
    // current sqrt(price)
    sqrt_price_x96: U256,
    // the tick associated with the current price
    tick: i32,
    // the current liquidity in range
    liquidity: u128,
    // accumulated swap fees
    swap_fee: U256,
}

impl Default for SwapState {
    fn default() -> Self {
        Self {
            amount_specified_remaining: I256::ZERO,
            amount_calculated: I256::ZERO,
            sqrt_price_x96: U256::ZERO,
            tick: 0i32,
            liquidity: 0u128,
            swap_fee: U256::ZERO,
        }
    }
}

pub struct StepComputations {
    // the price at the beginning of the step
    sqrt_price_start_x96: U256,
    // the next tick to swap to from the current tick in the swap direction
    tick_next: i32,
    // whether tickNext is initialized or not
    initialized: bool,
    // sqrt(price) for the next tick (1/0)
    sqrt_price_next_x96: U256,
    // how much is being swapped in this step
    amount_in: U256,
    // how much is being swapped out
    amount_out: U256,
    // how much fee is being paid in
    fee_amount: U256,
}

impl Default for StepComputations {
    fn default() -> Self {
        Self {
            sqrt_price_start_x96: U256::ZERO,
            tick_next: 0,
            initialized: false,
            sqrt_price_next_x96: U256::ZERO,
            amount_in: U256::ZERO,
            amount_out: U256::ZERO,
            fee_amount: U256::ZERO,
        }
    }
}

impl<P> crate::pool::v3_pool::V3Pool<P> {
    /// Executes a Uniswap V3‑style swap against the in‑memory pool
    /// state using the provided `SwapParams`, returning signed token
    /// deltas and total fees charged.
    ///
    /// In `onchain` builds, you typically call the async helpers on
    /// `V3Pool` to populate state from a live pool, then run `swap`
    /// locally to simulate or quote a trade.
    pub fn swap(&self, params: SwapParams) -> Result<SwapResult, Error> {
        let amount_specified = params.amount_specified;
        if unlikely(amount_specified.is_zero()) {
            return Err(Error::SwapError(SwapError::AmountSpecifiedIsZero));
        }
        if unlikely(self.liquidity == 0) {
            return Err(Error::SwapError(SwapError::LiquidityIsZero));
        }

        let zero_for_one = params.zero_for_one;
        let sqrt_price_limit_x96 = params.sqrt_price_limit_x96;
        if zero_for_one {
            if unlikely(
                (sqrt_price_limit_x96 >= self.slot0.sqrt_price_x96)
                    || (sqrt_price_limit_x96 <= MIN_SQRT_RATIO),
            ) {
                return Err(Error::SwapError(SwapError::SqrtPriceOutOfBounds));
            }
        } else if unlikely(
            (sqrt_price_limit_x96 <= self.slot0.sqrt_price_x96)
                || (sqrt_price_limit_x96 >= MAX_SQRT_RATIO),
        ) {
            return Err(Error::SwapError(SwapError::SqrtPriceOutOfBounds));
        }

        let exact_input: bool = amount_specified.is_positive();

        let mut state: SwapState = SwapState {
            amount_specified_remaining: amount_specified,
            amount_calculated: I256::ZERO,
            sqrt_price_x96: self.slot0.sqrt_price_x96,
            tick: self.slot0.tick,
            liquidity: self.liquidity,
            swap_fee: U256::ZERO,
        };

        while (state.amount_specified_remaining != I256::ZERO)
            && (state.sqrt_price_x96 != sqrt_price_limit_x96)
        {
            let mut step = StepComputations {
                sqrt_price_start_x96: state.sqrt_price_x96,
                ..StepComputations::default()
            };

            (step.tick_next, step.initialized) = next_initialized_tick_within_one_word(
                &self.bitmap,
                state.tick,
                self.tick_spacing,
                zero_for_one,
            )?;

            step.tick_next = step.tick_next.clamp(MIN_TICK, MAX_TICK);

            step.sqrt_price_next_x96 = get_sqrt_ratio_at_tick(step.tick_next)?;

            (
                state.sqrt_price_x96,
                step.amount_in,
                step.amount_out,
                step.fee_amount,
            ) = compute_swap_step(
                state.sqrt_price_x96,
                if zero_for_one {
                    if step.sqrt_price_next_x96 < sqrt_price_limit_x96 {
                        sqrt_price_limit_x96
                    } else {
                        step.sqrt_price_next_x96
                    }
                } else if step.sqrt_price_next_x96 > sqrt_price_limit_x96 {
                    sqrt_price_limit_x96
                } else {
                    step.sqrt_price_next_x96
                },
                state.liquidity,
                state.amount_specified_remaining,
                self.fee_pips,
            )?;

            state.swap_fee += step.fee_amount;

            if exact_input {
                state.amount_specified_remaining -=
                    I256::from_raw(step.amount_in + step.fee_amount);
                state.amount_calculated =
                    state.amount_calculated.sub(I256::from_raw(step.amount_out));
            } else {
                state.amount_specified_remaining += I256::from_raw(step.amount_out);
                state.amount_calculated = state
                    .amount_calculated
                    .add(I256::from_raw(step.amount_in + step.fee_amount));
            }

            if state.sqrt_price_x96 == step.sqrt_price_next_x96 {
                if step.initialized {
                    if let Some(mut liquidity_net) = self.get_liquidity_net(&step.tick_next) {
                        if zero_for_one {
                            liquidity_net = -liquidity_net;
                        }
                        state.liquidity = add_delta(state.liquidity, liquidity_net)?;
                    } else {
                        return Err(Error::SwapError(SwapError::LiquidityIsZero));
                    }
                }
                state.tick = if zero_for_one {
                    step.tick_next - 1
                } else {
                    step.tick_next
                };
            } else if state.sqrt_price_x96 != step.sqrt_price_start_x96 {
                state.tick = get_tick_at_sqrt_ratio(state.sqrt_price_x96)?;
            }
        }

        let (amount0, amount1): (I256, I256) = if zero_for_one == exact_input {
            (
                amount_specified - state.amount_specified_remaining,
                state.amount_calculated,
            )
        } else {
            (
                state.amount_calculated,
                amount_specified - state.amount_specified_remaining,
            )
        };

        Ok(SwapResult {
            amount0_delta: amount0,
            amount1_delta: amount1,
            fees_paid: state.swap_fee,
        })
    }

    /// Returns the maximum input amount that can be swapped in the given
    /// direction before the pool exhausts all usable liquidity or reaches
    /// global tick bounds.
    ///
    /// This is useful for algorithms that require an upper bound on swap
    /// size (e.g., binary search for optimal input).
    ///
    /// The value is denominated in the input token for the chosen direction
    /// and includes the pool’s fee.
    pub fn get_max_token_amount(&self, zero_for_one: bool) -> Result<U256, Error> {
        let mut state = SwapState {
            sqrt_price_x96: self.slot0.sqrt_price_x96,
            tick: self.slot0.tick,
            liquidity: self.liquidity,
            ..Default::default()
        };

        let mut max_token_amount: U256 = U256::ZERO;

        while state.tick > MIN_TICK && state.tick < MAX_TICK && state.liquidity != 0 {
            let mut step = StepComputations {
                sqrt_price_start_x96: state.sqrt_price_x96,
                ..Default::default()
            };

            (step.tick_next, step.initialized) = next_initialized_tick_within_one_word(
                &self.bitmap,
                state.tick,
                self.tick_spacing,
                zero_for_one,
            )?;

            step.tick_next = step.tick_next.clamp(MIN_TICK, MAX_TICK);

            step.sqrt_price_next_x96 = get_sqrt_ratio_at_tick(step.tick_next)?;

            max_token_amount += if zero_for_one {
                get_amount_0_delta_base(
                    step.sqrt_price_next_x96,
                    state.sqrt_price_x96,
                    state.liquidity,
                    true,
                )?
            } else {
                get_amount_1_delta_base(
                    state.sqrt_price_x96,
                    step.sqrt_price_next_x96,
                    state.liquidity,
                    true,
                )?
            };

            state.sqrt_price_x96 = step.sqrt_price_next_x96;

            if step.initialized {
                if let Some(mut liquidity_net) = self.get_liquidity_net(&step.tick_next) {
                    if zero_for_one {
                        liquidity_net = -liquidity_net;
                    }
                    state.liquidity = add_delta(state.liquidity, liquidity_net)?;
                } else {
                    return Err(Error::SwapError(SwapError::LiquidityIsZero));
                }
            }
            state.tick = if zero_for_one {
                step.tick_next - 1
            } else {
                step.tick_next
            };
        }
        Ok(mul_div(
            max_token_amount,
            U256_E6,
            U256::from(1000000u32 - self.fee_pips),
        )
        .unwrap_or(U256::MAX))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::FastMap;
    use crate::V3Pool;
    use alloy_primitives::address;
    #[cfg(all(test, feature = "onchain"))]
    use alloy_provider::Provider;
    use std::str::FromStr;
    #[cfg(all(test, feature = "onchain"))]
    use std::sync::Arc;

    use crate::pool::v3_pool::TickInfo;
    #[cfg(all(test, feature = "onchain"))]
    use alloy_provider::RootProvider;
    #[cfg(all(test, feature = "onchain"))]
    use alloy_provider::network::Ethereum;
    // ---------------- Dummy Provider for tests ----------------

    #[cfg(all(test, feature = "onchain"))]
    #[derive(Clone)]
    struct DummyProvider;
    #[cfg(all(test, feature = "onchain"))]
    impl Provider for DummyProvider {
        fn root(&self) -> &RootProvider<Ethereum> {
            // swap() never touches the provider in these tests.
            // If this is ever called, it's a bug in the test wiring.
            unimplemented!("DummyProvider::root should not be used in swap unit tests");
        }
    }
    #[cfg(all(test, feature = "onchain"))]
    type TestPool = V3Pool<DummyProvider>;
    #[cfg(all(test, feature = "onchain"))]
    fn make_basic_pool(
        sqrt_price_x96: U256,
        tick: i32,
        liquidity: u128,
        fee_pips: u32,
        bitmap: FastMap<i16, U256>,
    ) -> TestPool {
        let provider = Arc::new(DummyProvider);

        let pool_address = address!("0x1000000000000000000000000000000000000000");
        let token0 = address!("0x0000000000000000000000000000000000000001");
        let token1 = address!("0x0000000000000000000000000000000000000002");

        let mut pool = TestPool::new(pool_address, token0, token1, fee_pips, provider);

        pool.slot0 = Slot0 {
            sqrt_price_x96,
            tick,
        };
        pool.liquidity = liquidity;
        pool.tick_spacing = 1; // simplest spacing
        pool.bitmap = bitmap;

        pool
    }
    #[cfg(not(feature = "onchain"))]
    type TestPool = V3Pool<()>;

    #[cfg(not(feature = "onchain"))]
    fn make_basic_pool(
        sqrt_price_x96: U256,
        tick: i32,
        liquidity: u128,
        fee_pips: u32,
        bitmap: FastMap<i16, U256>,
    ) -> TestPool {
        let pool_address = address!("0x1000000000000000000000000000000000000000");
        let token0 = address!("0x0000000000000000000000000000000000000001");
        let token1 = address!("0x0000000000000000000000000000000000000002");

        let mut pool = TestPool::new(pool_address, token0, token1, fee_pips);

        pool.slot0 = Slot0 {
            sqrt_price_x96,
            tick,
        };
        pool.liquidity = liquidity;
        pool.tick_spacing = 1;
        pool.bitmap = bitmap;

        pool
    }

    fn default_bitmap() -> FastMap<i16, U256> {
        FastMap::default()
    }

    // ---------------- Basic validation tests ----------------

    #[test]
    fn swap_rejects_zero_amount_specified() {
        let sqrt_price = get_sqrt_ratio_at_tick(0).unwrap();
        let pool = make_basic_pool(sqrt_price, 0, 1_000_000u128, 3000, default_bitmap());

        let params = SwapParams {
            zero_for_one: true,
            amount_specified: I256::ZERO,
            sqrt_price_limit_x96: sqrt_price - U256::from(1u8),
        };

        let err = pool.swap(params).unwrap_err();

        match err {
            Error::SwapError(SwapError::AmountSpecifiedIsZero) => {}
            other => panic!("expected AmountSpecifiedIsZero, got: {:?}", other),
        }
    }

    #[test]
    fn swap_rejects_sqrt_price_limit_out_of_bounds_zero_for_one() {
        let sqrt_price = get_sqrt_ratio_at_tick(0).unwrap();
        let pool = make_basic_pool(sqrt_price, 0, 1_000_000u128, 3000, default_bitmap());

        // limit >= current price should be rejected for zero_for_one
        let params_eq = SwapParams {
            zero_for_one: true,
            amount_specified: I256::from_raw(U256::from(1_000u64)),
            sqrt_price_limit_x96: sqrt_price, // equal
        };
        let err_eq = pool.swap(params_eq).unwrap_err();
        match err_eq {
            Error::SwapError(SwapError::SqrtPriceOutOfBounds) => {}
            other => panic!("expected SqrtPriceOutOfBounds (eq case), got: {:?}", other),
        }

        // limit <= MIN_SQRT_RATIO should also be rejected
        let params_min = SwapParams {
            zero_for_one: true,
            amount_specified: I256::from_raw(U256::from(1_000u64)),
            sqrt_price_limit_x96: MIN_SQRT_RATIO, // too low or equal
        };
        let err_min = pool.swap(params_min).unwrap_err();
        match err_min {
            Error::SwapError(SwapError::SqrtPriceOutOfBounds) => {}
            other => panic!("expected SqrtPriceOutOfBounds (min case), got: {:?}", other),
        }
    }

    #[test]
    fn swap_rejects_sqrt_price_limit_out_of_bounds_one_for_zero() {
        let sqrt_price = get_sqrt_ratio_at_tick(0).unwrap();
        let pool = make_basic_pool(sqrt_price, 0, 1_000_000u128, 3000, default_bitmap());

        // limit <= current price should be rejected for one_for_zero
        let params_eq = SwapParams {
            zero_for_one: false,
            amount_specified: I256::from_raw(U256::from(1_000u64)),
            sqrt_price_limit_x96: sqrt_price, // equal
        };
        let err_eq = pool.swap(params_eq).unwrap_err();
        match err_eq {
            Error::SwapError(SwapError::SqrtPriceOutOfBounds) => {}
            other => panic!("expected SqrtPriceOutOfBounds (eq case), got: {:?}", other),
        }

        // limit >= MAX_SQRT_RATIO should be rejected
        let params_max = SwapParams {
            zero_for_one: false,
            amount_specified: I256::from_raw(U256::from(1_000u64)),
            sqrt_price_limit_x96: MAX_SQRT_RATIO, // too high or equal
        };
        let err_max = pool.swap(params_max).unwrap_err();
        match err_max {
            Error::SwapError(SwapError::SqrtPriceOutOfBounds) => {}
            other => panic!("expected SqrtPriceOutOfBounds (max case), got: {:?}", other),
        }
    }

    // ---------------- Behavioural / invariants tests ----------------

    #[test]
    fn swap_with_zero_liquidity_does_not_change_amounts_or_charge_fees() {
        let sqrt_price = get_sqrt_ratio_at_tick(0).unwrap();
        let pool = make_basic_pool(sqrt_price, 0, 0u128, 3000, default_bitmap());

        let limit = sqrt_price - U256::from(1u8);

        let params = SwapParams {
            zero_for_one: true,
            amount_specified: I256::from_raw(U256::from(1_000_000u64)),
            sqrt_price_limit_x96: limit,
        };

        let result = pool.swap(params);

        // With zero liquidity, we can't actually trade anything.
        assert!(matches!(
            result,
            Err(Error::SwapError(SwapError::LiquidityIsZero))
        ));
    }

    #[test]
    fn swap_exact_input_one_for_zero_has_expected_signs() {
        let sqrt_price = get_sqrt_ratio_at_tick(0).unwrap();
        let mut bitmap = FastMap::default();
        bitmap.insert(0_i16, U256::from(1u8));

        let pool = make_basic_pool(sqrt_price, 0, 1_000_000u128, 3000, bitmap);

        let limit = sqrt_price * U256::from(2u8); // higher price, but < MAX_SQRT_RATIO
        assert!(limit < MAX_SQRT_RATIO);

        let amount = U256::from_str("1000000000000000000").unwrap(); // 1e18

        let params = SwapParams {
            zero_for_one: false, // one-for-zero
            amount_specified: I256::from_raw(amount),
            sqrt_price_limit_x96: limit,
        };

        let result = pool.swap(params).unwrap();

        assert!(result.amount1_delta >= I256::ZERO);
        assert!(result.amount0_delta <= I256::ZERO);

        assert!(
            result.amount0_delta != I256::ZERO || result.amount1_delta != I256::ZERO,
            "expected some swap to occur"
        );
        assert!(result.fees_paid >= U256::ZERO);
    }

    fn build_real_example_pool() -> TestPool {
        let mut pool = make_basic_pool(U256::ZERO, 0, 0, 3000, FastMap::default());

        pool.slot0 = Slot0 {
            sqrt_price_x96: U256::from_str("1046706758115479018135889").unwrap(),
            tick: -224701,
        };
        pool.liquidity = 203624297715738503472u128;

        pool.tick_spacing = 60;

        let mut bitmap: FastMap<i16, U256> = FastMap::default();
        bitmap.insert(
            -15_i16,
            U256::from_str("39614081257132168796771975168").unwrap(),
        );
        bitmap.insert(
            57_i16,
            U256::from_str("50216813883093446110686315385661331328818843555712276103168").unwrap(),
        );

        let mut ticks: FastMap<i32, TickInfo> = FastMap::default();

        ticks.insert(
            -224700,
            TickInfo {
                word_position: -15,
                liquidity_gross: 203624287356963452704,
                liquidity_net: -203624287356963452704,
            },
        );

        ticks.insert(
            887220,
            TickInfo {
                word_position: 57,
                liquidity_gross: 10358775050768,
                liquidity_net: -10358775050768,
            },
        );
        pool.bitmap = bitmap;
        pool.ticks = ticks;

        pool
    }

    #[test]
    fn swap_matches_js_single_case() {
        let pool = build_real_example_pool();

        let zero_for_one = false; // Direction: false
        let amount_specified = I256::from_raw(U256::from(1_098_120u64));

        let slippage_bps = 0.5; // 0.5% = 50 bps
        let sqrt_price_start = pool.slot0.sqrt_price_x96;
        let sqrt_price_limit_x96 =
            calculate_sqrt_price_limit(sqrt_price_start, zero_for_one, slippage_bps);

        let params = SwapParams {
            zero_for_one,
            amount_specified,
            sqrt_price_limit_x96,
        };

        // Act
        let result = pool.swap(params).expect("swap should succeed");

        let expected_amount_out = I256::from_raw(-U256::from(6222896066140743u64));
        let expected_amount_used = I256::from_raw(U256::from(1098120));

        assert_eq!(
            result.amount0_delta, expected_amount_out,
            "Swap amount0_out does not match expected amountOut"
        );
        assert_eq!(
            result.amount1_delta, expected_amount_used,
            "Swap amount1_out does not match expected amountUsed"
        );
    }

    #[test]
    fn max_token_amount_matches_full_swap_zero_for_one() {
        // Build a realistic pool using your existing helper
        let pool = build_real_example_pool();

        // Choose direction: token1 -> token0 (like your existing test: zero_for_one = false)
        let zero_for_one = false;

        // 1) Ask the pool for the theoretical maximum token amount
        let max_token_amount = pool
            .get_max_token_amount(zero_for_one)
            .expect("Failed to get max token amount");

        let huge_input = I256::MAX;

        let swap_result = pool
            .swap(SwapParams {
                zero_for_one,
                amount_specified: huge_input,
                sqrt_price_limit_x96: MAX_SQRT_RATIO.sub(U256::ONE),
            })
            .expect("Swap with huge input should succeed");

        assert!(
            U256::from(swap_result.amount1_delta).abs_diff(max_token_amount) <= U256::from(150u64),
            "Full-range swap with effectively infinite input should consume exactly get_max_token_amount() tokens",
        );
    }
}
