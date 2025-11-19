use crate::error::{Error, SwapError};
use crate::swap_math::compute_swap_step;
use crate::tick_bitmap::next_initialized_tick_within_one_word;
use crate::tick_math::{
    MAX_SQRT_RATIO, MAX_TICK, MIN_SQRT_RATIO, MIN_TICK, get_sqrt_ratio_at_tick,
    get_tick_at_sqrt_ratio,
};
use alloy_primitives::{Address, I256, U256};
use std::ops::{Add, Sub};

#[derive(Copy, Clone)]
pub struct Slot0 {
    pub(crate) sqrt_price_x96: U256,
    pub(crate) tick: i32,
}

impl Default for Slot0 {
    fn default() -> Self {
        Self {
            sqrt_price_x96: U256::ZERO,
            tick: 0i32,
        }
    }
}

pub struct SwapInput {
    pool_address: Address,
    zero_for_one: bool,
    amount_specified: I256,
    sqrt_price_limit_x96: U256,
    slot0: Slot0,
    liquidity: u128,
    tick_spacing: i32,
    fee: u32,
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

pub async fn swap(input: SwapInput) -> Result<(I256, I256), Error> {
    let amount_specified = input.amount_specified;
    if amount_specified.is_zero() {
        return Err(Error::SwapError(SwapError::AmountSpecifiedIsZero).into());
    }
    let slot0_start = input.slot0.clone();

    let zero_for_one = input.zero_for_one;
    let sqrt_price_limit_x96 = input.sqrt_price_limit_x96;
    if zero_for_one {
        if sqrt_price_limit_x96 >= slot0_start.sqrt_price_x96
            || sqrt_price_limit_x96 <= MIN_SQRT_RATIO
        {
            return Err(Error::SwapError(SwapError::SqrtPriceOutOfBounds).into());
        }
    } else {
        if sqrt_price_limit_x96 <= slot0_start.sqrt_price_x96
            || sqrt_price_limit_x96 >= MAX_SQRT_RATIO
        {
            return Err(Error::SwapError(SwapError::SqrtPriceOutOfBounds).into());
        }
    }

    let exact_input: bool = amount_specified.is_positive();

    let mut state: SwapState = SwapState {
        amount_specified_remaining: amount_specified,
        amount_calculated: I256::ZERO,
        sqrt_price_x96: slot0_start.sqrt_price_x96,
        tick: slot0_start.tick,
        liquidity: input.liquidity,
        swap_fee: U256::ZERO,
    };
    // TODO: create bitmap initialisation
    let bitmap;

    while state.amount_specified_remaining != I256::ZERO
        && state.sqrt_price_x96 != sqrt_price_limit_x96
    {
        let mut step: StepComputations = StepComputations::default();

        step.sqrt_price_start_x96 = state.sqrt_price_x96;

        (step.tick_next, step.initialized) = next_initialized_tick_within_one_word(
            bitmap,
            state.tick,
            input.tick_spacing,
            zero_for_one,
        )?;

        if step.tick_next < MIN_TICK {
            step.tick_next = MIN_TICK;
        } else if step.tick_next > MAX_TICK {
            step.tick_next = MAX_TICK;
        }

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
            } else {
                if step.sqrt_price_next_x96 > sqrt_price_limit_x96 {
                    sqrt_price_limit_x96
                } else {
                    step.sqrt_price_next_x96
                }
            },
            state.liquidity,
            state.amount_specified_remaining,
            input.fee,
        )?;

        state.swap_fee += step.fee_amount;

        if exact_input {
            state.amount_specified_remaining -= I256::from_raw(step.amount_in + step.fee_amount);
            state.amount_calculated = state.amount_calculated.sub(I256::from_raw(step.amount_out));
        } else {
            state.amount_specified_remaining += I256::from_raw(step.amount_out);
            state.amount_calculated = state
                .amount_calculated
                .add(I256::from_raw(step.amount_in + step.fee_amount));
        }

        if state.sqrt_price_x96 == step.sqrt_price_next_x96 {
            if step.initialized {
                // TODO: Need to think, if I need to write something there
            }
            state.tick = if zero_for_one {
                step.tick_next - 1
            } else {
                step.tick_next
            }
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

    return Ok((amount0, amount1));
}
