use crate::RESOLUTION;
use crate::math::math_helpers::{div_rounding_up, mul_div, mul_div_rounding_up, unlikely};
use crate::{
    Q96, U160_MAX,
    error::{Error, MathError, StateError},
};
use alloy_primitives::{I256, U256};

/// Computes the next sqrt price after swapping token0, rounding the
/// resulting price up, given current price, liquidity, amount, and
/// whether the amount is added or removed.
///
/// This is the low‑level primitive used by higher‑level swap math.
pub fn get_next_sqrt_price_from_amount_0_rounding_up(
    sqrt_p_x96: U256,
    liquidity: u128,
    amount: U256,
    add: bool,
) -> Result<U256, Error> {
    if amount.is_zero() {
        return Ok(sqrt_p_x96);
    }

    let numerator1: U256 = U256::from(liquidity) << RESOLUTION;
    let product: U256 = amount * sqrt_p_x96;

    if add {
        if product / amount == sqrt_p_x96 {
            let denominator = numerator1 + product;
            if denominator >= numerator1 {
                return mul_div_rounding_up(numerator1, sqrt_p_x96, denominator)
                    .map_err(Error::from);
            }
        }
        Ok(div_rounding_up(
            numerator1,
            (numerator1 / sqrt_p_x96) + amount,
        ))
    } else {
        if product / amount != sqrt_p_x96 || numerator1 <= product {
            return Err(StateError::InsufficientReserves.into());
        }
        let denominator = numerator1 - product;
        mul_div_rounding_up(numerator1, sqrt_p_x96, denominator).map_err(Error::from)
    }
}

/// Computes the next sqrt price after swapping token1, rounding the
/// resulting price down, given current price, liquidity, amount, and
/// direction (add/remove).
pub fn get_next_sqrt_price_from_amount_1_rounding_down(
    sqrt_p_x96: U256,
    liquidity: u128,
    amount: U256,
    add: bool,
) -> Result<U256, Error> {
    let liquidity = U256::from(liquidity);
    if add {
        let quotient: U256 = if amount <= U160_MAX {
            (amount << RESOLUTION) / liquidity
        } else {
            mul_div(amount, Q96, liquidity)?
        };

        let result = sqrt_p_x96 + quotient;
        if result <= U160_MAX {
            Ok(result)
        } else {
            Err(MathError::Overflow.into())
        }
    } else {
        let quotient: U256 = if amount <= U160_MAX {
            div_rounding_up(amount << RESOLUTION, liquidity)
        } else {
            mul_div_rounding_up(amount, Q96, liquidity)?
        };

        if sqrt_p_x96 <= quotient {
            return Err(StateError::InsufficientReserves.into());
        }
        let result = sqrt_p_x96 - quotient;

        if result <= U160_MAX {
            Ok(result)
        } else {
            Err(MathError::Overflow.into())
        }
    }
}

/// Core helper for computing the token0 amount delta between two
/// sqrt prices for a given liquidity, optionally rounding up.
///
/// This is used by both exact‑in and exact‑out swap flows.
pub fn get_amount_0_delta_base(
    mut sqrt_ratio_a_x96: U256,
    mut sqrt_ratio_b_x96: U256,
    liquidity: u128,
    round_up: bool,
) -> Result<U256, Error> {
    if sqrt_ratio_a_x96 > sqrt_ratio_b_x96 {
        (sqrt_ratio_a_x96, sqrt_ratio_b_x96) = (sqrt_ratio_b_x96, sqrt_ratio_a_x96)
    };

    if sqrt_ratio_a_x96.is_zero() {
        return Err(StateError::SqrtRatioIsZero.into());
    }

    let numerator1 = U256::from(liquidity) << RESOLUTION;
    let numerator2 = sqrt_ratio_b_x96 - sqrt_ratio_a_x96;

    if round_up {
        Ok(div_rounding_up(
            mul_div_rounding_up(numerator1, numerator2, sqrt_ratio_b_x96)?,
            sqrt_ratio_a_x96,
        ))
    } else {
        Ok(mul_div(numerator1, numerator2, sqrt_ratio_b_x96)? / sqrt_ratio_a_x96)
    }
}

/// Core helper for computing the token1 amount delta between two
/// sqrt prices for a given liquidity, optionally rounding up.
pub fn get_amount_1_delta_base(
    mut sqrt_ratio_a_x96: U256,
    mut sqrt_ratio_b_x96: U256,
    liquidity: u128,
    round_up: bool,
) -> Result<U256, MathError> {
    if sqrt_ratio_a_x96 > sqrt_ratio_b_x96 {
        (sqrt_ratio_a_x96, sqrt_ratio_b_x96) = (sqrt_ratio_b_x96, sqrt_ratio_a_x96)
    };
    let liquidity = U256::from(liquidity);

    if round_up {
        mul_div_rounding_up(liquidity, sqrt_ratio_b_x96 - sqrt_ratio_a_x96, Q96)
    } else {
        mul_div(liquidity, sqrt_ratio_b_x96 - sqrt_ratio_a_x96, Q96)
    }
}

/// Public wrapper for computing the signed token0 amount delta between
/// two sqrt prices for a signed liquidity amount.
pub fn get_amount_0_delta(
    sqrt_ratio_a_x96: U256,
    sqrt_ratio_b_x96: U256,
    liquidity: i128,
) -> Result<I256, Error> {
    if liquidity < 0 {
        Ok(-I256::from_raw(get_amount_0_delta_base(
            sqrt_ratio_a_x96,
            sqrt_ratio_b_x96,
            -liquidity as u128,
            false,
        )?))
    } else {
        Ok(I256::from_raw(get_amount_0_delta_base(
            sqrt_ratio_a_x96,
            sqrt_ratio_b_x96,
            liquidity as u128,
            true,
        )?))
    }
}

/// Public wrapper for computing the signed token1 amount delta between
/// two sqrt prices for a signed liquidity amount.
pub fn get_amount_1_delta(
    sqrt_ratio_a_x96: U256,
    sqrt_ratio_b_x96: U256,
    liquidity: i128,
) -> Result<I256, MathError> {
    if liquidity < 0 {
        Ok(-I256::from_raw(get_amount_1_delta_base(
            sqrt_ratio_a_x96,
            sqrt_ratio_b_x96,
            -liquidity as u128,
            false,
        )?))
    } else {
        Ok(I256::from_raw(get_amount_1_delta_base(
            sqrt_ratio_a_x96,
            sqrt_ratio_b_x96,
            -liquidity as u128,
            true,
        )?))
    }
}

/// Computes the next sqrt price when swapping *into* the pool
/// (`amount_in`), choosing the correct branch for token0/token1
/// depending on `zero_for_one`.
pub fn get_next_sqrt_price_from_input(
    sqrt_p_x96: U256,
    liquidity: u128,
    amount_in: U256,
    zero_for_one: bool,
) -> Result<U256, Error> {
    if unlikely(sqrt_p_x96.is_zero()) {
        return Err(StateError::SqrtPriceIsZero.into());
    }
    if unlikely(liquidity == 0) {
        return Err(StateError::LiquidityIsZero.into());
    }

    if zero_for_one {
        get_next_sqrt_price_from_amount_0_rounding_up(sqrt_p_x96, liquidity, amount_in, true)
    } else {
        get_next_sqrt_price_from_amount_1_rounding_down(sqrt_p_x96, liquidity, amount_in, true)
    }
}

/// Computes the next sqrt price when swapping *out of* the pool
/// (`amount_out`), choosing the correct branch for token0/token1
/// depending on `zero_for_one`.
pub fn get_next_sqrt_price_from_output(
    sqrt_p_x96: U256,
    liquidity: u128,
    amount_out: U256,
    zero_for_one: bool,
) -> Result<U256, Error> {
    if unlikely(sqrt_p_x96.is_zero()) {
        return Err(StateError::SqrtPriceIsZero.into());
    }
    if unlikely(liquidity == 0) {
        return Err(StateError::LiquidityIsZero.into());
    }

    if zero_for_one {
        get_next_sqrt_price_from_amount_1_rounding_down(sqrt_p_x96, liquidity, amount_out, false)
    } else {
        get_next_sqrt_price_from_amount_0_rounding_up(sqrt_p_x96, liquidity, amount_out, false)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::U256_1;
    const U256_2: U256 = U256::from_limbs([2, 0, 0, 0]);
    use std::{
        ops::{Add, Sub},
        str::FromStr,
    };

    #[test]
    fn test_get_next_sqrt_price_from_input() {
        //Fails if price is zero
        let result = get_next_sqrt_price_from_input(
            U256::ZERO,
            0,
            U256::from(100000000000000000_u128),
            false,
        );
        assert!(matches!(
            result,
            Err(Error::StateError(StateError::SqrtPriceIsZero))
        ));

        //Fails if liquidity is zero
        let result =
            get_next_sqrt_price_from_input(U256_1, 0, U256::from(100000000000000000_u128), true);
        assert!(matches!(
            result,
            Err(Error::StateError(StateError::LiquidityIsZero))
        ));

        //fails if input amount overflows the price
        let result = get_next_sqrt_price_from_input(U160_MAX, 1024, U256::from(1024), false);
        assert!(matches!(result, Err(Error::MathError(MathError::Overflow))));

        //any input amount cannot underflow the price
        let result = get_next_sqrt_price_from_input(
            U256_1,
            1,
            U256::from_str(
                "57896044618658097711785492504343953926634992332820282019728792003956564819968",
            )
            .unwrap(),
            true,
        );

        assert_eq!(result.unwrap(), U256_1);

        //returns input price if amount in is zero and zeroForOne = true
        let result = get_next_sqrt_price_from_input(
            U256::from_str("79228162514264337593543950336").unwrap(),
            1e17 as u128,
            U256::ZERO,
            true,
        );

        assert_eq!(
            result.unwrap(),
            U256::from_str("79228162514264337593543950336").unwrap()
        );

        //returns input price if amount in is zero and zeroForOne = false
        let result = get_next_sqrt_price_from_input(
            U256::from_str("79228162514264337593543950336").unwrap(),
            1e17 as u128,
            U256::ZERO,
            true,
        );

        assert_eq!(
            result.unwrap(),
            U256::from_str("79228162514264337593543950336").unwrap()
        );

        //returns the minimum price for max inputs

        let sqrt_price = U160_MAX;
        let liquidity = u128::MAX;
        let max_amount_no_overflow = U256::MAX - ((U256::from(liquidity) << 96) / sqrt_price);
        let result =
            get_next_sqrt_price_from_input(sqrt_price, liquidity, max_amount_no_overflow, true);
        assert_eq!(result.unwrap(), U256_1);

        //input amount of 0.1 token1
        let result = get_next_sqrt_price_from_input(
            U256::from_str("79228162514264337593543950336").unwrap(),
            1e18 as u128,
            U256::from_str("100000000000000000").unwrap(),
            false,
        );

        assert_eq!(
            result.unwrap(),
            U256::from_str("87150978765690771352898345369").unwrap()
        );

        //input amount of 0.1 token0
        let result = get_next_sqrt_price_from_input(
            U256::from_str("79228162514264337593543950336").unwrap(),
            1e18 as u128,
            U256::from_str("100000000000000000").unwrap(),
            true,
        );

        assert_eq!(
            result.unwrap(),
            U256::from_str("72025602285694852357767227579").unwrap()
        );

        //amountIn > type(uint96).max and zeroForOne = true
        let result = get_next_sqrt_price_from_input(
            U256::from_str("79228162514264337593543950336").unwrap(),
            1e19 as u128,
            U256::from_str("1267650600228229401496703205376").unwrap(),
            true,
        );
        // perfect answer:
        // https://www.wolframalpha.com/input/?i=624999999995069620+-+%28%281e19+*+1+%2F+%281e19+%2B+2%5E100+*+1%29%29+*+2%5E96%29
        assert_eq!(
            result.unwrap(),
            U256::from_str("624999999995069620").unwrap()
        );

        //can return 1 with enough amountIn and zeroForOne = true
        let result = get_next_sqrt_price_from_input(
            U256::from_str("79228162514264337593543950336").unwrap(),
            1,
            U256::MAX / U256_2,
            true,
        );

        assert_eq!(result.unwrap(), U256_1);
    }

    #[test]
    fn test_get_next_sqrt_price_from_output() {
        //fails if price is zero
        let result = get_next_sqrt_price_from_output(U256::ZERO, 0, U256::from(1000000000), false);
        assert!(matches!(
            result,
            Err(Error::StateError(StateError::SqrtPriceIsZero))
        ));

        //fails if liquidity is zero
        let result = get_next_sqrt_price_from_output(U256_1, 0, U256::from(1000000000), false);
        assert!(matches!(
            result,
            Err(Error::StateError(StateError::LiquidityIsZero))
        ));

        //fails if output amount is exactly the virtual reserves of token0
        let result = get_next_sqrt_price_from_output(
            U256::from_str("20282409603651670423947251286016").unwrap(),
            1024,
            U256::from(4),
            false,
        );
        assert!(matches!(
            result,
            Err(Error::StateError(StateError::InsufficientReserves))
        ));

        //fails if output amount is greater than virtual reserves of token0
        let result = get_next_sqrt_price_from_output(
            U256::from_str("20282409603651670423947251286016").unwrap(),
            1024,
            U256::from(5),
            false,
        );
        assert!(matches!(
            result,
            Err(Error::StateError(StateError::InsufficientReserves))
        ));

        //fails if output amount is greater than virtual reserves of token1
        let result = get_next_sqrt_price_from_output(
            U256::from_str("20282409603651670423947251286016").unwrap(),
            1024,
            U256::from(262145),
            true,
        );
        assert!(matches!(
            result,
            Err(Error::StateError(StateError::InsufficientReserves))
        ));

        //fails if output amount is exactly the virtual reserves of token1
        let result = get_next_sqrt_price_from_output(
            U256::from_str("20282409603651670423947251286016").unwrap(),
            1024,
            U256::from(262144),
            true,
        );
        assert!(matches!(
            result,
            Err(Error::StateError(StateError::InsufficientReserves))
        ));

        //succeeds if output amount is just less than the virtual
        let result = get_next_sqrt_price_from_output(
            U256::from_str("20282409603651670423947251286016").unwrap(),
            1024,
            U256::from(262143),
            true,
        );
        assert_eq!(
            result.unwrap(),
            U256::from_str("77371252455336267181195264").unwrap()
        );

        //puzzling echidna test
        let result = get_next_sqrt_price_from_output(
            U256::from_str("20282409603651670423947251286016").unwrap(),
            1024,
            U256::from(4),
            false,
        );
        assert!(matches!(
            result,
            Err(Error::StateError(StateError::InsufficientReserves))
        ));

        //returns input price if amount in is zero and zeroForOne = true
        let result = get_next_sqrt_price_from_output(
            U256::from_str("79228162514264337593543950336").unwrap(),
            1e17 as u128,
            U256::ZERO,
            true,
        );
        assert_eq!(
            result.unwrap(),
            U256::from_str("79228162514264337593543950336").unwrap()
        );

        //returns input price if amount in is zero and zeroForOne = false
        let result = get_next_sqrt_price_from_output(
            U256::from_str("79228162514264337593543950336").unwrap(),
            1e17 as u128,
            U256::ZERO,
            false,
        );
        assert_eq!(
            result.unwrap(),
            U256::from_str("79228162514264337593543950336").unwrap()
        );

        //output amount of 0.1 token1
        let result = get_next_sqrt_price_from_output(
            U256::from_str("79228162514264337593543950336").unwrap(),
            1e18 as u128,
            U256::from(1e17 as u128),
            false,
        );
        assert_eq!(
            result.unwrap(),
            U256::from_str("88031291682515930659493278152").unwrap()
        );

        //output amount of 0.1 token1
        let result = get_next_sqrt_price_from_output(
            U256::from_str("79228162514264337593543950336").unwrap(),
            1e18 as u128,
            U256::from(1e17 as u128),
            true,
        );
        assert_eq!(
            result.unwrap(),
            U256::from_str("71305346262837903834189555302").unwrap()
        );

        //reverts if amountOut is impossible in zero for one direction
        let result = get_next_sqrt_price_from_output(
            U256::from_str("79228162514264337593543950336").unwrap(),
            1,
            U256::MAX,
            true,
        );
        assert!(matches!(result, Err(Error::MathError(MathError::Overflow))));

        //reverts if amountOut is impossible in one for zero direction
        let result = get_next_sqrt_price_from_output(
            U256::from_str("79228162514264337593543950336").unwrap(),
            1,
            U256::MAX,
            false,
        );
        assert!(matches!(
            result,
            Err(Error::StateError(StateError::InsufficientReserves))
        ));
    }

    #[test]
    fn test_get_amount_0_delta() {
        // returns 0 if liquidity is 0
        let amount_0 = get_amount_0_delta_base(
            U256::from_str("79228162514264337593543950336").unwrap(),
            U256::from_str("79228162514264337593543950336").unwrap(),
            0,
            true,
        );

        assert_eq!(amount_0.unwrap(), U256::ZERO);

        // returns 0 if prices are equal
        let amount_0 = get_amount_0_delta_base(
            U256::from_str("79228162514264337593543950336").unwrap(),
            U256::from_str("87150978765690771352898345369").unwrap(),
            0,
            true,
        );

        assert_eq!(amount_0.unwrap(), U256::ZERO);

        // returns 0.1 amount1 for price of 1 to 1.21
        let amount_0 = get_amount_0_delta_base(
            U256::from_str("79228162514264337593543950336").unwrap(),
            U256::from_str("87150978765690771352898345369").unwrap(),
            1e18 as u128,
            true,
        )
        .unwrap();

        assert_eq!(
            amount_0.clone(),
            U256::from_str("90909090909090910").unwrap()
        );

        let amount_0_rounded_down = get_amount_0_delta_base(
            U256::from_str("79228162514264337593543950336").unwrap(),
            U256::from_str("87150978765690771352898345369").unwrap(),
            1e18 as u128,
            false,
        );

        assert_eq!(amount_0_rounded_down.unwrap(), amount_0.sub(U256_1));

        // works for prices that overflow
        let amount_0_up = get_amount_0_delta_base(
            U256::from_str("2787593149816327892691964784081045188247552").unwrap(),
            U256::from_str("22300745198530623141535718272648361505980416").unwrap(),
            1e18 as u128,
            true,
        )
        .unwrap();

        let amount_0_down = get_amount_0_delta_base(
            U256::from_str("2787593149816327892691964784081045188247552").unwrap(),
            U256::from_str("22300745198530623141535718272648361505980416").unwrap(),
            1e18 as u128,
            false,
        )
        .unwrap();

        assert_eq!(amount_0_up, amount_0_down.add(U256_1));
    }

    #[test]
    fn test_get_amount_1_delta() {
        // returns 0 if liquidity is 0
        let amount_1 = get_amount_1_delta_base(
            U256::from_str("79228162514264337593543950336").unwrap(),
            U256::from_str("79228162514264337593543950336").unwrap(),
            0,
            true,
        );

        assert_eq!(amount_1.unwrap(), U256::ZERO);

        // returns 0 if prices are equal
        let amount_1 = get_amount_1_delta_base(
            U256::from_str("79228162514264337593543950336").unwrap(),
            U256::from_str("87150978765690771352898345369").unwrap(),
            0,
            true,
        );

        assert_eq!(amount_1.unwrap(), U256::ZERO);

        // returns 0.1 amount1 for price of 1 to 1.21
        let amount_1 = get_amount_1_delta_base(
            U256::from_str("79228162514264337593543950336").unwrap(),
            U256::from_str("87150978765690771352898345369").unwrap(),
            1e18 as u128,
            true,
        )
        .unwrap();

        assert_eq!(
            amount_1.clone(),
            U256::from_str("100000000000000000").unwrap()
        );

        let amount_1_rounded_down = get_amount_1_delta_base(
            U256::from_str("79228162514264337593543950336").unwrap(),
            U256::from_str("87150978765690771352898345369").unwrap(),
            1e18 as u128,
            false,
        );

        assert_eq!(amount_1_rounded_down.unwrap(), amount_1.sub(U256_1));
    }

    #[test]
    fn test_swap_computation() {
        let sqrt_price =
            U256::from_str("1025574284609383690408304870162715216695788925244").unwrap();
        let liquidity = 50015962439936049619261659728067971248;
        let zero_for_one = true;
        let amount_in = U256::from(406);

        let sqrt_q =
            get_next_sqrt_price_from_input(sqrt_price, liquidity, amount_in, zero_for_one).unwrap();

        assert_eq!(
            sqrt_q,
            U256::from_str("1025574284609383582644711336373707553698163132913").unwrap()
        );

        let amount_0_delta = get_amount_0_delta_base(sqrt_q, sqrt_price, liquidity, true).unwrap();

        assert_eq!(amount_0_delta, U256::from(406));
    }
}
