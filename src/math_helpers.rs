use crate::error::MathError;
use alloy_primitives::U256;

pub fn mul_div(a: U256, b: U256, mut denominator: U256) -> Result<U256, MathError> {
    let mm = a.mul_mod(b, U256::MAX);

    let mut prod0 = a.overflowing_mul(b).0;
    let mut prod1 = mm
        .overflowing_sub(prod0)
        .0
        .overflowing_sub(U256::from(mm.lt(&prod0) as u8))
        .0;

    if prod1 == U256::ZERO {
        if denominator == U256::ZERO {
            return Err(MathError::DivisionByZero);
        }
        return Ok(prod0.wrapping_div(denominator));
    }

    if denominator <= prod1 {
        return Err(MathError::Overflow);
    }

    let remainder = a.mul_mod(b, denominator);

    prod1 = prod1
        .overflowing_sub(U256::from(remainder.gt(&prod0) as u8))
        .0;
    prod0 = prod0.overflowing_sub(remainder).0;

    let mut twos = denominator.wrapping_neg() & denominator;

    denominator = denominator.wrapping_div(twos);

    prod0 = prod0.wrapping_div(twos);

    twos = twos
        .wrapping_neg()
        .wrapping_div(twos)
        .overflowing_add(U256::ONE)
        .0;

    prod0 |= prod1 * twos;

    let mut inv: U256 = (U256::from(3u8) * denominator).bitxor(U256::from(2u8));

    inv *= U256::from(2u8) - denominator * inv;
    inv *= U256::from(2u8) - denominator * inv;
    inv *= U256::from(2u8) - denominator * inv;
    inv *= U256::from(2u8) - denominator * inv;
    inv *= U256::from(2u8) - denominator * inv;
    inv *= U256::from(2u8) - denominator * inv;

    return Ok(prod0 * inv);
}

pub fn mul_div_rounding_up(a: U256, b: U256, denominator: U256) -> Result<U256, MathError> {
    let mut result = mul_div(a, b, denominator)?;

    if a.mul_mod(b, denominator) > U256::ZERO {
        if result >= U256::MAX {
            return Err(MathError::Overflow);
        }
        result += U256::ONE;
    }
    return Ok(result);
}

// unsafe
pub fn div_rounding_up(a: U256, b: U256) -> U256 {
    let (quotient, remainder) = a.div_rem(b);
    if remainder.is_zero() {
        return quotient;
    } else {
        return quotient + U256::ONE;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ------------------------- mul_div tests -------------------------

    #[test]
    fn mul_div_simple_division() {
        let a = U256::from(10u8);
        let b = U256::from(20u8);
        let denominator = U256::from(5u8);

        let result = mul_div(a, b, denominator).unwrap();
        assert_eq!(result, U256::from(40u8));
    }

    #[test]
    fn mul_div_division_by_zero() {
        let a = U256::from(10u8);
        let b = U256::from(20u8);
        let denominator = U256::ZERO;

        let result = mul_div(a, b, denominator);
        assert!(matches!(result, Err(MathError::DivisionByZero)));
    }

    #[test]
    fn mul_div_no_overflow_simple() {
        let a = U256::from(1000u16);
        let b = U256::from(2000u16);
        let denominator = U256::from(100u8);

        let result = mul_div(a, b, denominator).unwrap();
        assert_eq!(result, U256::from(20_000u16));
    }

    #[test]
    fn mul_div_large_multiplication_no_overflow() {
        // Large values where a * b does not fit in 256 bits, but
        // the final quotient still fits in 256 bits.
        // (2^256 - 1) * (2^256 - 1) / (2^256 - 1) = 2^256 - 1
        let a = U256::MAX;
        let b = U256::MAX;
        let denominator = U256::MAX;

        let result = mul_div(a, b, denominator).unwrap();
        assert_eq!(result, U256::MAX);
    }

    #[test]
    fn mul_div_result_overflow() {
        // Quotient would exceed U256
        // (2^256 - 1) * 2 / 1 = 2^257 - 2, which cannot fit in 256 bits
        let a = U256::MAX;
        let b = U256::from(2u8);
        let denominator = U256::ONE;

        let result = mul_div(a, b, denominator);
        assert!(matches!(result, Err(MathError::Overflow)));
    }

    #[test]
    fn mul_div_rounding_down_behavior() {
        // 7 * 10 / 8 = 70 / 8 = 8.75, floor is 8
        let a = U256::from(7u8);
        let b = U256::from(10u8);
        let denominator = U256::from(8u8);

        let result = mul_div(a, b, denominator).unwrap();
        assert_eq!(result, U256::from(8u32));
    }

    // ------------------------- mul_div_rounding_up tests -------------------------

    #[test]
    fn mul_div_rounding_up_exact_division() {
        // 20 * 10 / 5 = 40 exactly, so rounding_up should be same as mul_div
        let a = U256::from(20u8);
        let b = U256::from(10u8);
        let denominator = U256::from(5u8);

        let result = mul_div_rounding_up(a, b, denominator).unwrap();
        assert_eq!(result, U256::from(40u8));
    }

    #[test]
    fn mul_div_rounding_up_non_exact() {
        // 7 * 10 / 3 = 70 / 3 = 23.333..., floor is 23, rounding_up should give 24
        let a = U256::from(7u8);
        let b = U256::from(10u8);
        let denominator = U256::from(3u8);

        let result = mul_div_rounding_up(a, b, denominator).unwrap();
        assert_eq!(result, U256::from(24u8));
    }

    #[test]
    fn mul_div_rounding_up_division_by_zero() {
        let a = U256::from(10u8);
        let b = U256::from(20u8);
        let denominator = U256::ZERO;

        let result = mul_div_rounding_up(a, b, denominator);
        assert!(matches!(result, Err(MathError::DivisionByZero)));
    }

    #[test]
    fn mul_div_rounding_up_propagates_overflow_from_mul_div() {
        // When mul_div already overflows, rounding_up should propagate that overflow.
        let a = U256::MAX;
        let b = U256::from(2u8);
        let denominator = U256::ONE;

        let result = mul_div_rounding_up(a, b, denominator);
        assert!(matches!(result, Err(MathError::Overflow)));
    }

    // ------------------------- div_rounding_up tests -------------------------

    #[test]
    fn div_rounding_up_exact_division() {
        // 10 / 5 = 2 exactly, no rounding
        let a = U256::from(10u8);
        let b = U256::from(5u8);

        let result = div_rounding_up(a, b);
        assert_eq!(result, U256::from(2u8));
    }

    #[test]
    fn div_rounding_up_non_exact() {
        // 10 / 3 = 3.333..., ceil => 4
        let a = U256::from(10u8);
        let b = U256::from(3u8);

        let result = div_rounding_up(a, b);
        assert_eq!(result, U256::from(4u8));
    }

    #[test]
    fn div_rounding_up_large_non_exact() {
        // (2^256 - 1) / (2^256 - 2) is not an integer, should round up to 2
        let a = U256::MAX;
        let b = U256::MAX - U256::ONE;

        let result = div_rounding_up(a, b);
        assert_eq!(result, U256::from(2u8));
    }

    #[test]
    #[should_panic] // div_rem(b = 0) should panic internally
    fn div_rounding_up_division_by_zero_panics() {
        let a = U256::from(10u8);
        let b = U256::ZERO;

        let _ = div_rounding_up(a, b);
    }
}
