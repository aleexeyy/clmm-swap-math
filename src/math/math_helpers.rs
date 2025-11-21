use crate::error::MathError;
use alloy_primitives::U256;

const U256_ONE: U256 = U256::ONE;
const U256_TWO: U256 = U256::from_limbs([2, 0, 0, 0]);
const U256_THREE: U256 = U256::from_limbs([3, 0, 0, 0]);

#[inline(always)]
const fn likely(b: bool) -> bool {
    // Use intrinsics if available
    #[cfg(target_arch = "x86_64")]
    {
        if b { core::intrinsics::likely(b) } else { b }
    }
    #[cfg(not(target_arch = "x86_64"))]
    b
}

#[inline(always)]
#[cold]
const fn unlikely(b: bool) -> bool {
    #[cfg(target_arch = "x86_64")]
    {
        if !b {
            core::intrinsics::unlikely(!b)
        } else {
            b
        }
    }
    #[cfg(not(target_arch = "x86_64"))]
    b
}

/// Computes `a * b / denominator` with full 256‑bit precision,
/// returning a `MathError` on overflow or division by zero.
///
/// This mirrors the Solidity `FullMath.mulDiv` behavior and underpins
/// many of the higher‑level swap and liquidity calculations.
#[inline(always)]
pub fn mul_div(a: U256, b: U256, mut denominator: U256) -> Result<U256, MathError> {
    // Early exit for division by zero
    if unlikely(denominator.is_zero()) {
        return Err(MathError::DivisionByZero);
    }

    let mm = a.mul_mod(b, U256::MAX);
    let mut prod0 = a.wrapping_mul(b);

    let (mut prod1, borrow1) = mm.overflowing_sub(prod0);
    if borrow1 {
        prod1 = prod1.wrapping_sub(U256_ONE);
    }

    if likely(prod1.is_zero()) {
        return Ok(prod0.wrapping_div(denominator));
    }

    if unlikely(denominator <= prod1) {
        return Err(MathError::Overflow);
    }

    let remainder = a.mul_mod(b, denominator);
    let (prod0_new, borrow2) = prod0.overflowing_sub(remainder);
    prod0 = prod0_new;
    if borrow2 {
        prod1 = prod1.wrapping_sub(U256_ONE);
    }

    let twos = denominator & denominator.wrapping_neg();
    denominator = denominator.wrapping_div(twos);
    prod0 = prod0.wrapping_div(twos);

    let twos_adj = twos
        .wrapping_neg()
        .wrapping_div(twos)
        .wrapping_add(U256_ONE);
    prod0 |= prod1.wrapping_mul(twos_adj);

    let mut inv = U256_THREE.wrapping_mul(denominator) ^ U256_TWO;

    macro_rules! newton_iteration {
        () => {
            inv = inv.wrapping_mul(U256_TWO.wrapping_sub(denominator.wrapping_mul(inv)))
        };
    }

    newton_iteration!();
    newton_iteration!();
    newton_iteration!();
    newton_iteration!();
    newton_iteration!();
    newton_iteration!();

    Ok(prod0.wrapping_mul(inv))
}

/// Like [`mul_div`], but rounds the result up when there is a
/// non‑zero remainder, returning an overflow error if the result
/// would exceed `U256::MAX`.
#[inline(always)]
pub fn mul_div_rounding_up(a: U256, b: U256, denominator: U256) -> Result<U256, MathError> {
    let mut result = mul_div(a, b, denominator)?;

    if a.mul_mod(b, denominator) > U256::ZERO {
        if result >= U256::MAX {
            return Err(MathError::Overflow);
        }
        result += U256::ONE;
    }
    Ok(result)
}

/// Divides `a` by `b`, rounding the result up to the next integer
/// when there is a non‑zero remainder.
///
/// This will panic on division by zero, mirroring primitive integer
/// division, so callers must ensure `b != 0`.
#[inline(always)]
pub fn div_rounding_up(a: U256, b: U256) -> U256 {
    let (quotient, remainder) = a.div_rem(b);
    if remainder.is_zero() {
        quotient
    } else {
        quotient + U256::ONE
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
