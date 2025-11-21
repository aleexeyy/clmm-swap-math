use crate::error::MathError;
use alloy_primitives::U256;

/// Returns the index (0–255) of the most significant set bit in a `U256`,
/// or `MathError::ZeroValue` if the input is zero.
///
/// Useful for fast order‑of‑magnitude / log2‑like operations on large integers.
pub fn most_significant_bit(x: U256) -> Result<u8, MathError> {
    if x.is_zero() {
        return Err(MathError::ZeroValue);
    }
    Ok(255 - x.leading_zeros() as u8)
}

/// Returns the index (0–255) of the least significant set bit in a `U256`,
/// or `MathError::ZeroValue` if the input is zero.
///
/// This is typically used when scanning bitmaps from the right to find
/// the first initialized position.
pub fn least_significant_bit(x: U256) -> Result<u8, MathError> {
    if x.is_zero() {
        return Err(MathError::ZeroValue);
    }
    Ok(x.trailing_zeros() as u8)
}

#[cfg(test)]
mod tests {
    use super::*;

    // ------------------------- most_significant_bit tests -------------------------

    #[test]
    fn msb_errors_on_zero() {
        let x = U256::ZERO;
        let res = most_significant_bit(x);
        assert!(matches!(res, Err(MathError::ZeroValue)));
    }

    #[test]
    fn msb_of_power_of_two() {
        // 1 << 7  = bit 7
        let x = U256::from(1u64 << 7);
        let res = most_significant_bit(x).unwrap();
        assert_eq!(res, 7);
    }

    #[test]
    fn msb_of_multiple_bits() {
        // binary: 1001_0100 (MSB = bit 7)
        let x = U256::from(0b1001_0100u64);
        let res = most_significant_bit(x).unwrap();
        assert_eq!(res, 7);
    }

    #[test]
    fn msb_of_max_u256() {
        // U256::MAX has MSB = 255
        let x = U256::MAX;
        let res = most_significant_bit(x).unwrap();
        assert_eq!(res, 255);
    }

    // ------------------------- least_significant_bit tests -------------------------

    #[test]
    fn lsb_errors_on_zero() {
        let x = U256::ZERO;
        let res = least_significant_bit(x);
        assert!(matches!(res, Err(MathError::ZeroValue)));
    }

    #[test]
    fn lsb_of_power_of_two() {
        // 1 << 12 => LSB = 12
        let x = U256::from(1u64 << 12);
        let res = least_significant_bit(x).unwrap();
        assert_eq!(res, 12);
    }

    #[test]
    fn lsb_of_multiple_bits() {
        // binary: 1011001000 -> LSB is position 3 (0-based)
        let x = U256::from(0b1011001000u64);
        let res = least_significant_bit(x).unwrap();
        assert_eq!(res, 3);
    }

    #[test]
    fn lsb_of_max_u256() {
        // U256::MAX ends with ...1111, so LSB = 0
        let x = U256::MAX;
        let res = least_significant_bit(x).unwrap();
        assert_eq!(res, 0);
    }
}
