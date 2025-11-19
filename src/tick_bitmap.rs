use crate::U256_1;
use crate::bit_math::{least_significant_bit, most_significant_bit};
use crate::error::MathError;
use alloy_primitives::U256;
use rustc_hash::FxHashMap;
use std::ops::Shr;

pub fn position(tick: i32) -> (i16, u8) {
    (tick.shr(8) as i16, (tick % 256) as u8)
}

pub fn get_word(bitmap: &FxHashMap<i16, U256>, word: i16) -> U256 {
    *bitmap.get(&word).unwrap_or(&U256::ZERO)
}

pub fn flip_tick(
    tick_bitmap: &mut FxHashMap<i16, U256>,
    tick: i32,
    tick_spacing: i32,
) -> Result<(), MathError> {
    if (tick % tick_spacing) != 0 {
        return Err(MathError::OutOfBounds);
    }

    let (word_pos, bit_pos) = position(tick / tick_spacing);
    let mask = U256_1 << bit_pos;
    let word = *tick_bitmap.get(&word_pos).unwrap_or(&U256::ZERO);
    tick_bitmap.insert(word_pos, word ^ mask);
    Ok(())
}

pub fn next_initialized_tick_within_one_word(
    bitmap: &FxHashMap<i16, U256>,
    tick: i32,
    tick_spacing: i32,
    lte: bool,
) -> Result<(i32, bool), MathError> {
    let mut compressed: i32 = tick / tick_spacing;

    if tick < 0 && tick % tick_spacing != 0 {
        compressed -= 1;
    }

    if lte {
        let (word_pos, bit_pos) = position(compressed);

        let mask: U256 = (U256_1 << bit_pos) - U256_1 + (U256_1 << bit_pos);
        let masked: U256 = get_word(&bitmap, word_pos) & mask;

        let initialized = !masked.is_zero();

        let next: i32 = if initialized {
            (compressed - (bit_pos - most_significant_bit(masked)?) as i32) * tick_spacing
        } else {
            (compressed - bit_pos as i32) * tick_spacing
        };
        return Ok((next, initialized));
    } else {
        let (word_pos, bit_pos) = position(compressed + 1);

        let mask: U256 = ((U256_1 << bit_pos) - U256_1).bitxor(U256::MAX);

        let masked: U256 = get_word(&bitmap, word_pos) & mask;

        let initialized = !masked.is_zero();

        let next: i32 = if initialized {
            (compressed + 1 + (least_significant_bit(masked)? - bit_pos) as i32) * tick_spacing
        } else {
            (compressed + 1 + (255u8 - bit_pos) as i32) * tick_spacing
        };
        return Ok((next, initialized));
    }
}

#[cfg(test)]

mod tests {

    use super::*;

    pub fn init_test_ticks() -> FxHashMap<i16, U256> {
        let ticks = vec![-200, -55, -4, 70, 78, 84, 139, 240, 535];
        let mut bitmap = FxHashMap::default();
        for t in ticks {
            flip_tick(&mut bitmap, t, 1).unwrap();
        }
        bitmap
    }

    #[test]
    pub fn test_position_simple() {
        assert_eq!(position(0), (0, 0));
        assert_eq!(position(1), (0, 1));
        assert_eq!(position(255), (0, 255));
        assert_eq!(position(256), (1, 0));
        assert_eq!(position(300), (1, 44));
    }

    #[test]
    pub fn test_position_negative() {
        assert_eq!(position(-1), (-1, 255));
        assert_eq!(position(-256), (-1, 0));
        assert_eq!(position(-257), (-2, 255));
    }

    // -----------------------------------------------------------------------------
    // TESTS: flip_tick correctness
    // -----------------------------------------------------------------------------
    #[test]
    pub fn test_flip_tick_roundtrip() {
        let mut bm = FxHashMap::default();
        flip_tick(&mut bm, 78, 1).unwrap();
        let (word, bit) = position(78);
        assert_eq!(get_word(&bm, word), U256_1 << bit);
        flip_tick(&mut bm, 78, 1).unwrap();
        assert_eq!(get_word(&bm, word), U256::ZERO);
    }

    // -----------------------------------------------------------------------------
    // TESTS: Right Search (lte = false)
    // -----------------------------------------------------------------------------
    #[test]
    pub fn test_right_exact_match() {
        let bm = init_test_ticks();
        let (next, init) = next_initialized_tick_within_one_word(&bm, 78, 1, false).unwrap();
        assert_eq!(next, 84);
        assert!(init);
    }

    #[test]
    pub fn test_right_between_ticks() {
        let bm = init_test_ticks();
        let (next, init) = next_initialized_tick_within_one_word(&bm, 77, 1, false).unwrap();
        assert_eq!(next, 78);
        assert!(init);
    }

    #[test]
    pub fn test_right_negative_between() {
        let bm = init_test_ticks();
        let (next, init) = next_initialized_tick_within_one_word(&bm, -56, 1, false).unwrap();
        assert_eq!(next, -55);
        assert!(init);
    }

    #[test]
    pub fn test_right_cross_to_next_word() {
        let bm = init_test_ticks();
        let (next, init) = next_initialized_tick_within_one_word(&bm, 255, 1, false).unwrap();
        assert_eq!(next, 511);
        assert!(!init);
    }

    #[test]
    pub fn test_right_find_in_next_word() {
        let mut bm = init_test_ticks();
        flip_tick(&mut bm, 340, 1).unwrap();
        let (next, init) = next_initialized_tick_within_one_word(&bm, 328, 1, false).unwrap();
        assert_eq!(next, 340);
        assert!(init);
    }
}
