use std::ops::Shr;

use crate::error::MathError;

pub fn position(tick: i32) -> (i16, u8) {
    return (tick.shr(8) as i16, (tick % 256) as u8);
}

pub fn next_initialised_tick_within_one_word(
    tick: i32,
    tick_spacing: i32,
    lte: bool,
) -> Result<(i32, bool), MathError> {
    return Err(MathError::OutOfBounds);
}
