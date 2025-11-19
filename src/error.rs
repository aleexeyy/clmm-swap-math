use thiserror::Error;

#[derive(Debug, Error)]
pub enum MathError {
    #[error("Math error - overflow")]
    Overflow,
    #[error("Math error - underflow")]
    Underflow,
    #[error("Math error - out of bounds")]
    OutOfBounds,
    #[error("Math error - division by zero")]
    DivisionByZero,
    #[error("BitMath error - zero input value")]
    ZeroValue,
}

#[derive(Debug, Error)]
pub enum StateError {
    #[error("State error - sqrtPrice out of bounds")]
    SqrtPriceOutOfBounds,
    #[error("State error - sqrtPrice is 0")]
    SqrtPriceIsZero,
    #[error("State error - sqrtRatio is 0")]
    SqrtRatioIsZero,

    #[error("State error - tick out of bounds")]
    TickOutOfBounds,

    #[error("State error - liquidity is 0")]
    LiquidityIsZero,

    #[error("State error - requested amount exceeds pool reserves")]
    InsufficientReserves,
}

#[derive(Debug, Error)]
pub enum Error {
    #[error(transparent)]
    MathError(#[from] crate::error::MathError),

    #[error(transparent)]
    StateError(#[from] crate::error::StateError),
}
