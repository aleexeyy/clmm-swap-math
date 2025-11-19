use crate::error::MathError;

pub fn add_delta(x: u128, y: i128) -> Result<u128, MathError> {
    if y < 0 {
        let z = x.overflowing_sub(-y as u128);
        if z.1 {
            return Err(MathError::Underflow);
        }
        return Ok(z.0);
    } else {
        let z = x.overflowing_add(y as u128);
        if z.1 {
            return Err(MathError::Overflow);
        }
        return Ok(z.0);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add_delta_adds_positive_delta() {
        // 100 + 20 = 120
        let x: u128 = 100;
        let y: i128 = 20;

        let res = add_delta(x, y).unwrap();
        assert_eq!(res, 120u128);
    }

    #[test]
    fn add_delta_subtracts_negative_delta() {
        // 100 + (-20) = 80
        let x: u128 = 100;
        let y: i128 = -20;

        let res = add_delta(x, y).unwrap();
        assert_eq!(res, 80u128);
    }

    #[test]
    fn add_delta_zero_delta_returns_same() {
        let x: u128 = 123456789;
        let y: i128 = 0;

        let res = add_delta(x, y).unwrap();
        assert_eq!(res, x);
    }

    #[test]
    fn add_delta_positive_overflow() {
        // u128::MAX + 1 => Overflow
        let x: u128 = u128::MAX;
        let y: i128 = 1;

        let res = add_delta(x, y);
        assert!(matches!(res, Err(MathError::Overflow)));
    }

    #[test]
    fn add_delta_negative_no_underflow_at_boundary() {
        // smallest non-underflowing negative delta: x + (-x) = 0
        let x: u128 = 1_000;
        let y: i128 = -1_000;

        let res = add_delta(x, y).unwrap();
        assert_eq!(res, 0u128);
    }

    #[test]
    fn add_delta_negative_underflow_panics_in_debug() {
        // This is logically an underflow case: 100 + (-200)
        let x: u128 = 100;
        let y: i128 = -200;

        let res = add_delta(x, y);
        assert!(matches!(res, Err(MathError::Underflow)));
    }
}
