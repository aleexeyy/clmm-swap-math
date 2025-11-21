use crate::error::StateError;
use crate::{U256_127, U256_128};
use alloy_primitives::{I256, U256};

pub const MIN_TICK: i32 = -887272;
pub const MAX_TICK: i32 = -MIN_TICK;

pub const MIN_SQRT_RATIO: U256 = U256::from_limbs([4295128739, 0, 0, 0]);
pub const MAX_SQRT_RATIO: U256 =
    U256::from_limbs([6743328256752651558, 17280870778742802505, 4294805859, 0]);

pub const SQRT_10001: I256 = I256::from_raw(U256::from_limbs([11745905768312294533, 13863, 0, 0]));
pub const TICK_LOW: I256 = I256::from_raw(U256::from_limbs([
    6552757943157144234,
    184476617836266586,
    0,
    0,
]));
pub const TICK_HIGH: I256 = I256::from_raw(U256::from_limbs([
    4998474450511881007,
    15793544031827761793,
    0,
    0,
]));

/// Returns the sqrt price (Q64.96 fixed‑point) at a given Uniswap V3
/// tick index, or `StateError::TickOutOfBounds` if the tick is invalid.
///
/// Use this to convert from discrete ticks to the continuous price
/// representation used by the rest of the math.
pub fn get_sqrt_ratio_at_tick(tick: i32) -> Result<U256, StateError> {
    let abs_tick = tick.unsigned_abs();

    if abs_tick > MAX_TICK as u32 {
        return Err(StateError::TickOutOfBounds);
    }

    // Start with ratio based on bit 0
    let mut ratio = if abs_tick & 1 != 0 {
        U256::from_limbs([12262481743371124737, 18445821805675392311, 0, 0])
    } else {
        U256::from_limbs([0, 0, 1, 0])
    };

    macro_rules! apply_multiplier {
        ($bit:expr, $l0:expr, $l1:expr) => {
            if abs_tick & $bit != 0 {
                ratio = ratio.wrapping_mul(U256::from_limbs([$l0, $l1, 0, 0])) >> 128;
            }
        };
    }

    apply_multiplier!(2, 6459403834229662010, 18444899583751176498);
    apply_multiplier!(4, 17226890335427755468, 18443055278223354162);
    apply_multiplier!(8, 2032852871939366096, 18439367220385604838);
    apply_multiplier!(16, 14545316742740207172, 18431993317065449817);
    apply_multiplier!(32, 5129152022828963008, 18417254355718160513);
    apply_multiplier!(64, 4894419605888772193, 18387811781193591352);
    apply_multiplier!(128, 1280255884321894483, 18329067761203520168);
    apply_multiplier!(256, 15924666964335305636, 18212142134806087854);
    apply_multiplier!(512, 8010504389359918676, 17980523815641551639);
    apply_multiplier!(1024, 10668036004952895731, 17526086738831147013);
    apply_multiplier!(2048, 4878133418470705625, 16651378430235024244);
    apply_multiplier!(4096, 9537173718739605541, 15030750278693429944);
    apply_multiplier!(8192, 9972618978014552549, 12247334978882834399);
    apply_multiplier!(16384, 10428997489610666743, 8131365268884726200);
    apply_multiplier!(32768, 9305304367709015974, 3584323654723342297);
    apply_multiplier!(65536, 14301143598189091785, 696457651847595233);
    apply_multiplier!(131072, 7393154844743099908, 26294789957452057);
    apply_multiplier!(262144, 2209338891292245656, 37481735321082);
    apply_multiplier!(524288, 10518117631919034274, 76158723);

    if tick > 0 {
        ratio = U256::MAX / ratio;
    }

    let lower_32_bits = (ratio.as_limbs()[0] & 0xFFFF_FFFF) as u32;
    Ok((ratio >> 32) + U256::from((lower_32_bits != 0) as u64))
}

const SHIFT_32: usize = 32;
const SHIFT_128: usize = 128;

const MASK_128: U256 = U256::from_limbs([u64::MAX, u64::MAX, 0, 0]);
const MASK_64: U256 = U256::from_limbs([u64::MAX, 0, 0, 0]);
const MASK_32: U256 = U256::from_limbs([u32::MAX as u64, 0, 0, 0]);
const MASK_16: U256 = U256::from_limbs([u16::MAX as u64, 0, 0, 0]);

#[inline(always)]
fn compute_msb_optimized(mut r: U256) -> (u32, U256) {
    let mut msb: u32 = 0;

    // Check bit 128 (is upper 128 bits non-zero?)
    if r > MASK_128 {
        msb |= 128;
        r >>= 128;
    }

    // Check bit 64
    if r > MASK_64 {
        msb |= 64;
        r >>= 64;
    }

    // Check bit 32
    if r > MASK_32 {
        msb |= 32;
        r >>= 32;
    }

    // Check bit 16
    if r > MASK_16 {
        msb |= 16;
        r >>= 16;
    }

    // Check bit 8
    if r > U256::from(255u64) {
        msb |= 8;
        r >>= 8;
    }

    // Check bit 4
    if r > U256::from(15u64) {
        msb |= 4;
        r >>= 4;
    }

    // Check bit 2
    if r > U256::from(3u64) {
        msb |= 2;
        r >>= 2;
    }

    // Check bit 1
    if r > U256::ONE {
        msb |= 1;
        r >>= 1;
    }

    (msb, r)
}

/// Computes the tick index corresponding to a given sqrt price
/// (Q64.96 fixed‑point), enforcing the standard Uniswap V3 bounds.
///
/// This is the primary implementation used by the rest of the crate
/// and is intended to match the Solidity logic exactly.
pub fn get_tick_at_sqrt_ratio(sqrt_price_x_96: U256) -> Result<i32, StateError> {
    if sqrt_price_x_96 < MIN_SQRT_RATIO || sqrt_price_x_96 >= MAX_SQRT_RATIO {
        return Err(StateError::SqrtPriceOutOfBounds);
    }

    let ratio = sqrt_price_x_96 << SHIFT_32;
    let (msb, _) = compute_msb_optimized(ratio);

    let mut r = if msb >= 128 {
        ratio >> (msb - 127)
    } else {
        ratio << (127 - msb)
    };

    let mut log_2: I256 = (I256::from_raw(U256::from(msb)) - I256::from_raw(U256_128)) << 64;

    macro_rules! log2_step {
        ($shift:expr) => {{
            r = r.overflowing_mul(r).0 >> U256_127;
            let f = r >> SHIFT_128;
            log_2 |= I256::from_raw(f << $shift);
            r >>= f;
        }};
    }

    log2_step!(63);
    log2_step!(62);
    log2_step!(61);
    log2_step!(60);
    log2_step!(59);
    log2_step!(58);
    log2_step!(57);
    log2_step!(56);
    log2_step!(55);
    log2_step!(54);
    log2_step!(53);
    log2_step!(52);
    log2_step!(51);
    log2_step!(50);

    let log_sqrt10001 = log_2.wrapping_mul(SQRT_10001);
    let tick_low = ((log_sqrt10001 - TICK_LOW) >> SHIFT_128).low_i32();
    let tick_high = ((log_sqrt10001 + TICK_HIGH) >> SHIFT_128).low_i32();

    Ok(if tick_low == tick_high {
        tick_low
    } else if get_sqrt_ratio_at_tick(tick_high)? <= sqrt_price_x_96 {
        tick_high
    } else {
        tick_low
    })
}

#[cfg(test)]
mod test {
    use super::*;

    use std::{ops::Sub, str::FromStr};

    #[test]
    fn test_get_sqrt_ratio_at_tick_bounds() {
        // the function should return an error if the tick is out of bounds
        if let Err(err) = get_sqrt_ratio_at_tick(MIN_TICK - 1) {
            assert!(matches!(err, StateError::TickOutOfBounds));
        } else {
            panic!("get_qrt_ratio_at_tick did not respect lower tick bound")
        }
        if let Err(err) = get_sqrt_ratio_at_tick(MAX_TICK + 1) {
            assert!(matches!(err, StateError::TickOutOfBounds));
        } else {
            panic!("get_qrt_ratio_at_tick did not respect upper tick bound")
        }
    }

    #[test]
    fn test_get_sqrt_ratio_at_tick_values() {
        // test individual values for correct results
        assert_eq!(
            get_sqrt_ratio_at_tick(MIN_TICK).unwrap(),
            U256::from(4295128739u64),
            "sqrt ratio at min incorrect"
        );
        assert_eq!(
            get_sqrt_ratio_at_tick(MIN_TICK + 1).unwrap(),
            U256::from(4295343490u64),
            "sqrt ratio at min + 1 incorrect"
        );
        assert_eq!(
            get_sqrt_ratio_at_tick(MAX_TICK - 1).unwrap(),
            U256::from_str("1461373636630004318706518188784493106690254656249").unwrap(),
            "sqrt ratio at max - 1 incorrect"
        );
        assert_eq!(
            get_sqrt_ratio_at_tick(MAX_TICK).unwrap(),
            U256::from_str("1461446703485210103287273052203988822378723970342").unwrap(),
            "sqrt ratio at max incorrect"
        );
        // checking hard coded values against solidity results
        assert_eq!(
            get_sqrt_ratio_at_tick(50).unwrap(),
            U256::from(79426470787362580746886972461u128),
            "sqrt ratio at 50 incorrect"
        );
        assert_eq!(
            get_sqrt_ratio_at_tick(100).unwrap(),
            U256::from(79625275426524748796330556128u128),
            "sqrt ratio at 100 incorrect"
        );
        assert_eq!(
            get_sqrt_ratio_at_tick(250).unwrap(),
            U256::from(80224679980005306637834519095u128),
            "sqrt ratio at 250 incorrect"
        );
        assert_eq!(
            get_sqrt_ratio_at_tick(500).unwrap(),
            U256::from(81233731461783161732293370115u128),
            "sqrt ratio at 500 incorrect"
        );
        assert_eq!(
            get_sqrt_ratio_at_tick(1000).unwrap(),
            U256::from(83290069058676223003182343270u128),
            "sqrt ratio at 1000 incorrect"
        );
        assert_eq!(
            get_sqrt_ratio_at_tick(2500).unwrap(),
            U256::from(89776708723587163891445672585u128),
            "sqrt ratio at 2500 incorrect"
        );
        assert_eq!(
            get_sqrt_ratio_at_tick(3000).unwrap(),
            U256::from(92049301871182272007977902845u128),
            "sqrt ratio at 3000 incorrect"
        );
        assert_eq!(
            get_sqrt_ratio_at_tick(4000).unwrap(),
            U256::from(96768528593268422080558758223u128),
            "sqrt ratio at 4000 incorrect"
        );
        assert_eq!(
            get_sqrt_ratio_at_tick(5000).unwrap(),
            U256::from(101729702841318637793976746270u128),
            "sqrt ratio at 5000 incorrect"
        );
        assert_eq!(
            get_sqrt_ratio_at_tick(50000).unwrap(),
            U256::from(965075977353221155028623082916u128),
            "sqrt ratio at 50000 incorrect"
        );
        assert_eq!(
            get_sqrt_ratio_at_tick(150000).unwrap(),
            U256::from(143194173941309278083010301478497u128),
            "sqrt ratio at 150000 incorrect"
        );
        assert_eq!(
            get_sqrt_ratio_at_tick(250000).unwrap(),
            U256::from(21246587762933397357449903968194344u128),
            "sqrt ratio at 250000 incorrect"
        );
        assert_eq!(
            get_sqrt_ratio_at_tick(500000).unwrap(),
            U256::from_str("5697689776495288729098254600827762987878").unwrap(),
            "sqrt ratio at 500000 incorrect"
        );
        assert_eq!(
            get_sqrt_ratio_at_tick(738203).unwrap(),
            U256::from_str("847134979253254120489401328389043031315994541").unwrap(),
            "sqrt ratio at 738203 incorrect"
        );
    }

    #[test]
    pub fn test_get_tick_at_sqrt_ratio() {
        //throws for too low
        let result = get_tick_at_sqrt_ratio(MIN_SQRT_RATIO.sub(U256::ONE));
        assert!(matches!(result, Err(StateError::SqrtPriceOutOfBounds)));

        //throws for too high
        let result = get_tick_at_sqrt_ratio(MAX_SQRT_RATIO);
        assert!(matches!(result, Err(StateError::SqrtPriceOutOfBounds)));

        //ratio of min tick
        let result = get_tick_at_sqrt_ratio(MIN_SQRT_RATIO).unwrap();
        assert_eq!(result, MIN_TICK);

        //ratio of min tick + 1
        let result = get_tick_at_sqrt_ratio(U256::from_str("4295343490").unwrap()).unwrap();
        assert_eq!(result, MIN_TICK + 1);
    }
}
