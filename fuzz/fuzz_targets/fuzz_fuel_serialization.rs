#![no_main]
//! Property fuzz: serialization round-trip preserves value on *legal* ZFuel.
//!   * `to_string` never panics for any legal ZFuel.
//!   * `from_str(to_string(x)) == x` for any legal ZFuel `x` at any valid precision.
//!
//! Out-of-range inputs are rejected at construction time, so we early-return.

use std::str::FromStr;

use libfuzzer_sys::fuzz_target;
use zfuel::fuel::{Precision, ZFuel};

fuzz_target!(|data: (i64, u8)| {
    let (units, raw_p) = data;
    let precision = Precision::new(raw_p % 7).unwrap_or(Precision::DEFAULT);

    let Ok(zfuel) = ZFuel::new(units, precision) else { return };
    let serialized = zfuel.to_string();

    // Round-trip property: re-parsing must yield a value-equal ZFuel.
    let parsed = ZFuel::from_str(&serialized).unwrap_or_else(|e| {
        panic!(
            "Display output {:?} of ZFuel(units={}, precision={}) failed to re-parse: {}",
            serialized,
            units,
            precision.value(),
            e
        )
    });
    assert_eq!(parsed, zfuel);
});
