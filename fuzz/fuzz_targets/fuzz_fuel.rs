#![no_main]
//! Property fuzz: constructing a *legal* ZFuel at every valid precision must:
//!   * never panic
//!   * preserve `units` and `precision` exactly
//!   * always render via Display without panicking
//!   * round-trip via Display + FromStr to a value-equal ZFuel
//!
//! Out-of-range (units, precision) pairs are a valid rejection from `ZFuel::new`
//! (not a panic), so we early-return on `Err`.

use std::str::FromStr;

use libfuzzer_sys::fuzz_target;
use zfuel::fuel::{Precision, ZFuel};

fuzz_target!(|data: (i64, u8)| {
    let (units, raw_precision) = data;

    // Use the value modulo 7 so we cover all valid Precision values (0..=6).
    let precision = match Precision::new(raw_precision % 7) {
        Ok(p) => p,
        Err(_) => Precision::DEFAULT,
    };

    let zfuel = match ZFuel::new(units, precision) {
        Ok(z) => z,
        Err(_) => return,
    };
    assert_eq!(zfuel.units, units);
    assert_eq!(zfuel.precision, precision);

    // Display must not panic for any *legal* (units, precision) pair.
    let rendered = format!("{}", zfuel);

    // Round-trip property: the parsed value must be value-equal to the original.
    // PartialEq on ZFuel is value-based across precisions, so this is robust.
    match ZFuel::from_str(&rendered) {
        Ok(parsed) => assert_eq!(parsed, zfuel),
        Err(e) => panic!(
            "Display output {:?} (units={}, precision={}) failed to re-parse: {}",
            rendered,
            units,
            precision.value(),
            e
        ),
    }
});
