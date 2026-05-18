#![no_main]
//! Property fuzz: cross-precision invariants on *every legal* pair of `ZFuel`s.
//!
//! Once `ZFuel::new` is fallible and enforces the bounded value space
//! (`±MAXVALUE / 10^(6-p)` for any precision `p`), the following are total
//! operations (no panics, no overflow) on every constructible pair of values:
//!
//!   * Scaling either operand to `Precision::DEFAULT`.
//!   * `partial_cmp` between the two operands.
//!   * `a + b`, `a - b` (may return Err when the mathematical result exceeds
//!     the value space, but never panic).
//!   * `a * Fraction` for a fee-shaped fraction (1/100).

use libfuzzer_sys::fuzz_target;
use zfuel::fraction::Fraction;
use zfuel::fuel::{Precision, ZFuel};

fuzz_target!(|data: (i64, u8, i64, u8)| {
    let (ua, pa, ub, pb) = data;
    let pa = Precision::new(pa % 7).unwrap_or(Precision::DEFAULT);
    let pb = Precision::new(pb % 7).unwrap_or(Precision::DEFAULT);

    let Ok(a) = ZFuel::new(ua, pa) else { return };
    let Ok(b) = ZFuel::new(ub, pb) else { return };

    // Scaling any *legal* value to DEFAULT is total — must never return Err.
    assert!(
        ZFuel::scale_units(a.units, pa, Precision::DEFAULT).is_ok(),
        "scale_units must succeed for legal a={}@p{}",
        a.units,
        pa.value()
    );
    assert!(
        ZFuel::scale_units(b.units, pb, Precision::DEFAULT).is_ok(),
        "scale_units must succeed for legal b={}@p{}",
        b.units,
        pb.value()
    );

    // Cross-precision comparison is total for every pair of legal values.
    assert!(
        a.partial_cmp(&b).is_some(),
        "partial_cmp must be Some for legal pair ({}@p{}, {}@p{})",
        a.units,
        pa.value(),
        b.units,
        pb.value()
    );

    // a + b and a - b never panic; they may return Err if the mathematical result
    // exceeds MAXVALUE/MINVALUE at the result precision.
    let _ = a + b;
    let _ = a - b;

    // Fee-shaped multiplication (1%) never panics for any legal a.
    let pct = Fraction::new(1, 100).unwrap();
    let _ = a * pct;
});
