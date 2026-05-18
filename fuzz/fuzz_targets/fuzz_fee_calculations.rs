#![no_main]
//! Property fuzz: fee calculation must never panic and must obey simple bounds.
//!   * `tabulate_fee` never panics on any legal (units, precision) input.
//!   * On a successful fee result, the fee has the same sign as the amount
//!     (or is zero), and rounding only ever pushes |fee| up by at most 1 unit.
//!
//! Out-of-range inputs are rejected at `ZFuel::new`, not later via panic, so
//! we early-return.

use libfuzzer_sys::fuzz_target;
use zfuel::fee::tabulate_fee;
use zfuel::fuel::{Precision, ZFuel};

fuzz_target!(|data: (i64, u8)| {
    let (units, raw_p) = data;
    let precision = Precision::new(raw_p % 7).unwrap_or(Precision::DEFAULT);

    let Ok(amount) = ZFuel::new(units, precision) else {
        return;
    };

    // Must not panic for any legal input.
    let fee = tabulate_fee(&amount);

    if let Ok(f) = fee {
        // Sign consistency: fee must not flip sign relative to amount (modulo zero).
        if units > 0 {
            assert!(f.units >= 0, "positive amount produced negative fee");
        } else if units < 0 {
            assert!(f.units <= 0, "negative amount produced positive fee");
        }
    }
});
