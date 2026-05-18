#![no_main]
//! Property fuzz: parser robustness and roundtrip.
//!   * `from_str` must never panic on arbitrary input.
//!   * `check` must never panic on arbitrary input.
//!   * `from_str` and `check` must agree: for any input, `check(s).is_ok()`
//!     implies `from_str(s).is_ok()` (and the parsed value is non-negative).
//!   * If parsing succeeds, Display → FromStr roundtrip must produce an equal value.

use std::str::FromStr;

use libfuzzer_sys::fuzz_target;
use zfuel::fuel::ZFuel;

fuzz_target!(|v: &[u8]| {
    let s = match std::str::from_utf8(v) {
        Ok(s) => s,
        Err(_) => return,
    };

    let parsed = ZFuel::from_str(s);
    let checked = ZFuel::check(s);

    // Cross-consistency: check(s).is_ok() implies from_str(s).is_ok() AND non-negative.
    if checked.is_ok() {
        match &parsed {
            Ok(z) => assert!(
                z.units >= 0,
                "check accepted {:?} but parsed value is negative (units={})",
                s,
                z.units
            ),
            Err(e) => panic!(
                "check accepted {:?} but from_str rejected it: {}",
                s, e
            ),
        }
    }

    // Roundtrip property: any successfully parsed value must Display + re-parse to itself.
    if let Ok(z) = parsed {
        let rendered = format!("{}", z);
        let reparsed = ZFuel::from_str(&rendered).unwrap_or_else(|e| {
            panic!(
                "Display of valid ZFuel ({:?} from input {:?}) failed to re-parse: {}",
                rendered, s, e
            )
        });
        assert_eq!(reparsed, z);
    }
});
