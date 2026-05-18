#![no_main]
//! Property fuzz: arithmetic invariants on *legal* ZFuel values.
//!   * Operators must never panic — overflow returns Err, not a panic.
//!   * Addition is commutative when it succeeds.
//!   * `(a + b) - b` returns `a` when both ops succeed (additive inverse).
//!   * `a + zero == a` (identity for addition).
//!   * Comparison is consistent: `a < b` and `b < a` are mutually exclusive,
//!     and `a == b` iff neither is true.
//!
//! Out-of-range inputs are rejected at construction time, not later via panic,
//! so we early-return on `ZFuel::new` errors.

use libfuzzer_sys::fuzz_target;
use zfuel::fuel::{Precision, ZFuel};

fuzz_target!(|data: (i64, i64, u8)| {
    let (x, y, raw_p) = data;
    let precision = Precision::new(raw_p % 7).unwrap_or(Precision::DEFAULT);

    let Ok(a) = ZFuel::new(x, precision) else {
        return;
    };
    let Ok(b) = ZFuel::new(y, precision) else {
        return;
    };
    let zero = ZFuel::zero_precision(precision);

    // Operators must not panic on any legal input pair; overflow is a recoverable Err.
    let ab = a + b;
    let ba = b + a;
    let _ = a - b;
    let _ = b - a;
    let _ = -a;
    let _ = -b;

    // Commutativity of addition (when both succeed, they must agree).
    if let (Ok(s1), Ok(s2)) = (ab, ba) {
        assert_eq!(s1, s2, "addition is not commutative for ({}, {})", x, y);
    }

    // Identity for addition: a + 0 == a.
    if let Ok(s) = a + zero {
        assert_eq!(
            s,
            a,
            "addition with zero broke identity for ({}, prec={})",
            x,
            raw_p % 7
        );
    }

    // Additive inverse: (a + b) - b == a, when both operations succeed.
    if let Ok(sum) = a + b {
        if let Ok(back) = sum - b {
            assert_eq!(
                back,
                a,
                "(a+b)-b != a for ({}, {}, prec={})",
                x,
                y,
                raw_p % 7
            );
        }
    }

    // Comparison trichotomy: exactly one of <, ==, > must hold.
    let lt = a < b;
    let gt = a > b;
    let eq = a == b;
    let count = (lt as u8) + (gt as u8) + (eq as u8);
    assert_eq!(
        count, 1,
        "comparison trichotomy broken for ({}, {}): lt={}, gt={}, eq={}",
        x, y, lt, gt, eq
    );
});
