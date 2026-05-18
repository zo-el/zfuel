#![no_main]
//! Property fuzz: Fraction non-arithmetic invariants.
//!
//! Note: `&Fraction +/-/*/÷ &Fraction` is documented as NOT overflow-checked; exercising
//! those operators with adversarial inputs would panic in debug builds (which is the
//! correct, defensive behavior). This target focuses on the safe surface area:
//!   * `reduce()` is idempotent and preserves value-equality.
//!   * Equality is symmetric and reflexive.
//!   * Comparison respects equality (a == b => !(a < b) && !(a > b)).

use libfuzzer_sys::fuzz_target;
use zfuel::fraction::Fraction;

fuzz_target!(|data: ((i64, i64), (i64, i64))| {
    let (Ok(f1), Ok(f2)) = (
        Fraction::new(data.0 .0, data.0 .1),
        Fraction::new(data.1 .0, data.1 .1),
    ) else {
        return;
    };

    // reduce() idempotency.
    let r1 = f1.reduce();
    let r2 = r1.reduce();
    assert_eq!(r1, r2);

    // reduce() preserves equality.
    assert_eq!(r1, f1);

    // Reflexivity of equality.
    assert!(f1 == f1);

    // Symmetry of equality.
    assert_eq!(f1 == f2, f2 == f1);

    // Equality implies neither <, > (when both decimal forms are finite).
    let d1 = f1.to_decimal();
    let d2 = f2.to_decimal();
    if d1.is_finite() && d2.is_finite() && f1 == f2 {
        assert!(!(f1 < f2));
        assert!(!(f1 > f2));
    }
});
