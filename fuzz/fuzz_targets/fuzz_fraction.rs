#![no_main]
//! Property fuzz: Fraction construction and reduction invariants.
//!   * `new` either returns Ok or a well-formed error — never panics.
//!   * If `new` succeeds, `reduce()` produces a Fraction equal to the original.
//!   * `reduce()` is idempotent.
//!   * `to_decimal()` never panics.

use libfuzzer_sys::fuzz_target;
use zfuel::fraction::Fraction;

fuzz_target!(|n: (i64, i64)| {
    let result = Fraction::new(n.0, n.1);

    match result {
        Ok(f) => {
            // Denominator must be strictly positive after `new`'s normalization.
            assert!(
                f.denominator > 0,
                "denominator must be positive after construction, got {}",
                f.denominator
            );

            let r1 = f.reduce();
            let r2 = r1.reduce();

            assert_eq!(r1, r2, "reduce() must be idempotent");
            assert_eq!(r1, f, "reduce() must preserve value-equality");

            // to_decimal must not panic; its result may be infinite for very large
            // denominators-of-zero-numerator boundary cases but never NaN here.
            let _ = f.to_decimal();
        }
        Err(_) => {
            // Construction failure is acceptable: 0 denominator or i64::MIN extremes.
            // We just confirm no panic occurred.
        }
    }
});
