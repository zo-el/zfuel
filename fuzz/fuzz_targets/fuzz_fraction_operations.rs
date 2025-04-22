#![no_main]
use libfuzzer_sys::fuzz_target;
use zfuel::fraction::Fraction;

fuzz_target!(|data: ((i64, i64), (i64, i64))| {
    // Skip invalid inputs that would cause immediate overflow
    if data.0 .0 == i64::MIN
        || data.0 .1 == i64::MIN
        || data.1 .0 == i64::MIN
        || data.1 .1 == i64::MIN
    {
        return;
    }

    // Try to create fractions, but handle errors gracefully
    match (
        Fraction::new(data.0 .0, data.0 .1),
        Fraction::new(data.1 .0, data.1 .1),
    ) {
        (Ok(frac1), Ok(frac2)) => {
            // Test reduction and conversion
            let _ = frac1.reduce();
            let _ = frac1.to_decimal();

            // Test comparisons
            let _ = frac1 == frac2;
            let _ = frac1 < frac2;
            let _ = frac1 > frac2;
        }
        _ => {
            // Invalid inputs are expected and should be handled gracefully
        }
    }
});
