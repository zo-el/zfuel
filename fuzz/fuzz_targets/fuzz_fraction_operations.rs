#![no_main]
use libfuzzer_sys::fuzz_target;
use zfuel::fraction::Fraction;

fuzz_target!(|data: ((i64, i64), (i64, i64))| {
    if let Ok(frac1) = Fraction::new(data.0 .0, data.0 .1) {
        if let Ok(frac2) = Fraction::new(data.1 .0, data.1 .1) {
            // Test reduction and conversion
            let _ = frac1.reduce();
            let _ = frac1.to_decimal();

            // Test comparisons
            let _ = frac1 == frac2;
            let _ = frac1 < frac2;
            let _ = frac1 > frac2;
        }
    }
});
