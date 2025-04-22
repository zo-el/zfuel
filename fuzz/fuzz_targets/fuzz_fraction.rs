#![no_main]

use libfuzzer_sys::fuzz_target;

use zfuel::fraction::Fraction;

fuzz_target!(|n: (i64, i64)| {
    let _ = Fraction::new(n.0, n.1);
});
