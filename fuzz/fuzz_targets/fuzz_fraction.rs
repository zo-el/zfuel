#![no_main]

use libfuzzer_sys::fuzz_target;

use zfuel::fraction::Fraction;

fuzz_target!(|n: (i128, i128)| {
    let _ = Fraction::new(n.0, n.1);
});
