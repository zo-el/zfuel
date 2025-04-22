#![no_main]
use libfuzzer_sys::fuzz_target;
use std::ops::{Add, Sub};
use zfuel::fuel::ZFuel;

fuzz_target!(|data: (i64, i64)| {
    // Skip invalid inputs that would cause immediate overflow
    if data.0 == i64::MIN || data.1 == i64::MIN {
        return;
    }

    let fuel1 = ZFuel::new(data.0);
    let fuel2 = ZFuel::new(data.1);

    // Test arithmetic operations using operators
    let _ = fuel1 + &fuel2;
    let _ = fuel1 - &fuel2;

    // Test comparisons
    let _ = fuel1 == fuel2;
    let _ = fuel1 < fuel2;
    let _ = fuel1 > fuel2;
});
