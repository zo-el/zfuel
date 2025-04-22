#![no_main]
use libfuzzer_sys::fuzz_target;
use std::ops::{Add, Sub};
use zfuel::fuel::ZFuel;

fuzz_target!(|data: i64| {
    // Skip invalid inputs that would cause immediate overflow
    if data == i64::MIN {
        return;
    }

    let amount = ZFuel::new(data);
    // Test basic operations that might be used in fee calculations
    let _ = amount + &amount;
    let _ = amount - &amount;
});
