#![no_main]
use libfuzzer_sys::fuzz_target;
use zfuel::fuel::{Precision, ZFuel};

fuzz_target!(|data: i64| {
    // Skip invalid inputs that would cause immediate overflow
    if data == i64::MIN {
        return;
    }

    let amount = ZFuel::new(data, Precision::DEFAULT);
    // Test basic operations that might be used in fee calculations
    let _ = amount + &amount;
    let _ = amount - &amount;
});
