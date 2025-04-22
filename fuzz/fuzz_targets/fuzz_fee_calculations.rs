#![no_main]
use libfuzzer_sys::fuzz_target;
use zfuel::fuel::ZFuel;

fuzz_target!(|data: i64| {
    let amount = ZFuel::new(data);
    // Test basic operations that might be used in fee calculations
    let _ = amount + &amount;
    let _ = amount - &amount;
});
