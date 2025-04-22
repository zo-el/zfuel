#![no_main]
use libfuzzer_sys::fuzz_target;
use zfuel::fuel::ZFuel;

fuzz_target!(|data: (i64, i64)| {
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
