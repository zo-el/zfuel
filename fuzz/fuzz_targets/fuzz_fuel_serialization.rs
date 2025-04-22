#![no_main]
use libfuzzer_sys::fuzz_target;
use std::str::FromStr;
use zfuel::fuel::ZFuel;

fuzz_target!(|data: i64| {
    // Skip invalid inputs that would cause immediate overflow
    if data == i64::MIN {
        return;
    }

    let fuel = ZFuel::new(data);
    // Test serialization/deserialization
    let serialized = fuel.to_string();
    let _ = ZFuel::from_str(&serialized);
});
