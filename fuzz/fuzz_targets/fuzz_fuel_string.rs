#![no_main]

use std::str::FromStr;

use libfuzzer_sys::fuzz_target;

use zfuel::fuel::Fuel;

fuzz_target!(|v: &[u8]| {
    if let Ok(s) = std::str::from_utf8(v) {
        let _ = Fuel::from_str(s);
        let _ = Fuel::check(s);
    }
});
