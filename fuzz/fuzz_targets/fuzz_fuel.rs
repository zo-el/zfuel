#![no_main]

use libfuzzer_sys::fuzz_target;

use zfuel::fuel::ZFuel;

fuzz_target!(|data: i64| {
    ZFuel::new(data);
});
