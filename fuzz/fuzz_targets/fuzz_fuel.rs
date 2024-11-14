#![no_main]

use libfuzzer_sys::fuzz_target;

use zfuel::fuel::Fuel;

fuzz_target!(|data: i128| {
    Fuel::new(data);
});
