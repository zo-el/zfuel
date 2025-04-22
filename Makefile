.PHONY: all test fuzz clean

# Default target
all: test fuzz

# Run all regular tests
test:
	cargo test --all

# Run all fuzz tests
fuzz:
	cargo +nightly fuzz run fuzz_fuel -- -max_total_time=300
	cargo +nightly fuzz run fuzz_fraction -- -max_total_time=300
	cargo +nightly fuzz run fuzz_fuel_string -- -max_total_time=300
	cargo +nightly fuzz run fuzz_fuel_operations -- -max_total_time=300
	cargo +nightly fuzz run fuzz_fraction_operations -- -max_total_time=300
	cargo +nightly fuzz run fuzz_fee_calculations -- -max_total_time=300
	cargo +nightly fuzz run fuzz_fuel_serialization -- -max_total_time=300

# Run a specific fuzz test
fuzz-%:
	cargo +nightly fuzz run $* -- -max_total_time=300

# Clean up
clean:
	cargo clean
	cargo +nightly fuzz clean 