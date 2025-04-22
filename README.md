# ZFuel

A Rust library for handling ZFuel types in a mutual credit accounting system.

## Development

### Prerequisites

- Rust (nightly toolchain)
- cargo-fuzz

### Installation

```bash
# Install nightly toolchain
rustup install nightly

# Install cargo-fuzz
cargo install cargo-fuzz
```

### Running Tests

The project includes both regular unit tests and fuzz tests. You can use the Makefile to run them:

```bash
# Run all tests (unit tests and fuzz tests)
make all

# Run only unit tests
make test

# Run only fuzz tests
make fuzz

# Run a specific fuzz test
make fuzz-fuzz_fuel
make fuzz-fuzz_fraction
make fuzz-fuzz_fuel_string
make fuzz-fuzz_fuel_operations
make fuzz-fuzz_fraction_operations
make fuzz-fuzz_fee_calculations
make fuzz-fuzz_fuel_serialization
```

### Fuzz Tests Coverage

The project includes several fuzz tests to ensure robustness:

1. `fuzz_fuel`: Tests basic ZFuel creation
2. `fuzz_fraction`: Tests Fraction creation and validation
3. `fuzz_fuel_string`: Tests string parsing and validation
4. `fuzz_fuel_operations`: Tests arithmetic operations and comparisons
5. `fuzz_fraction_operations`: Tests fraction operations and conversions
6. `fuzz_fee_calculations`: Tests basic fee-related operations
7. `fuzz_fuel_serialization`: Tests serialization/deserialization

### CI/CD

The project uses GitHub Actions to run all tests on every push and pull request to the main branch. The workflow is defined in `.github/workflows/fuzz.yml`.
