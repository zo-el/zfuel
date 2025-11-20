# ZFuel

A high-precision Rust library for handling ZFuel types in mutual credit accounting systems. ZFuel provides fixed-point arithmetic with configurable precision (0-6 decimal places), ensuring accurate financial calculations without floating-point rounding errors.

[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)
[![Rust](https://github.com/zo-el/zfuel/actions/workflows/fuzz.yml/badge.svg)](https://github.com/zo-el/zfuel/actions/workflows/fuzz.yml)

## Features

- Variable precision support (0-6 decimal places)
- Type-safe precision handling with validation
- Mixed-precision arithmetic operations
- Full support for positive and negative values
- Precise fee calculations with configurable rates
- String parsing and formatting with full precision
- Comprehensive test coverage including fuzz testing
- No floating-point arithmetic, ensuring exact calculations
- Bounds checking on all operations
- Efficient implementation with zero-cost abstractions

## Installation

Add to your `Cargo.toml`:

```toml
[dependencies]
zfuel = "0.4.0"
```

## Quick Start

```rust
use zfuel::fuel::{ZFuel, Precision};
use zfuel::fraction::Fraction;

// Create a ZFuel amount (default precision is 6)
let amount = ZFuel::from_str("123.456789").unwrap();

// Create with specific precision
let amount_2dp = ZFuel::new(12345, Precision::new(2).unwrap()); // 123.45

// Perform arithmetic operations
let doubled = (amount + amount).unwrap();
let sum = (amount + amount_2dp).unwrap(); // Automatically uses higher precision

// Calculate fees (1%)
let fee = (amount * Fraction::new(1, 100).unwrap()).unwrap();

// Format as string
println!("Amount: {}", amount);      // "123.456789"
println!("Doubled: {}", doubled);    // "246.913578"
println!("Fee: {}", fee);            // "1.234567"
```

## Documentation

- [API Documentation](https://docs.rs/zfuel)
- [Technical Documentation](docs/technical.md) - Detailed implementation details
- [CHANGELOG](CHANGELOG.md) - Version history and changes

## Development

### Prerequisites

- Rust (nightly toolchain)
- cargo-fuzz

### Setup

```bash
# Install nightly toolchain
rustup install nightly

# Install cargo-fuzz
cargo install cargo-fuzz
```

### Testing

The project includes comprehensive test coverage:

```bash
# Run all tests (unit tests and fuzz tests)
make all

# Run only unit tests
make test

# Run only fuzz tests
make fuzz

# Run specific fuzz tests
make fuzz-fuzz_fuel
make fuzz-fuzz_fraction
make fuzz-fuzz_fuel_string
make fuzz-fuzz_fuel_operations
make fuzz-fuzz_fraction_operations
make fuzz-fuzz_fee_calculations
make fuzz-fuzz_fuel_serialization
```

### Fuzz Testing

The project includes several fuzz tests to ensure robustness:

1. `fuzz_fuel`: Basic ZFuel creation and validation
2. `fuzz_fraction`: Fraction operations and validation
3. `fuzz_fuel_string`: String parsing and validation
4. `fuzz_fuel_operations`: Arithmetic operations
5. `fuzz_fraction_operations`: Fraction arithmetic
6. `fuzz_fee_calculations`: Fee computation
7. `fuzz_fuel_serialization`: Serialization/deserialization

## Contributing

Contributions are welcome! Please see our [Contributing Guidelines](.github/CONTRIBUTING.md) for details.

## License

This project is licensed under the Apache License 2.0 - see the [LICENSE](LICENSE) file for details.
