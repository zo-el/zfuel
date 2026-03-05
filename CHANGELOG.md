# Changelog

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).
This project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.6.1] - 2026-03-05

### Added

- new fn for Precision (new_min and new_max)

## [0.6.0] - 2025-12-07

### Changed

- **BREAKING**: `Mul<Fraction>` now uses precision 6 (maximum) for all results to ensure fractional results can be represented exactly
  - Previously, multiplication preserved the input precision, which could cause fractional results to be truncated to 0 at low precision
  - Now, `10 * 1% = 0.1` regardless of input precision (all results use precision 6)
  - Example: `ZFuel::from_str("10") * Fraction::new(1, 100)` now returns `0.1` (precision 6) instead of `0` (precision 0)
- **BREAKING**: `Mul<Fraction>` now rounds up (away from zero) instead of truncating when there's a remainder
  - Previously, results were truncated: `1 * 1/3 = 0.333333` (truncated)
  - Now, results are rounded up: `1 * 1/3 = 0.333334` (rounded up)
  - This ensures no value is lost due to truncation in financial calculations

## [0.5.0] - 2025-12-07

### Added

- `is_valid_precision()` method to check if a ZFuel value can be represented at an expected precision
- Precision information in Debug output (`Fuel(123.45) precision(2)`)
- Precision preservation during serialization/deserialization - precision is now detected from string format

### Changed

- **BREAKING**: Comparison operators (`==`, `!=`, `<`, `>`, `<=`, `>=`) now use value-based comparison, ignoring precision differences
  - Previously, `ZFuel(10, precision=0) == ZFuel(10, precision=6)` would return `false`
  - Now, `ZFuel(10, precision=0) == ZFuel(10, precision=6)` returns `true` (same numeric value)
- `from_str()` now detects and preserves precision from the input string
  - `"123.45"` is parsed with precision 2
  - `"123.450"` is parsed with precision 3 (trailing zeros are significant)
  - Hex values (`0x...`) use default precision 6

### Fixed

- Precision is now preserved when serializing and deserializing ZFuel values
- String parsing now correctly detects precision from the number of decimal places

## [0.4.1] - 2025-12-04

### Added

- Serialization support for `Precision` type (`Serialize` and `Deserialize` derives)

### Changed

- `ZFuel::zero()` now uses default precision (no parameter required) for improved API ergonomics
- `ZFuel::zero_default()` renamed to `ZFuel::zero_precision(precision: Precision)` for clarity

## [0.4.0] - 2025-01-XX

### Added

- Variable precision support for ZFuel (0-6 decimal places)
- `Precision` type for type-safe precision handling with validation
- `to_precision()` method to convert ZFuel between different precision levels
- Precision-aware arithmetic operations that automatically use higher precision for results
- Comprehensive test suite for precision operations including property-based tests
- Performance benchmarks for precision operations

### Changed

- `ZFuel::new()` now requires a `Precision` parameter (use `new_with_default_precision()` for default behavior)
- `ZFuel::zero()` now requires a `Precision` parameter (use `zero_default()` for default behavior)
- Arithmetic operations (`Add`, `Sub`) now handle mixed precision by scaling to the higher precision
- Display formatting respects the instance's precision level
- Optimized arithmetic operations with fast path for same-precision operands
- Updated fuzz tests to work with new precision-aware API

### Fixed

- Fuzz tests updated to use new `ZFuel::new()` signature with precision parameter

## [0.3.1] - 2025-04-22

### Update

- updated holochain_wasmer_common to v0.0.101

## [0.3.0] - 2025-04-22

### Update

- fuzz testing and production ready code

## [0.2.2] - 2025-02-06

### Update

- holochain_wasmer_common updated to "0.0.99"

## [0.2.1] - 2025-02-03

### Update

- added the check function for fuel type and updated Fractions to handle 0 denominators

## [0.2.0] - 2025-02-02

### Update

- update ZFuel from using u128 to u64

## [0.1.1] - 2024-12-10

### Update

- impl WasmError for ZFuelError type

## [0.1.1] - 2024-12-10

### Changed

- serde version to `0.1`

## [0.1.0] - 2024-12-10

### Added

- ZFuel Type
