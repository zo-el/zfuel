# Changelog

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).
This project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

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
