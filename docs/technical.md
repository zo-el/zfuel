# ZFuel Technical Documentation

## Implementation Details

### Precision and Range

- ZFuel is implemented as a fixed-point number with 6 decimal places (1/1,000,000th precision)
- Uses i64 internally to represent units, allowing for a range of approximately ±9.223 trillion ZFuel
- All calculations are performed using integer arithmetic to avoid floating-point precision issues
- String representations maintain full precision through the decimal point

### Error Handling

The library defines several error types:

- `Range`: Indicates when a value exceeds the allowed range
- `FractionOverflow`: Occurs when multiplying by a fraction would cause overflow
- `Generic`: For other error conditions (should be avoided in favor of specific errors)

### Core Components

#### ZFuel

- Main type for representing ZFuel amounts
- Implements arithmetic operations (Add, Sub, Mul, Div) with proper overflow checking
- Supports serialization/deserialization to/from human-readable strings
- Handles both positive and negative values with full precision

#### Fraction

- Represents rational numbers for precise calculations
- Used for fee calculations and percentage operations
- Implements reduction to simplest form
- Supports basic arithmetic operations

#### Fee Calculation

- Implements a 1% fee structure
- Uses Fraction type for precise calculations
- Handles edge cases for very small transactions
- Rounds up fees on extremely small transactions to reflect system costs

## Edge Cases and Special Handling

### Small Transactions

- For transactions below 0.0001 ZFuel, fees are rounded up
- This ensures the system can handle micro-transactions while maintaining economic viability
- Example: A 0.000123 ZFuel transaction has a fee of 0.000002 (rounded up from 0.00000123)

### Large Numbers

- The library can handle values up to approximately 9.223 trillion ZFuel
- All operations are checked for overflow
- String parsing validates input ranges before conversion

### Precision Handling

- Division operations maintain precision by using the Fraction type
- Multiplication operations are carefully ordered to avoid overflow
- String formatting preserves all significant digits

## Testing Coverage

### Unit Tests

- Basic arithmetic operations
- String parsing and formatting
- Edge case handling
- Fee calculations

### Fuzz Tests

- Random input testing for all operations
- String parsing validation
- Arithmetic operation stress testing
- Serialization/deserialization testing

## Performance Considerations

- Uses `opt-level = "z"` for both dev and release profiles
- Implements Copy trait where appropriate for efficient value passing
- Avoids unnecessary allocations in string operations
- Uses checked arithmetic operations to prevent overflow

## Security Considerations

- All arithmetic operations are bounds-checked
- String parsing validates input ranges
- No floating-point arithmetic is used
- Serialization/deserialization maintains precision
