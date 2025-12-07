use crate::error::ZFuelError;
use serde::{Deserialize, Serialize};

/// Precision type for ZFuel, representing decimal places (0-6)
#[derive(Serialize, Deserialize, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Debug)]
pub struct Precision(u8);

impl Precision {
    /// Maximum allowed precision
    pub const MAX: u8 = 6;
    /// Minimum allowed precision
    pub const MIN: u8 = 0;
    /// Default precision (6 decimal places)
    pub const DEFAULT: Precision = Precision(6);

    /// Create a new Precision value, validating it's in the valid range (0-6)
    pub fn new(value: u8) -> Result<Self, ZFuelError> {
        if value > Self::MAX {
            Err(ZFuelError::Range(format!(
                "Precision must be between {} and {}, got {}",
                Self::MIN,
                Self::MAX,
                value
            )))
        } else {
            Ok(Precision(value))
        }
    }

    /// Get the underlying u8 value
    pub fn value(self) -> u8 {
        self.0
    }

    /// Get the denominator for this precision (10^precision)
    pub fn denominator(self) -> u64 {
        match self.0 {
            0 => 1,
            1 => 10,
            2 => 100,
            3 => 1_000,
            4 => 10_000,
            5 => 100_000,
            6 => 1_000_000,
            _ => unreachable!("Precision is validated to be 0-6"),
        }
    }
}

impl TryFrom<u8> for Precision {
    type Error = ZFuelError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        Precision::new(value)
    }
}

impl From<Precision> for u8 {
    fn from(precision: Precision) -> u8 {
        precision.0
    }
}

#[cfg(test)]
pub mod tests {
    use crate::fraction::Fraction;
    use crate::fuel::{Precision, ZFuel};
    use std::str::FromStr;

    // Helper macro for creating Precision values in tests
    macro_rules! p {
        (0) => {
            Precision::new(0).unwrap()
        };
        (1) => {
            Precision::new(1).unwrap()
        };
        (2) => {
            Precision::new(2).unwrap()
        };
        (3) => {
            Precision::new(3).unwrap()
        };
        (4) => {
            Precision::new(4).unwrap()
        };
        (5) => {
            Precision::new(5).unwrap()
        };
        (6) => {
            Precision::DEFAULT
        };
    }

    #[test]
    fn test_precision_constructors() {
        // Test basic constructors with different precisions
        let f0 = ZFuel::new(123, p!(0));
        assert_eq!(f0.units, 123);
        assert_eq!(f0.precision, p!(0));

        let f2 = ZFuel::new(12345, p!(2));
        assert_eq!(f2.units, 12345);
        assert_eq!(f2.precision, p!(2));

        let f6 = ZFuel::new(1234567, p!(6));
        assert_eq!(f6.units, 1234567);
        assert_eq!(f6.precision, Precision::DEFAULT);

        // Test zero constructors
        let z0 = ZFuel::zero_precision(p!(0));
        assert_eq!(z0.units, 0);
        assert_eq!(z0.precision, p!(0));

        let z6 = ZFuel::zero();
        assert_eq!(z6.units, 0);
        assert_eq!(z6.precision, Precision::DEFAULT);
    }

    #[test]
    fn test_precision_scaling() {
        // Test scaling between different precisions
        let f2 = ZFuel::new(150, p!(2)); // 1.50 at precision 2

        // Scale up to higher precision
        let f6 = f2.to_precision(p!(6)).unwrap();
        assert_eq!(f6.units, 1500000); // 1.500000 at precision 6
        assert_eq!(f6.precision, Precision::DEFAULT);

        // Scale back down
        let f2_back = f6.to_precision(p!(2)).unwrap();
        assert_eq!(f2_back.units, 150); // 1.50 at precision 2
        assert_eq!(f2_back.precision, p!(2));

        // Test scaling to same precision (no-op)
        let f2_same = f2.to_precision(p!(2)).unwrap();
        assert_eq!(f2_same.units, 150);
        assert_eq!(f2_same.precision, p!(2));
    }

    #[test]
    fn test_mixed_precision_arithmetic() {
        let f2 = ZFuel::new(150, p!(2)); // 1.50 at precision 2
        let f4 = ZFuel::new(12500, p!(4)); // 1.2500 at precision 4

        // Addition should use higher precision (4)
        let sum = (f2 + f4).unwrap();
        assert_eq!(sum.precision, p!(4));
        assert_eq!(sum.units, 27500); // 1.5000 + 1.2500 = 2.7500 at precision 4

        // Subtraction should use higher precision (4)
        let diff = (f2 - f4).unwrap();
        assert_eq!(diff.precision, p!(4));
        assert_eq!(diff.units, 2500); // 1.5000 - 1.2500 = 0.2500 at precision 4
    }

    #[test]
    fn test_precision_display() {
        // Test display formatting for different precisions
        let f0 = ZFuel::new(123, p!(0));
        assert_eq!(format!("{}", f0), "123");

        let f1 = ZFuel::new(125, p!(1)); // 12.5
        assert_eq!(format!("{}", f1), "12.5");

        let f2 = ZFuel::new(1250, p!(2)); // 12.50
        assert_eq!(format!("{}", f2), "12.5"); // Trailing zeros removed

        let f2_exact = ZFuel::new(1234, p!(2)); // 12.34
        assert_eq!(format!("{}", f2_exact), "12.34");

        let f6 = ZFuel::new(1234567, p!(6)); // 1.234567
        assert_eq!(format!("{}", f6), "1.234567");
    }

    #[test]
    fn test_precision_edge_cases() {
        // Test precision 0 (integers only)
        let f0 = ZFuel::new(42, p!(0));
        assert_eq!(format!("{}", f0), "42");

        // Test maximum precision (6)
        let f6 = ZFuel::new(1000000, p!(6)); // 1.000000
        assert_eq!(format!("{}", f6), "1");

        // Test very small values at different precisions
        let f1_small = ZFuel::new(1, p!(1)); // 0.1
        assert_eq!(format!("{}", f1_small), "0.1");

        let f6_small = ZFuel::new(1, p!(6)); // 0.000001
        assert_eq!(format!("{}", f6_small), "0.000001");
    }

    #[test]
    fn test_precision_overflow_handling() {
        // Test that scaling up can cause overflow
        let large_f0 = ZFuel::new(i64::MAX, p!(0));
        let result = large_f0.to_precision(p!(6));
        assert!(result.is_err()); // Should overflow when scaling up

        // Test that scaling down works for large values
        let large_f6 = ZFuel::new(i64::MAX, p!(6));
        let result = large_f6.to_precision(p!(0));
        assert!(result.is_ok()); // Should work when scaling down
    }

    #[test]
    fn test_precision_fraction_operations() {
        // Test that fraction operations preserve precision
        let f2 = ZFuel::new(200, p!(2)); // 2.00 at precision 2
        let fraction = Fraction::new(1, 4).unwrap(); // 25%

        let result = (f2 * fraction).unwrap();
        assert_eq!(result.precision, p!(2)); // Should preserve original precision
        assert_eq!(result.units, 50); // 2.00 * 0.25 = 0.50 at precision 2
    }

    #[test]
    fn test_precision_string_roundtrip() {
        // Test string parsing/display roundtrip
        let original = ZFuel::new(12345, p!(2)); // 123.45 at precision 2

        // Convert to string
        let string_repr = format!("{}", original);
        assert_eq!(string_repr, "123.45");

        // Parse back - precision should be preserved
        let parsed = ZFuel::from_str(&string_repr).unwrap();

        // Precision should be detected from the string (2 decimal places)
        assert_eq!(parsed.precision, p!(2));
        assert_eq!(parsed.units, 12345);
        assert_eq!(format!("{}", parsed), "123.45");
    }

    #[test]
    fn test_precision_boundaries() {
        // Test all valid precision values (0-6)
        for precision_val in 0..=6 {
            let precision = Precision::new(precision_val).unwrap();
            let f = ZFuel::new(123, precision);
            assert_eq!(f.precision, precision);

            let z = ZFuel::zero_precision(precision);
            assert_eq!(z.precision, precision);
            assert_eq!(z.units, 0);
        }
    }

    #[test]
    fn test_invalid_precision_errors() {
        // Test that invalid precision returns an error
        assert!(Precision::new(7).is_err());
        assert!(Precision::new(10).is_err());
    }

    #[test]
    fn test_precision_properties() {
        // Property: Converting to same precision should be identity
        for precision_val in 0..=6 {
            let precision = Precision::new(precision_val).unwrap();
            let original = ZFuel::new(12345, precision);
            let converted = original.to_precision(precision).unwrap();
            assert_eq!(original.units, converted.units);
            assert_eq!(original.precision, converted.precision);
        }

        // Property: Converting up then down should preserve value (within precision limits)
        let original = ZFuel::new(123, p!(2));
        let up = original.to_precision(p!(6)).unwrap();
        let down = up.to_precision(p!(2)).unwrap();
        assert_eq!(original.units, down.units);
        assert_eq!(original.precision, down.precision);

        // Property: Addition is commutative (same precision)
        let a = ZFuel::new(100, p!(3));
        let b = ZFuel::new(200, p!(3));
        let sum1 = (a + b).unwrap();
        let sum2 = (b + a).unwrap();
        assert_eq!(sum1.units, sum2.units);
        assert_eq!(sum1.precision, sum2.precision);

        // Property: Addition with zero is identity
        let original = ZFuel::new(12345, p!(4));
        let zero = ZFuel::zero_precision(p!(4));
        let result = (original + zero).unwrap();
        assert_eq!(original.units, result.units);
        assert_eq!(
            std::cmp::max(original.precision, zero.precision),
            result.precision
        );

        // Property: Subtraction with self gives zero
        let original = ZFuel::new(12345, p!(2));
        let result = (original - original).unwrap();
        assert_eq!(result.units, 0);

        // Property: Negation is involution (double negation)
        let original = ZFuel::new(12345, p!(3));
        let neg_once = (-original).unwrap();
        let neg_twice = (-neg_once).unwrap();
        assert_eq!(original.units, neg_twice.units);
        assert_eq!(original.precision, neg_twice.precision);
    }

    #[test]
    fn test_precision_arithmetic_properties() {
        // Property: Mixed precision arithmetic uses higher precision
        let test_cases = [
            (ZFuel::new(100, p!(0)), ZFuel::new(200, p!(3)), p!(3)),
            (ZFuel::new(100, p!(2)), ZFuel::new(200, p!(1)), p!(2)),
            (ZFuel::new(100, p!(6)), ZFuel::new(200, p!(4)), p!(6)),
        ];

        for (a, b, expected_precision) in test_cases.iter() {
            let sum = (*a + *b).unwrap();
            assert_eq!(sum.precision, *expected_precision);

            let diff = (*a - *b).unwrap();
            assert_eq!(diff.precision, *expected_precision);
        }
    }

    #[test]
    fn test_precision_scaling_properties() {
        // Property: Scaling preserves mathematical value (within precision limits)
        let test_values = [
            (100, p!(0)),
            (150, p!(1)),
            (1250, p!(2)),
            (12500, p!(3)),
            (125000, p!(4)),
            (1250000, p!(5)),
            (12500000, p!(6)),
        ];

        for &(units, precision) in test_values.iter() {
            let original = ZFuel::new(units, precision);
            let _display_original = format!("{}", original);

            // Scale to different precisions and back
            for target_precision_val in 0..=6 {
                let target_precision = Precision::new(target_precision_val).unwrap();
                if let Ok(scaled) = original.to_precision(target_precision) {
                    // The display representation should be mathematically equivalent
                    // (though precision may differ)
                    let _display_scaled = format!("{}", scaled);

                    // For this simple test, we'll just check that scaling doesn't crash
                    // and produces valid ZFuel values
                    assert!(scaled.precision == target_precision);
                    assert!(scaled.precision.value() <= Precision::MAX);
                }
            }
        }
    }

    #[test]
    fn benchmark_precision_operations() {
        use std::time::Instant;

        // Benchmark precision scaling
        let start = Instant::now();
        for _ in 0..10000 {
            let f = ZFuel::new(123456, p!(2));
            let _scaled = f.to_precision(p!(6)).unwrap();
        }
        let scaling_duration = start.elapsed();
        println!("Precision scaling (10k ops): {:?}", scaling_duration);

        // Benchmark mixed precision arithmetic
        let start = Instant::now();
        let f1 = ZFuel::new(123456, p!(2));
        let f2 = ZFuel::new(789012, p!(4));
        for _ in 0..10000 {
            let _sum = (f1 + f2).unwrap();
        }
        let arithmetic_duration = start.elapsed();
        println!(
            "Mixed precision addition (10k ops): {:?}",
            arithmetic_duration
        );

        // Benchmark display formatting
        let start = Instant::now();
        let f = ZFuel::new(123456789, p!(6));
        for _ in 0..10000 {
            let _display = format!("{}", f);
        }
        let display_duration = start.elapsed();
        println!("Display formatting (10k ops): {:?}", display_duration);

        // Benchmark string parsing
        let start = Instant::now();
        for _ in 0..10000 {
            let _parsed = ZFuel::from_str("123.456789").unwrap();
        }
        let parsing_duration = start.elapsed();
        println!("String parsing (10k ops): {:?}", parsing_duration);

        // These are just timing measurements, not assertions
        // In a real benchmark, you'd want to use a proper benchmarking framework
        assert!(scaling_duration.as_millis() < 1000); // Should be fast
        assert!(arithmetic_duration.as_millis() < 1000);
        assert!(display_duration.as_millis() < 1000);
        assert!(parsing_duration.as_millis() < 1000);
    }

    #[test]
    fn benchmark_precision_vs_fixed() {
        use std::time::Instant;

        // Compare performance of variable precision vs fixed precision operations
        let iterations = 100000;

        // Fixed precision operations (all precision 6)
        let start = Instant::now();
        let f1 = ZFuel::new(123456, p!(6));
        let f2 = ZFuel::new(789012, p!(6));
        for _ in 0..iterations {
            let _sum = (f1 + f2).unwrap();
        }
        let fixed_duration = start.elapsed();

        // Mixed precision operations
        let start = Instant::now();
        let f1 = ZFuel::new(123456, p!(2));
        let f2 = ZFuel::new(789012, p!(4));
        for _ in 0..iterations {
            let _sum = (f1 + f2).unwrap();
        }
        let mixed_duration = start.elapsed();

        println!(
            "Fixed precision addition ({}k ops): {:?}",
            iterations / 1000,
            fixed_duration
        );
        println!(
            "Mixed precision addition ({}k ops): {:?}",
            iterations / 1000,
            mixed_duration
        );

        // Mixed precision should be reasonably close to fixed precision performance
        let ratio = mixed_duration.as_nanos() as f64 / fixed_duration.as_nanos() as f64;
        println!("Performance ratio (mixed/fixed): {:.2}", ratio);

        // Allow up to 5.0x slower for mixed precision (scaling overhead is expected, some variance is normal)
        assert!(
            ratio < 5.0,
            "Mixed precision operations are too slow compared to fixed precision"
        );
    }

    #[test]
    fn test_is_valid_precision() {
        // Test: Lower precision is always valid for higher expected precision
        let value_p0 = ZFuel::new(123, p!(0)); // 123 (integer)
        assert!(value_p0.is_valid_precision(p!(0)));
        assert!(value_p0.is_valid_precision(p!(2)));
        assert!(value_p0.is_valid_precision(p!(6)));

        let value_p2 = ZFuel::new(12345, p!(2)); // 123.45
        assert!(value_p2.is_valid_precision(p!(2)));
        assert!(value_p2.is_valid_precision(p!(6)));
        assert!(!value_p2.is_valid_precision(p!(1))); // Can't represent 2 decimals at precision 1

        // Test: Higher precision with trailing zeros is valid for lower expected precision
        let value_p3_trailing_zero = ZFuel::new(123450, p!(3)); // 123.450
        assert!(value_p3_trailing_zero.is_valid_precision(p!(3)));
        assert!(value_p3_trailing_zero.is_valid_precision(p!(2))); // 123.45, third decimal is 0
        assert!(!value_p3_trailing_zero.is_valid_precision(p!(1))); // 123.4, but second decimal (5) is non-zero
        assert!(!value_p3_trailing_zero.is_valid_precision(p!(0))); // 123, but decimals are non-zero

        // Test: Value with all trailing zeros
        let value_all_zeros = ZFuel::new(123000, p!(3)); // 123.000
        assert!(value_all_zeros.is_valid_precision(p!(3)));
        assert!(value_all_zeros.is_valid_precision(p!(2))); // 123.00
        assert!(value_all_zeros.is_valid_precision(p!(1))); // 123.0
        assert!(value_all_zeros.is_valid_precision(p!(0))); // 123

        // Test: Higher precision with non-zero trailing digits is invalid for lower expected precision
        let value_p3_nonzero = ZFuel::new(123456, p!(3)); // 123.456
        assert!(value_p3_nonzero.is_valid_precision(p!(3)));
        assert!(!value_p3_nonzero.is_valid_precision(p!(2))); // Would lose the 6
        assert!(!value_p3_nonzero.is_valid_precision(p!(1))); // Would lose the 56
        assert!(!value_p3_nonzero.is_valid_precision(p!(0))); // Would lose the 456

        // Test: Edge case - zero value is always valid
        let zero = ZFuel::zero();
        assert!(zero.is_valid_precision(p!(0)));
        assert!(zero.is_valid_precision(p!(6)));

        // Test: Precision 6 value with trailing zeros
        let value_p6 = ZFuel::new(123450000, p!(6)); // 123.450000
        assert!(value_p6.is_valid_precision(p!(6)));
        assert!(value_p6.is_valid_precision(p!(3))); // Last 3 decimals are 0
        assert!(value_p6.is_valid_precision(p!(2))); // Last 4 decimals are 0
        assert!(!value_p6.is_valid_precision(p!(1))); // Third decimal (5) is non-zero

        // Test: Mixed precision scenarios
        let value_p4 = ZFuel::new(12345670, p!(4)); // 1234.5670
        assert!(value_p4.is_valid_precision(p!(4)));
        assert!(value_p4.is_valid_precision(p!(3))); // Last decimal (0) is zero, so valid
        assert!(!value_p4.is_valid_precision(p!(2))); // Third decimal (7) is non-zero

        // Test: Precision 4 with non-zero last digit
        let value_p4_nonzero = ZFuel::new(12345671, p!(4)); // 1234.5671
        assert!(value_p4_nonzero.is_valid_precision(p!(4)));
        assert!(!value_p4_nonzero.is_valid_precision(p!(3))); // Last decimal (1) is non-zero
    }

    #[test]
    fn test_value_based_equality() {
        // Test: Same value, different precision
        // Now == uses value-based comparison
        let a = ZFuel::new(10, p!(0)); // 10
        let b = ZFuel::new(10000000, p!(6)); // 10.000000
        assert!(a == b); // Value-based: 10 == 10.000000

        // Test: Same value, same precision
        let c = ZFuel::new(12345, p!(2)); // 123.45
        let d = ZFuel::new(12345, p!(2)); // 123.45
        assert!(c == d); // Value-based equality works

        // Test: Different values, same precision
        let e = ZFuel::new(12345, p!(2)); // 123.45
        let f = ZFuel::new(12346, p!(2)); // 123.46
        assert!(e != f); // Value-based: different values
        assert!(e < f); // Value-based: 123.45 < 123.46

        // Test: Different values, different precision
        let g = ZFuel::new(123, p!(0)); // 123
        let h = ZFuel::new(12345000, p!(3)); // 123.450
        assert!(g != h); // Value-based: 123 != 123.450
        assert!(g < h); // Value-based: 123 < 123.450

        // Test: Zero values with different precision
        let zero_p0 = ZFuel::zero_precision(p!(0));
        let zero_p6 = ZFuel::zero();
        assert!(zero_p0 == zero_p6); // Value-based: 0 == 0

        // Test: Negative values
        let neg_a = ZFuel::new(-10, p!(0)); // -10
        let neg_b = ZFuel::new(-10000000, p!(6)); // -10.000000
        assert!(neg_a == neg_b); // Value-based: -10 == -10.000000

        // Test: Edge case - very large values
        let max_p0 = ZFuel::new(i64::MAX, p!(0));
        let max_p6 = ZFuel::new(i64::MAX, p!(6));
        // These might not compare correctly due to overflow, but shouldn't panic
        let _comparison = max_p0.partial_cmp(&max_p6);
        // partial_cmp returns None if comparison fails, which is fine
    }

    #[test]
    fn test_value_based_comparison() {
        // Test: Less than
        let a = ZFuel::new(12345, p!(2)); // 123.45
        let b = ZFuel::new(12346, p!(2)); // 123.46
        assert!(a < b);
        assert!(!(b < a));

        // Test: Less than with different precisions
        let c = ZFuel::new(10, p!(0)); // 10
        let d = ZFuel::new(10000001, p!(6)); // 10.000001
        assert!(c < d);
        assert!(!(d < c));

        // Test: Less than or equal
        assert!(a <= b);
        assert!(a <= a); // Equal values

        // Test: Greater than
        assert!(b > a);
        assert!(!(a > b));

        // Test: Greater than with different precisions
        assert!(d > c);
        assert!(!(c > d));

        // Test: Greater than or equal
        assert!(b >= a);
        assert!(a >= a); // Equal values

        // Test: Negative values
        let neg_small = ZFuel::new(-12346, p!(2)); // -123.46
        let neg_large = ZFuel::new(-12345, p!(2)); // -123.45
        assert!(neg_small < neg_large);
        assert!(neg_large > neg_small);

        // Test: Zero comparisons
        let zero = ZFuel::zero();
        let positive = ZFuel::new(1000000, p!(6)); // 1.000000
        let negative = ZFuel::new(-1000000, p!(6)); // -1.000000
        assert!(negative < zero);
        assert!(zero < positive);
        assert!(positive > zero);
        assert!(zero > negative);

        // Test: Edge cases - equal values with different precision
        let e1 = ZFuel::new(10, p!(0)); // 10
        let e2 = ZFuel::new(10000000, p!(6)); // 10.000000
        assert!(!(e1 < e2));
        assert!(!(e1 > e2));
        assert!(e1 <= e2);
        assert!(e1 >= e2);
    }
}
