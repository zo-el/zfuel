use crate::error::ZFuelError;
use std::ops::{Add, Div, Mul, Sub};
use std::{cmp, fmt};

#[derive(Debug, Clone, Copy)] // Copy req'd for binary op implementations
pub struct Fraction {
    pub numerator: i64,
    pub denominator: i64,
}

impl Fraction {
    /// Creates a new fraction with the given numerator and denominator
    pub fn new(numerator: i64, denominator: i64) -> Result<Self, ZFuelError> {
        if denominator == 0 {
            return Err(ZFuelError::Generic(
                "Tried to create a fraction with a denominator of 0!".to_string(),
            ));
        }
        if denominator < 0 {
            if numerator < -i64::MAX || denominator < -i64::MAX {
                return Err(ZFuelError::Generic(
                    "Tried to create a fraction with a numerator or denominator less than -i64::MAX!"
                        .to_string(),
                ));
            }
            let a = Self {
                numerator: -numerator,
                denominator: -denominator,
            };
            Ok(a)
        } else {
            Ok(Self {
                numerator,
                denominator,
            })
        }
    }

    /// Returns a new Fraction that is equal to this one, but simplified
    pub fn reduce(&self) -> Self {
        // Use `unsigned_abs()` so that numerator == i64::MIN (whose absolute value does not
        // fit in i64) does not panic. The GCD of any pair fits in i64 because it is bounded
        // by min(|numerator|, |denominator|), and denominator is normalized positive in `new`,
        // so the divisions below cannot overflow.
        let g = gcd_u64(self.numerator.unsigned_abs(), self.denominator.unsigned_abs()) as i64;
        if g == 0 {
            // Both operands were zero (only possible if denominator is zero, which `new` rejects);
            // defensively return self unchanged.
            return *self;
        }
        Self {
            numerator: self.numerator / g,
            denominator: self.denominator / g,
        }
    }

    /// Returns a decimal equivalent to this Fraction
    pub fn to_decimal(&self) -> f64 {
        self.numerator as f64 / self.denominator as f64
    }
}

impl fmt::Display for Fraction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let temp = self.reduce();
        if temp.denominator == 1 {
            write!(f, "{}", temp.numerator)
        } else {
            write!(f, "{}/{}", temp.numerator, temp.denominator)
        }
    }
}

impl cmp::PartialEq for Fraction {
    fn eq(&self, other: &Fraction) -> bool {
        let simp_self = self.reduce();
        let simp_other = other.reduce();
        simp_self.numerator == simp_other.numerator
            && simp_self.denominator == simp_other.denominator
    }
}

impl cmp::Eq for Fraction {}

impl cmp::PartialOrd for Fraction {
    fn partial_cmp(&self, other: &Fraction) -> Option<cmp::Ordering> {
        self.to_decimal().partial_cmp(&other.to_decimal())
    }
}

impl<'a> Add for &'a Fraction {
    type Output = Fraction;

    fn add(self, other: Self) -> Fraction {
        Fraction {
            numerator: (self.numerator * other.denominator + other.numerator * self.denominator),
            denominator: (self.denominator * other.denominator),
        }
    }
}

impl<'a> Sub for &'a Fraction {
    type Output = Fraction;

    fn sub(self, other: Self) -> Fraction {
        Fraction {
            numerator: (self.numerator * other.denominator - other.numerator * self.denominator),
            denominator: (self.denominator * other.denominator),
        }
    }
}

impl<'a> Mul for &'a Fraction {
    type Output = Fraction;

    fn mul(self, other: Self) -> Fraction {
        Fraction {
            numerator: (self.numerator * other.numerator),
            denominator: (self.denominator * other.denominator),
        }
    }
}

impl<'a> Div for &'a Fraction {
    type Output = Fraction;

    fn div(self, other: Self) -> Fraction {
        Fraction {
            numerator: (self.numerator * other.denominator),
            denominator: (self.denominator * other.numerator),
        }
    }
}

/// Iterative Euclidean GCD over u64. Used internally by `Fraction::reduce` so that operands
/// whose absolute value would overflow i64 (specifically `i64::MIN`) are handled correctly.
/// This routine has constant stack depth, so it is safe for any input.
pub(crate) fn gcd_u64(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

// Calculate the greatest common denominator for two numbers
pub fn gcd(a: i64, b: i64) -> i64 {
    // Terminal cases
    if a == b {
        return a;
    }
    if a == 0 {
        return b;
    }
    if b == 0 {
        return a;
    }

    let a_is_even = a % 2 == 0;
    let b_is_even = b % 2 == 0;

    match (a_is_even, b_is_even) {
        (true, true) => gcd(a / 2, b / 2) * 2,
        (true, false) => gcd(a / 2, b),
        (false, true) => gcd(a, b / 2),
        (false, false) => {
            if a > b {
                gcd((a - b) / 2, b)
            } else {
                gcd((b - a) / 2, a)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::ZFuelError;

    // ---- Fraction::new ----

    #[test]
    fn new_rejects_zero_denominator() {
        let err = Fraction::new(1, 0).unwrap_err();
        match err {
            ZFuelError::Generic(msg) => assert!(msg.contains("denominator of 0")),
            other => panic!("expected Generic error, got {:?}", other),
        }
    }

    #[test]
    fn new_normalizes_negative_denominator() {
        // Negative denominator is normalized: the sign moves to the numerator
        let f = Fraction::new(1, -2).unwrap();
        assert_eq!(f.numerator, -1);
        assert_eq!(f.denominator, 2);

        let f = Fraction::new(-3, -4).unwrap();
        assert_eq!(f.numerator, 3);
        assert_eq!(f.denominator, 4);
    }

    #[test]
    fn new_accepts_negative_numerator() {
        let f = Fraction::new(-5, 7).unwrap();
        assert_eq!(f.numerator, -5);
        assert_eq!(f.denominator, 7);
    }

    #[test]
    fn new_rejects_i64_min_with_negative_denominator() {
        // i64::MIN cannot be negated without overflow
        assert!(Fraction::new(i64::MIN, -1).is_err());
        assert!(Fraction::new(1, i64::MIN).is_err());
    }

    #[test]
    fn new_accepts_i64_max() {
        let f = Fraction::new(i64::MAX, i64::MAX).unwrap();
        assert_eq!(f.numerator, i64::MAX);
        assert_eq!(f.denominator, i64::MAX);
    }

    // ---- gcd ----

    #[test]
    fn gcd_basic_cases() {
        assert_eq!(gcd(0, 5), 5);
        assert_eq!(gcd(5, 0), 5);
        assert_eq!(gcd(7, 7), 7);
        assert_eq!(gcd(12, 18), 6);
        assert_eq!(gcd(18, 12), 6);
        assert_eq!(gcd(1, 1), 1);
        // Co-prime pairs
        assert_eq!(gcd(7, 13), 1);
        assert_eq!(gcd(11, 17), 1);
    }

    #[test]
    fn gcd_powers_of_two() {
        assert_eq!(gcd(8, 16), 8);
        assert_eq!(gcd(1024, 4096), 1024);
        assert_eq!(gcd(1 << 30, 1 << 20), 1 << 20);
    }

    #[test]
    fn gcd_property_divides_both() {
        // For a representative grid of positive inputs, gcd must divide both operands
        for a in 1..20i64 {
            for b in 1..20i64 {
                let g = gcd(a, b);
                assert!(g > 0, "gcd({},{}) returned non-positive {}", a, b, g);
                assert_eq!(a % g, 0, "gcd({},{})={} does not divide {}", a, b, g, a);
                assert_eq!(b % g, 0, "gcd({},{})={} does not divide {}", a, b, g, b);
            }
        }
    }

    #[test]
    fn gcd_handles_large_inputs_without_stack_overflow() {
        // Sanity check: ensure recursion depth stays reasonable for large inputs.
        // The binary GCD algorithm halves on even inputs and subtracts on odd pairs.
        let _ = gcd(i64::MAX, 1);
        let _ = gcd(i64::MAX, i64::MAX - 1);
        let _ = gcd(1 << 60, (1 << 60) + 1);
    }

    // ---- reduce ----

    #[test]
    fn reduce_simplifies_to_lowest_terms() {
        let f = Fraction::new(4, 8).unwrap().reduce();
        assert_eq!((f.numerator, f.denominator), (1, 2));

        let f = Fraction::new(15, 25).unwrap().reduce();
        assert_eq!((f.numerator, f.denominator), (3, 5));

        let f = Fraction::new(100, 75).unwrap().reduce();
        assert_eq!((f.numerator, f.denominator), (4, 3));
    }

    #[test]
    fn reduce_preserves_negative_sign() {
        let f = Fraction::new(-4, 8).unwrap().reduce();
        assert_eq!((f.numerator, f.denominator), (-1, 2));

        let f = Fraction::new(4, -8).unwrap().reduce();
        // new() normalizes -> (-4, 8)
        assert_eq!((f.numerator, f.denominator), (-1, 2));
    }

    #[test]
    fn reduce_zero_numerator_yields_zero_over_one() {
        let f = Fraction::new(0, 7).unwrap().reduce();
        // gcd(0,7) == 7, so 0/7 -> 0/1
        assert_eq!((f.numerator, f.denominator), (0, 1));
    }

    #[test]
    fn reduce_already_reduced_is_idempotent() {
        let f = Fraction::new(3, 5).unwrap();
        let r1 = f.reduce();
        let r2 = r1.reduce();
        assert_eq!((r1.numerator, r1.denominator), (r2.numerator, r2.denominator));
    }

    #[test]
    fn reduce_handles_i64_min_numerator() {
        // Regression: the old `self.numerator.abs()` panicked when numerator == i64::MIN.
        // After construction, reduce() must not panic for any valid Fraction.
        let f = Fraction::new(i64::MIN, 1).unwrap();
        let r = f.reduce();
        assert_eq!(r.numerator, i64::MIN);
        assert_eq!(r.denominator, 1);

        let f = Fraction::new(i64::MIN, 2).unwrap();
        let r = f.reduce();
        assert_eq!(r.numerator, i64::MIN / 2);
        assert_eq!(r.denominator, 1);

        let f = Fraction::new(i64::MIN, i64::MAX).unwrap();
        let _ = f.reduce(); // must not panic
    }

    // ---- to_decimal ----

    #[test]
    fn to_decimal_basic() {
        assert_eq!(Fraction::new(1, 2).unwrap().to_decimal(), 0.5);
        assert_eq!(Fraction::new(3, 4).unwrap().to_decimal(), 0.75);
        assert_eq!(Fraction::new(-1, 2).unwrap().to_decimal(), -0.5);
    }

    #[test]
    fn to_decimal_irrational_approximation() {
        let third = Fraction::new(1, 3).unwrap().to_decimal();
        assert!((third - 0.333_333_333_333_333).abs() < 1e-12);
    }

    // ---- Display ----

    #[test]
    fn display_whole_numbers_omit_denominator() {
        let f = Fraction::new(7, 1).unwrap();
        assert_eq!(format!("{}", f), "7");
        let f = Fraction::new(10, 5).unwrap();
        assert_eq!(format!("{}", f), "2");
    }

    #[test]
    fn display_fractional_shows_reduced_form() {
        let f = Fraction::new(2, 4).unwrap();
        assert_eq!(format!("{}", f), "1/2");
        let f = Fraction::new(35, 1000).unwrap();
        assert_eq!(format!("{}", f), "7/200");
    }

    #[test]
    fn display_negative_fractions() {
        let f = Fraction::new(-3, 4).unwrap();
        assert_eq!(format!("{}", f), "-3/4");
        let f = Fraction::new(3, -4).unwrap();
        assert_eq!(format!("{}", f), "-3/4");
    }

    // ---- Comparison ----

    #[test]
    fn ordering_test() {
        let a = Fraction::new(1, 2).unwrap();
        let b = Fraction::new(3, 4).unwrap();
        let c = Fraction::new(4, 3).unwrap();
        let d = Fraction::new(-1, 2).unwrap();
        assert!(a < b);
        assert!(a <= b);
        assert!(c > b);
        assert!(c >= a);
        assert!(d < a);
    }

    #[test]
    fn equality_test() {
        let a = Fraction::new(1, 2).unwrap();
        let b = Fraction::new(2, 4).unwrap();
        let c = Fraction::new(5, 5).unwrap();
        assert!(a == b);
        assert!(a != c);
    }

    #[test]
    fn equality_is_value_based_across_reduction() {
        // Fractions with the same value but different (numerator, denominator) should be equal
        let a = Fraction::new(7, 200).unwrap();
        let b = Fraction::new(35, 1000).unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn equality_handles_negative_normalization() {
        // (-1)/2 and 1/(-2) should both normalize to -1/2
        let a = Fraction::new(-1, 2).unwrap();
        let b = Fraction::new(1, -2).unwrap();
        assert_eq!(a, b);
    }

    // ---- Arithmetic ----

    #[test]
    fn arithmetic_test() {
        let a = Fraction::new(1, 2).unwrap();
        let b = Fraction::new(3, 4).unwrap();
        assert!(&a + &a == Fraction::new(1, 1).unwrap());
        assert!(&a - &a == Fraction::new(0, 5).unwrap());
        assert!(&a * &b == Fraction::new(3, 8).unwrap());
        assert!(&a / &b == Fraction::new(4, 6).unwrap());
    }

    #[test]
    fn arithmetic_distributes_over_zero_numerator() {
        // 0/x + n/d == n/d (after reduction)
        let zero = Fraction::new(0, 1).unwrap();
        let n = Fraction::new(3, 7).unwrap();
        assert_eq!(&zero + &n, n);
    }

    #[test]
    fn fraction_arithmetic_operators_have_no_overflow_protection() {
        // Documented limitation: &Fraction +/-/*/÷ &Fraction performs raw i64 math.
        // For production use with adversarial inputs, callers should pre-reduce or use ZFuel * Fraction
        // (which IS overflow-checked). This test pins current behavior with safe inputs.
        let a = Fraction::new(i64::MAX / 4, 2).unwrap();
        let b = Fraction::new(1, 2).unwrap();
        let product = &a * &b;
        // (MAX/4) * 1 / (2 * 2) is representable without overflow
        assert_eq!(product.numerator, i64::MAX / 4);
        assert_eq!(product.denominator, 4);
    }
}
