use std::ops::{Add, Div, Mul, Sub};
use std::{cmp, fmt};

use crate::error::ZFuelError;

#[derive(Debug, Clone, Copy)] // Copy req'd for binary op implementations
pub struct Fraction {
    pub numerator: i128,
    pub denominator: i128,
}

impl Fraction {
    /// Creates a new fraction with the given numerator and denominator
    /// Panics if given a denominator of 0
    pub fn new(numerator: i128, denominator: i128) -> Result<Self, ZFuelError> {
        if denominator == 0 {
            return Err(ZFuelError::Generic(
                "Tried to create a fraction with a denominator of 0!".to_string(),
            ));
        }
        if denominator < 0 {
            if numerator < -i128::MAX || denominator < -i128::MAX {
                return Err(ZFuelError::Generic(
                    "Tried to create a fraction with a numerator or denominator less than -i128::MAX!"
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
        // Use absolute value because negatives
        let gcd = gcd(self.numerator.abs(), self.denominator.abs());
        Self {
            numerator: (self.numerator / gcd),
            denominator: (self.denominator / gcd),
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

// Calculate the greatest common denominator for two numbers
pub fn gcd(a: i128, b: i128) -> i128 {
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
fn arithmetic_test() {
    let a = Fraction::new(1, 2).unwrap();
    let b = Fraction::new(3, 4).unwrap();
    assert!(&a + &a == Fraction::new(1, 1).unwrap());
    assert!(&a - &a == Fraction::new(0, 5).unwrap());
    assert!(&a * &b == Fraction::new(3, 8).unwrap());
    assert!(&a / &b == Fraction::new(4, 6).unwrap());
}
