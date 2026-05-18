//! The Fuel Fuel type and math functions, and JSON serialization support.  Supports Fraction
//! type for computing fractional Fuel amounts using rational numbers; useful for expressing
//! "percentages" of Fuel amounts without losing (too much) precision, while retaining the
//! ability to compute Fuel transaction fees on the largest possible transaction amounts.
//!
//! # Value-space invariant
//!
//! A `ZFuel` represents a value in the fixed range `±MAXVALUE / 10^6 ≈ ±9.223 trillion`,
//! regardless of the chosen representation precision. `precision` selects how that value is
//! displayed (0–6 decimal digits) — it does **not** widen the value space.
//!
//! Concretely, [`ZFuel::new`] rejects any `units` whose absolute value exceeds the cap below:
//!
//! | precision | max units                    | what one unit represents |
//! |-----------|------------------------------|--------------------------|
//! | 0         | 9_223_372_036_854            | 1 ZFuel                  |
//! | 1         | 92_233_720_368_547           | 0.1 ZFuel                |
//! | 2         | 922_337_203_685_477          | 0.01 ZFuel               |
//! | 3         | 9_223_372_036_854_775        | 0.001 ZFuel              |
//! | 4         | 92_233_720_368_547_758       | 0.0001 ZFuel             |
//! | 5         | 922_337_203_685_477_580      | 0.00001 ZFuel            |
//! | 6         | 9_223_372_036_854_775_807    | 0.000001 ZFuel           |
//!
//! Because every legal `ZFuel` can be scaled to `Precision::DEFAULT` (6) without overflow,
//! cross-precision arithmetic and comparison are total against panics for any pair of
//! constructible values.

use crate::error::ZFuelError;
use crate::fraction::Fraction;
pub use crate::precision::Precision;
use regex::Regex;
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use std::{
    fmt,
    ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Sub, SubAssign},
    result,
    str::FromStr,
};
///
/// Fuel -- Account for z Fuel, in fractions of 1/10^6 ( 1/1,000,000th of a unit)
///
/// Ensures that the integer amount never leaves Rust / Web Assembly.  For example, if the i64 value
/// was processed in Javascript, it must not exceed a +/- value that would fit into an IEEE 754
/// double-precision floating point value without loss of precision.  Thus, the no value exceeding
/// +/- 2^53-1 fractional units of z Fuel should be converted into an f64.
///
/// This Fuel struct is what ensures that we do not pass numeric z Fuel amounts through the WASM
/// boundary.  All precise z Fuel values, such as 2,882,343,476 x 1/1e6 units of z Fuel are
/// represented as Display 'fmt()' values (eg. "2882.343467" z Fuel).  The Display value is precisely
/// convertible back and forth into the internal integer representation without loss of precision,
/// and is also a human-readable fractional amount of z Fuel, it is also the preferred external
/// representation.
///
/// Javascript (and other languages that use IEEE 754 floats to represent integer values) cannot be
/// allowed to compute numeric values that will exceed 2^53-1 (9.0072e15); the capacity of IEEE 754
/// mantissa w/o loss of numerical accuracy, for those platforms that emulate i64 using IEEE 754
/// double-precision floating point.  Allowing 15 total decimal digits in 7 integer and 8 fractional
/// digits (+/-1e15), and 13 hex digits (+/-4.5e15) is safely within this range.  However, we would
/// give up some possibly useful capacity.
///
/// The available range in [0,2^53), with 8 decimal digits after the decimal point, is about 7.95
/// digits: log( 2**53 / 10 ** 8, 10 ) == 7.9545.  So, we would allow up to 8 integer digits, and
/// manually check for precision overflow by comparing against 2**53, and rejecting any value that
/// exceeds the maximum 9.0071e15).  Likewise, we accept 14 hex digits, and check the full precision
/// limits manually.  This would allow only z Fuel account and transaction values up to about
/// 90,071,992 z Fuel; insufficient (there are 177B HOT issued already, so the Holo
/// infrastructure account will be in a debit condition beyond this value).
///
/// With 6 decimal digits of fractional precision (a minimum transaction of 1/1,000,000 of a
/// Fuel), the range is log( 2**53 / 10 ** 6, 10 ) == 9.9545 digits of z Fuel; almost 10
/// digits of precision, with a max capacity of about 9,007,199,254 Fuel; still insufficient to
/// represent the debit balance of the Holo organization which issued the HOT.
///
/// Therefore, we allow the full range of i64 values for Fuel.units -- and disallow/discourage
/// calculation on Fuel values in Javascript code; unless you use Big values, you *will* (very, very
/// probably) do it wrong, and lose precision with large Fuel values.
///
/// By allowing the full i64 range for Fuel units (1/10^6 of a Fuel), we achieve a maximum
/// range of +/- of log( 2**63 / 10 ** 6 ) == 12.96 digits of Fuel capacity; about
/// 9,223,372,036,854 (9.223 Trillion) Fuel account and transaction value capacity; adequate for
/// any single Fuel account value or Transaction amount.  Any transaction the exceeds these
/// values will fail to complete (as all calculations are strictly bounds-checked).
///
/// The minimum fractional minimum amount of 1/10^6 Fuel allows for micro-transactions down to
/// 1/1,000,000th (1 millionth) of a Fuel.  Fee payments lose precision below value of
/// 1/10,000th of a Fuel; for example, if a micro-transaction of 0.000123 Fuel is spent, the
/// 1% fee that will be computed and charged could be 0.000001 Fuel if rounded down, or 0.000002
/// if rounded up.
///
/// Since the system "cost" of extremely tiny transactions is not free, fees on the portion of
/// transactions below the minimum threshold are always rounded up (away from 0).  This doesn't
/// affect the fee calculation of fees on transactions of precision 0.0001 or above (ie. the fee for
/// spending .0021 Fuel is exactly 0.000021).  However, the fee for spending 0.00213 is computed
/// as 0.000022 (is round up), instead of 0.000021 (normal rounding).  Perhaps surprisingly, the fee
/// to spend 0.000001 Fuel is 0.000001.  In effect, the fees on extremely tiny transactions
/// increase from 1%, up to 100% fees on the tiniest possible transaction.  This better reflects the
/// actual costs of running the Holo system, and is not an egregious cost; 1,000 such transactions
/// would cost an additional 0.001 Fuel in fees (vs. fees calculated with infinite precision).
///

// FRACTION -- units of z Fuel are stored to this fixed-point precision.  These must
// be consistent with eachother.  Values after the decimal point are truncated to the
// EXPONENT number of significant decimal places; the remainder are ignored.
pub const EXPONENT: usize = 6; // Up to 6 digits after decimal (>6 truncated)
pub const DENOMINATOR: usize = 1_000_000; // eg. 10 ^ EXPONENT

// At any precision, the maximum representable ZFuel value is bounded at ±MAXVALUE/10^6 ≈
// ±9.223 trillion (≈12.96 digits). The integer part of any valid decimal input therefore
// fits in at most 13 digits. Inputs with more integer digits are always invalid, regardless
// of precision; `ZFuel::new` enforces the corresponding per-precision unit cap.
pub const INTLIMIT: usize = 13; // Up to 13 digits before decimal (~12.96 accepted)
pub const HEXLIMIT: usize = 16; // Up to 16 hex digits (full 64-bit signed twos-complement integer)

// These {MIN,MAX}{VALUE,RANGE} values are *carefully* chosen to avoid the possibility of
// over/underflow at the limits of u64/i64 interactions in Fuel calculations.  Do not consider
// changing without carefully considering/testing the effects at the limits of possible value.
pub const MAXVALUE: i64 = i64::max_value(); // 0x7fff_ffff_ffff_ffff;
pub const MAXRANGE: u64 = MAXVALUE as u64;

pub const MINVALUE: i64 = -MAXVALUE - 1; // == i64::min_value();
pub const MINRANGE: u64 = MAXRANGE + 1;

// DECSHOWN -- default number of decimal places desired after '.' in Display values
pub const DECSHOWN: usize = 1; // could be 1-EXPONENT

#[derive(Clone, Copy)] // Copy req'd for binary op implementations
/// z Fuel, with variable decimal precision (0-6 places)
pub struct ZFuel {
    pub units: i64,
    pub precision: Precision,
}

/// fuel::FuelResult -- a fully defined custom Result type for z Fuel operations
pub type FuelResult = result::Result<ZFuel, ZFuelError>;

/// Serialize as human-readable string, eg. "1.02" instead of { units: 102000000 }
///
/// This format is unambiguous and retains all precision of the raw units value, and is
/// automatically serialized to/from a JSON string type.
impl Serialize for ZFuel {
    fn serialize<S>(&self, serializer: S) -> result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(self.to_string().as_ref())
    }
}

impl<'d> Deserialize<'d> for ZFuel {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'d>,
    {
        let s = String::deserialize(deserializer)?;
        ZFuel::from_str(&s).map_err(|e| de::Error::custom(e.to_string()))
    }
}

impl ZFuel {
    /// Compute the maximum positive `units` value legal at a given precision.
    ///
    /// The value space of a `ZFuel` is bounded at `±MAXVALUE / 10^6 ≈ ±9.223 trillion`
    /// regardless of the chosen representation precision. At precision `p`, one unit
    /// represents `10^-p` ZFuel, so the maximum legal `units` is `MAXVALUE / 10^(6-p)`.
    ///
    /// | precision | max units                    |
    /// |-----------|------------------------------|
    /// | 0         | 9_223_372_036_854            |
    /// | 1         | 92_233_720_368_547           |
    /// | 2         | 922_337_203_685_477          |
    /// | 3         | 9_223_372_036_854_775        |
    /// | 4         | 92_233_720_368_547_758       |
    /// | 5         | 922_337_203_685_477_580      |
    /// | 6         | 9_223_372_036_854_775_807    |
    #[inline]
    pub fn max_units_at(precision: Precision) -> u64 {
        // `Precision::MAX - precision.value()` is the number of decimal places we'd have to scale
        // up to reach precision 6. Dividing MAXRANGE by that scale gives the cap.
        let headroom = (Precision::MAX - precision.value()) as u32;
        MAXRANGE / 10u64.pow(headroom)
    }

    /// Compute the maximum absolute `units` value legal for a negative `ZFuel` at a given
    /// precision. This is one larger than `max_units_at` exactly at `Precision::DEFAULT` to
    /// accommodate `MINVALUE`'s asymmetry in the i64 representation.
    #[inline]
    pub fn min_units_abs_at(precision: Precision) -> u64 {
        let headroom = (Precision::MAX - precision.value()) as u32;
        MINRANGE / 10u64.pow(headroom)
    }

    /// Construct a `ZFuel` from a raw `units` value at the given `precision`.
    ///
    /// Rejects values that fall outside the precision's legal range so every successfully
    /// constructed `ZFuel` can participate in cross-precision arithmetic without overflow.
    ///
    /// # Examples
    /// ```
    /// use zfuel::fuel::{ZFuel, Precision};
    /// // Within range at precision 0 (max ~9.22 trillion):
    /// assert!(ZFuel::new(9_223_372_036_854, Precision::new(0).unwrap()).is_ok());
    /// // Out of range at precision 0 (cannot scale up to precision 6 without overflow):
    /// assert!(ZFuel::new(i64::MAX, Precision::new(0).unwrap()).is_err());
    /// // Always valid at default precision (units are 1/10^6 of a ZFuel):
    /// assert!(ZFuel::new(i64::MAX, Precision::DEFAULT).is_ok());
    /// assert!(ZFuel::new(i64::MIN, Precision::DEFAULT).is_ok());
    /// ```
    pub fn new(units: i64, precision: Precision) -> Result<Self, ZFuelError> {
        let abs = units.unsigned_abs();
        let cap = if units < 0 {
            Self::min_units_abs_at(precision)
        } else {
            Self::max_units_at(precision)
        };
        if abs > cap {
            return Err(ZFuelError::Range(format!(
                "ZFuel units {} exceeds the legal range for precision {} (cap |units| = {})",
                units,
                precision.value(),
                cap
            )));
        }
        Ok(ZFuel { units, precision })
    }

    /// Construct a `ZFuel` at the default precision (6). Always succeeds, because
    /// every `i64` value is in range at `Precision::DEFAULT`.
    pub fn new_with_default_precision(units: i64) -> Self {
        ZFuel {
            units,
            precision: Precision::DEFAULT,
        }
    }

    pub fn zero() -> Self {
        ZFuel {
            units: 0,
            precision: Precision::DEFAULT,
        }
    }

    pub fn zero_precision(precision: Precision) -> Self {
        ZFuel {
            units: 0,
            precision,
        }
    }
    /// Validate that a string is a parseable, non-negative ZFuel amount.
    ///
    /// Returns `Ok(true)` if the input parses as a valid ZFuel value with a non-negative
    /// numeric value, otherwise returns a `ZFuelError::Range` describing why it was rejected.
    /// Accepts the same syntax as [`ZFuel::from_str`] (decimal, hex with `0x`, `H` / `♓`
    /// prefix, optional `+` sign, surrounding whitespace, and `_` digit separators).
    pub fn check(amount: &str) -> Result<bool, ZFuelError> {
        // Delegate to the canonical parser so `check` and `from_str` always agree on
        // what constitutes a valid amount. This guarantees no caller is surprised by a
        // string that passes `check` but later fails `from_str` (or vice versa).
        match ZFuel::from_str(amount) {
            Ok(z) if z.units >= 0 => Ok(true),
            Ok(_) => Err(ZFuelError::Range(format!(
                "Invalid negative amount {}",
                amount
            ))),
            Err(_) => Err(ZFuelError::Range(format!(
                "Invalid ZFuel amount {}",
                amount
            ))),
        }
    }
}

/// u64_to_i64 -- range-checked, optionally negating mantissa + fraction for Fuel.units.  Ensures
/// that supplied range (and fuel MIN/MAXVALUEs are not exceeded).  This is a subtle operation,
/// which requires us to pre-validate absolute (unsigned) mantissa and fractional fuel unit values
/// before any negative sign is applied.
pub fn u64_to_i64(
    negative: bool,
    mantissa: u64,
    fraction: u64,
    range: u64,
) -> Result<i64, ZFuelError> {
    match mantissa.checked_add(fraction) {
        Some(u_units) => {
            if u_units > range {
                Err(ZFuelError::Range(format!(
                    "Exceeded range for z Fuel mantissa {}, fraction {}",
                    mantissa, fraction
                )))
            } else if negative {
                if u_units > MINRANGE {
                    Err(ZFuelError::Range(format!(
                        "Underflow for z Fuel negative mantissa {}, fraction {}",
                        mantissa, fraction
                    )))
                } else if u_units == MINRANGE {
                    Ok(MINVALUE)
                } else {
                    Ok(-(u_units as i64))
                }
            } else {
                Ok(u_units as i64)
            }
        }
        None => Err(ZFuelError::Range(format!(
            "Overflow for z Fuel mantissa {}, fraction {}",
            mantissa, fraction
        ))),
    }
}

/// Precision scaling utilities for converting between precision levels
impl ZFuel {
    /// Scale units from one precision to another
    pub fn scale_units(
        units: i64,
        from_precision: Precision,
        to_precision: Precision,
    ) -> Result<i64, ZFuelError> {
        if from_precision == to_precision {
            return Ok(units);
        }

        let from_denom = from_precision.denominator();
        let to_denom = to_precision.denominator();

        if from_denom > to_denom {
            // Scaling down - divide by the difference in denominators
            let scale_factor = from_denom / to_denom;
            Ok(units / scale_factor as i64)
        } else {
            // Scaling up - multiply by the difference in denominators
            let scale_factor = to_denom / from_denom;
            units.checked_mul(scale_factor as i64).ok_or_else(|| {
                ZFuelError::Range(format!(
                    "Overflow when scaling units {} from precision {} to precision {}",
                    units,
                    from_precision.value(),
                    to_precision.value()
                ))
            })
        }
    }

    /// Convert this ZFuel to a different precision
    pub fn to_precision(&self, target_precision: Precision) -> Result<ZFuel, ZFuelError> {
        let scaled_units = Self::scale_units(self.units, self.precision, target_precision)?;
        Ok(ZFuel {
            units: scaled_units,
            precision: target_precision,
        })
    }

    /// Check if this ZFuel value is valid for the expected precision
    ///
    /// Returns `true` if the value can be represented at the expected precision without losing information.
    ///
    /// # Rules:
    /// - If actual precision <= expected precision: always valid (can represent lower precision at higher precision)
    /// - If actual precision > expected precision: valid only if the extra decimal places are all zeros
    ///
    /// # Examples:
    /// ```
    /// use zfuel::fuel::{ZFuel, Precision};
    ///
    /// // Precision 0 (integer) is valid for precision 6
    /// let value = ZFuel::new(123, Precision::new(0).unwrap()).unwrap();
    /// assert!(value.is_valid_precision(Precision::new(6).unwrap()));
    ///
    /// // Precision 2 is valid for precision 6
    /// let value = ZFuel::new(12345, Precision::new(2).unwrap()).unwrap(); // 123.45
    /// assert!(value.is_valid_precision(Precision::new(6).unwrap()));
    ///
    /// // Precision 3 with trailing zero is valid for precision 2
    /// let value = ZFuel::new(123450, Precision::new(3).unwrap()).unwrap(); // 123.450
    /// assert!(value.is_valid_precision(Precision::new(2).unwrap()));
    ///
    /// // Precision 3 with non-zero third decimal is invalid for precision 2
    /// let value = ZFuel::new(123456, Precision::new(3).unwrap()).unwrap(); // 123.456
    /// assert!(!value.is_valid_precision(Precision::new(2).unwrap()));
    /// ```
    pub fn is_valid_precision(&self, expected_precision: Precision) -> bool {
        let actual_precision = self.precision.value();
        let expected = expected_precision.value();

        // If actual precision is less than or equal to expected, always valid
        if actual_precision <= expected {
            return true;
        }

        // Actual precision is greater than expected - check if extra digits are zeros
        // We need to check if the last (actual_precision - expected) decimal places are all zeros
        let extra_digits = actual_precision - expected;
        let divisor = 10_u64.pow(extra_digits as u32) as i64;

        // Check if units are divisible by 10^(extra_digits)
        // This means the last 'extra_digits' decimal places are all zeros
        self.units % divisor == 0
    }

    /// Detect precision from a decimal string (count digits after decimal point)
    /// Trailing zeros are significant, so "123.450" has precision 3, not 2
    /// Integers (no decimal point) have precision 0
    /// Hex values (0x...) use default precision 6 since they represent raw units
    pub fn detect_precision_from_string(s: &str) -> Precision {
        // Hex values represent raw units in precision 6 format
        // Check for hex after trimming whitespace and sign
        let trimmed = s
            .trim_start()
            .trim_start_matches('-')
            .trim_start_matches('+');
        if trimmed.starts_with("0x") || s.contains('H') || s.contains('♓') {
            return Precision::DEFAULT;
        }

        if let Some(decimal_pos) = s.find('.') {
            let after_decimal = &s[decimal_pos + 1..];
            // Clamp in usize space before narrowing to u8 to avoid `as u8` wrap-around
            // on adversarially long fractional strings (>= 256 chars).
            let detected = std::cmp::min(after_decimal.len(), Precision::MAX as usize) as u8;
            // If no digits after decimal, default to 0 precision
            if detected == 0 {
                Precision::new(0).unwrap_or(Precision::DEFAULT)
            } else {
                Precision::new(detected).unwrap_or(Precision::DEFAULT)
            }
        } else {
            // No decimal point means precision 0 (integer)
            Precision::new(0).unwrap_or(Precision::DEFAULT)
        }
    }
}

/// Fuel::from_str -- Covert from &str; Result may yield Err if parsing fails
///
/// Handles hexadecimal and normal whole or fractional amounts of z Fuel, discarding any
/// precision beyond the 8th (EXPONENT) decimal place of fractional precision.  Returns ZFuelError
/// on any parsing or result value max range errors.
///
impl FromStr for ZFuel {
    type Err = ZFuelError;

    fn from_str(amount: &str) -> result::Result<Self, Self::Err> {
        // Accept underscores as digit separators (e.g. "1_000_000"). We strip them up front
        // so the canonical regex below stays simple and so `check` and `from_str` agree.
        let amount_clean: String;
        let amount_ref: &str = if amount.contains('_') {
            amount_clean = amount.replace('_', "");
            &amount_clean
        } else {
            amount
        };
        let amount = amount_ref;
        lazy_static! {
            // Either 'hex', or 'int' and optionally 'fra' will be set if RE matches.
            // Failure to construct this regex is a terminal failure; .unwrap() and
            // panic! is appropriate.
            static ref FUEL_RE: Regex = Regex::new( &format!( r"(?x)
                ^\s*
                (?P<sig>[-+]?)
                \s*
                (?:
                  (?:0x(?P<hex>[a-fA-F0-9]{{1,{hexlimit}}}))
                 |(?:[H♓]?\s*
                    (?:
                      (?P<int>\d{{1,{intlimit}}})\.?
                     |(?P<mnt>\d{{0,{intlimit}}})\.(?P<frc>\d+)
                    )
                  )
                )
                \s*$", hexlimit = HEXLIMIT, intlimit = INTLIMIT )).unwrap();
        }

        let caps = FUEL_RE
            .captures(amount)
            .ok_or_else(|| ZFuelError::Range(format!("Invalid z Fuel amount {}", amount)))?;

        // The regex matched. Either a hex, an int, or a (possibly-empty) mnt + frc pair is
        // present. We parse the integer part as a u64 scaled to Precision::DEFAULT (multiplied
        // by `DENOMINATOR`), then add the fractional part. Working at Precision::DEFAULT lets
        // the existing `u64_to_i64` range check enforce the absolute ZFuel value cap; we scale
        // down to the detected precision afterward.
        let mantissa: u64 = match caps.name("hex") {
            None => match caps.name("int") {
                None => match caps.name("mnt") {
                    None => {
                        return Err(ZFuelError::Range(format!(
                            "Invalid z Fuel amount {}",
                            amount
                        )));
                    }
                    Some(mnt) => match mnt.as_str() {
                        "" => 0_u64,
                        mnt_str => {
                            DENOMINATOR as u64
                                * mnt_str.parse::<u64>().map_err(|_| {
                                    ZFuelError::Range(format!(
                                        "Invalid z Fuel amount {}; bad mantissa {}",
                                        amount, mnt_str
                                    ))
                                })?
                        }
                    },
                },
                Some(int) => {
                    DENOMINATOR as u64
                        * int.as_str().parse::<u64>().map_err(|_| {
                            ZFuelError::Range(format!(
                                "Invalid z Fuel amount {}; bad int {}",
                                amount,
                                int.as_str()
                            ))
                        })?
                }
            },
            Some(hex) => u64::from_str_radix(hex.as_str(), 16).map_err(|_| {
                ZFuelError::Range(format!(
                    "Invalid z Fuel amount {}; bad hex {}",
                    amount,
                    hex.as_str()
                ))
            })?,
        };

        // Truncate/zero-pad the fractional digits to exactly EXPONENT width so the resulting
        // u64 lines up with Precision::DEFAULT units.
        let fraction: u64 = match caps.name("frc") {
            None => 0,
            Some(fra) => u64::from_str_radix(
                &format!(
                    "{:0<exponent$.exponent$}",
                    fra.as_str(),
                    exponent = EXPONENT
                ),
                10,
            )
            .map_err(|_| {
                ZFuelError::Range(format!(
                    "Invalid z Fuel amount {}; bad fraction {}",
                    amount,
                    fra.as_str()
                ))
            })?,
        };

        let sign = match caps.name("sig") {
            Some(cap) => cap.as_str(),
            None => "",
        };

        let units_default = match sign {
            "-" => u64_to_i64(true, mantissa, fraction, MINRANGE)?,
            _ => u64_to_i64(false, mantissa, fraction, MAXRANGE)?,
        };

        // Detect precision from the input string and scale the precision-6 units down to it.
        // Scaling down (DEFAULT -> p <= DEFAULT) is total integer division — never overflows.
        let detected_precision = Self::detect_precision_from_string(amount);
        let scaled_units = if detected_precision == Precision::DEFAULT {
            units_default
        } else {
            Self::scale_units(units_default, Precision::DEFAULT, detected_precision)?
        };

        // Go through the validating constructor so every parsed value satisfies the
        // per-precision range invariant. (Scaling-down preserves range, so this is
        // expected to always succeed; the check is defense-in-depth.)
        ZFuel::new(scaled_units, detected_precision)
    }
}

/// i64 -> Fuel for all integer types (uses default precision of 6)
impl From<i64> for ZFuel {
    fn from(units: i64) -> ZFuel {
        ZFuel {
            units,
            precision: Precision::DEFAULT,
        }
    }
}

/// & mut Fuel -> Fuel required for in-place operators
impl From<&mut ZFuel> for ZFuel {
    fn from(other: &mut ZFuel) -> ZFuel {
        ZFuel {
            units: other.units,
            precision: other.precision,
        }
    }
}

///
/// z Fuel amounts in human-readable Display representation
///
/// All integer numeric forms of z Fuel are deemed to be terms if 1/DENOMINATOR units.  Floating
/// point amounts are not acceptable, due to loss of precision.
///
/// All String/&str forms are deemed to be in "whole.fractional" amounts, and are converted to
/// internal 1/DENOMINATOR units.
///
/// If no fractional units are used, then the Fuel amount is represented as a whole-numbered value;
/// at least 1 fractional digit of precision is displayed (more, if required to represent the value
/// without loss of precision.).
///
/// # Examples
/// ```
/// use zfuel::fuel::ZFuel;
/// let f1 = ZFuel::from( 1234567890 );
/// let d1 = format!( "{}", f1 );
/// ```
///
impl fmt::Display for ZFuel {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let sign = if self.units < 0 { "-" } else { "" };
        let denominator = self.precision.denominator() as i64;
        let whole = self.units / denominator;
        let fraction = self.units - whole * denominator;
        // Use unsigned_abs() to avoid panicking on i64::MIN, which has no positive counterpart in i64.
        // This is critical for precision 0 where `whole` can equal i64::MIN directly.
        let whole_abs = whole.unsigned_abs();
        let fraction_abs = fraction.unsigned_abs();

        if fraction == 0 {
            write!(f, "{}{}", sign, whole_abs)
        } else {
            // Format the fractional part with the instance's precision
            let decimals = format!(
                "{:0>precision$}",
                fraction_abs,
                precision = self.precision.value() as usize
            );
            let decimals = decimals.trim_end_matches('0'); // Remove trailing zeros

            // Show minimal precision needed, but respect the instance's precision
            if decimals.is_empty() {
                write!(f, "{}{}", sign, whole_abs)
            } else {
                write!(f, "{}{}.{}", sign, whole_abs, decimals)
            }
        }
    }
}

impl fmt::Debug for ZFuel {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Fuel({}) precision({})", self, self.precision.value())
    }
}

/// PartialEq implementation for value-based equality
///
/// Compares ZFuel values by their numeric value, ignoring precision differences.
/// Returns `false` if scaling fails (e.g., due to overflow), indicating the values
/// are not equal.
impl PartialEq for ZFuel {
    fn eq(&self, other: &ZFuel) -> bool {
        // If precisions are the same, just compare units directly
        if self.precision == other.precision {
            return self.units == other.units;
        }

        // Scale both to the same precision (use the higher one to avoid losing precision)
        let target_precision = std::cmp::max(self.precision, other.precision);
        let self_scaled = match Self::scale_units(self.units, self.precision, target_precision) {
            Ok(v) => v,
            Err(_) => return false, // If scaling fails, values are not equal
        };
        let other_scaled = match Self::scale_units(other.units, other.precision, target_precision) {
            Ok(v) => v,
            Err(_) => return false, // If scaling fails, values are not equal
        };
        self_scaled == other_scaled
    }
}

/// Eq implementation for value-based equality
///
/// Provides total equality of ZFuel values by their numeric value.
/// This implementation assumes that scaling will always succeed for valid ZFuel values.
impl Eq for ZFuel {}

/// PartialOrd implementation for value-based comparison
///
/// Compares ZFuel values by their numeric value, ignoring precision differences.
/// Returns `None` if scaling fails (e.g., due to overflow), indicating the values
/// cannot be compared.
impl PartialOrd for ZFuel {
    fn partial_cmp(&self, other: &ZFuel) -> Option<std::cmp::Ordering> {
        // If precisions are the same, just compare units directly
        if self.precision == other.precision {
            return Some(self.units.cmp(&other.units));
        }

        // Scale both to the same precision (use the higher one to avoid losing precision)
        let target_precision = std::cmp::max(self.precision, other.precision);
        let self_scaled = Self::scale_units(self.units, self.precision, target_precision).ok()?;
        let other_scaled =
            Self::scale_units(other.units, other.precision, target_precision).ok()?;
        Some(self_scaled.cmp(&other_scaled))
    }
}

/// Ord implementation for value-based comparison
///
/// Provides total ordering of ZFuel values by their numeric value.
/// This implementation assumes that scaling will always succeed for valid ZFuel values.
/// If scaling fails, the comparison will panic (which should not happen in practice
/// for values within the valid range).
impl Ord for ZFuel {
    fn cmp(&self, other: &ZFuel) -> std::cmp::Ordering {
        // If precisions are the same, just compare units directly
        if self.precision == other.precision {
            return self.units.cmp(&other.units);
        }

        // Scale both to the same precision (use the higher one to avoid losing precision)
        let target_precision = std::cmp::max(self.precision, other.precision);
        // For Ord, we expect scaling to always succeed for valid values
        // If it fails, we'll get a panic, which is appropriate for Ord
        let self_scaled = Self::scale_units(self.units, self.precision, target_precision)
            .expect("Scaling failed in Ord::cmp - this should not happen for valid ZFuel values");
        let other_scaled = Self::scale_units(other.units, other.precision, target_precision)
            .expect("Scaling failed in Ord::cmp - this should not happen for valid ZFuel values");
        self_scaled.cmp(&other_scaled)
    }
}

///
/// Fuel Operators -- Numerical operations with/without validity check
///
/// Neg, Add, Sub, Mul, Div of Fuel always results in a checked Result<Fuel, ZFuelError> value.
/// So, it is necessary to handle the ZFuelError that may result from invalid computations
/// before assigning any valid Fuel result:
///
/// > let Fuel: value = ( Fuel::from_str( "1.0" ) + Fuel::from_str( "2.0" ) )?
///
/// Attempting to use an existing Result::Err always maintains the lhs-most Err.
///

/// Negation of Fuel can lead to an error at MINVALUE, so FuelResult is returned.  Because we cannot
/// implement Neg for non-local type result::Result<Fuel,...>, to negate an &FuelResult, use
/// something like: fuel_result.to_owned().and_then(|f| -f)
impl Neg for ZFuel {
    // - Fuel
    type Output = FuelResult;
    fn neg(self) -> FuelResult {
        Ok(match self.units.checked_neg() {
            Some(units) => ZFuel {
                units,
                precision: self.precision,
            },
            None => {
                return Err(ZFuelError::Range(format!(
                    "Overflow in negation of z Fuel amount {}",
                    self
                )))
            }
        })
    }
}

impl Neg for &ZFuel {
    // - &Fuel
    type Output = FuelResult;
    fn neg(self) -> FuelResult {
        -*self
    }
}

impl Add for ZFuel {
    // Fuel + Fuel
    type Output = FuelResult;
    fn add(self, rhs: ZFuel) -> Self::Output {
        // Use the higher precision for the result. Scaling both operands up is always safe
        // for legal ZFuel values (the bounded-value-space invariant guarantees this).
        let result_precision = std::cmp::max(self.precision, rhs.precision);
        let lhs_scaled = ZFuel::scale_units(self.units, self.precision, result_precision)?;
        let rhs_scaled = ZFuel::scale_units(rhs.units, rhs.precision, result_precision)?;

        let sum = lhs_scaled.checked_add(rhs_scaled).ok_or_else(|| {
            ZFuelError::Range(format!(
                "Overflow in addition of z Fuel amount {} + {}",
                self, rhs
            ))
        })?;

        // Range-check the result through the validating constructor so the invariant
        // (|units| <= cap for the chosen precision) is preserved by arithmetic.
        ZFuel::new(sum, result_precision)
    }
}

impl Add<&ZFuel> for ZFuel {
    // Fuel + &Fuel
    type Output = FuelResult;
    fn add(self, rhs: &ZFuel) -> Self::Output {
        self + *rhs
    }
}

impl Add<ZFuel> for &ZFuel {
    // &Fuel + Fuel
    type Output = FuelResult;
    fn add(self, rhs: ZFuel) -> Self::Output {
        *self + rhs
    }
}

impl Add for &ZFuel {
    // &Fuel + &Fuel
    type Output = FuelResult;
    fn add(self, rhs: &ZFuel) -> Self::Output {
        *self + *rhs
    }
}

impl Add<FuelResult> for ZFuel {
    // Fuel + Result<Fuel, ZFuelError>
    type Output = FuelResult;
    fn add(self, other: Self::Output) -> Self::Output {
        match other {
            Ok(rhs) => self + rhs,
            Err(rhs_e) => Err(rhs_e),
        }
    }
}

impl Add<FuelResult> for &ZFuel {
    // &Fuel + Result<Fuel, ZFuelError>
    type Output = FuelResult;
    fn add(self, other: Self::Output) -> Self::Output {
        match other {
            Ok(rhs) => *self + rhs,
            Err(rhs_e) => Err(rhs_e),
        }
    }
}

impl Add<&FuelResult> for ZFuel {
    // Fuel + &Result<Fuel, ZFuelError>
    type Output = FuelResult;
    fn add(self, other: &Self::Output) -> Self::Output {
        match other {
            Ok(rhs) => self + *rhs,
            Err(rhs_e) => Err(rhs_e.clone()),
        }
    }
}

impl Add<&FuelResult> for &ZFuel {
    // &Fuel + &Result<Fuel, ZFuelError>
    type Output = FuelResult;
    fn add(self, other: &Self::Output) -> Self::Output {
        match other {
            Ok(rhs) => *self + *rhs,
            Err(rhs_e) => Err(rhs_e.clone()),
        }
    }
}

impl Add<ZFuel> for FuelResult {
    // Result<Fuel, ZFuelError> + Fuel
    type Output = FuelResult;
    fn add(self, rhs: ZFuel) -> Self::Output {
        match self {
            Ok(lhs) => lhs + rhs,
            Err(lhs_e) => Err(lhs_e),
        }
    }
}

impl Add<&ZFuel> for FuelResult {
    // Result<Fuel, ZFuelError> + &Fuel
    type Output = FuelResult;
    fn add(self, rhs: &ZFuel) -> Self::Output {
        match self {
            Ok(lhs) => lhs + *rhs,
            Err(lhs_e) => Err(lhs_e),
        }
    }
}

impl Add<ZFuel> for &FuelResult {
    // &Result<Fuel, ZFuelError> + Fuel
    type Output = FuelResult;
    fn add(self, rhs: ZFuel) -> Self::Output {
        match self {
            Ok(lhs) => *lhs + rhs,
            Err(lhs_e) => Err(lhs_e.clone()),
        }
    }
}

impl Add<&ZFuel> for &FuelResult {
    // &Result<Fuel, ZFuelError> + &Fuel
    type Output = FuelResult;
    fn add(self, rhs: &ZFuel) -> Self::Output {
        match self {
            Ok(lhs) => *lhs + *rhs,
            Err(lhs_e) => Err(lhs_e.clone()),
        }
    }
}

impl AddAssign<ZFuel> for FuelResult {
    // Result<Fuel, ZFuelError> += Fuel
    fn add_assign(&mut self, rhs: ZFuel) {
        *self = match self {
            Ok(lhs) => ZFuel::from(lhs) + rhs,
            Err(lhs_e) => Err(lhs_e.clone()),
        };
    }
}

impl AddAssign<&ZFuel> for FuelResult {
    // Result<Fuel, ZFuelError> += &Fuel
    fn add_assign(&mut self, rhs: &ZFuel) {
        *self = match self {
            Ok(lhs) => ZFuel::from(lhs) + rhs,
            Err(lhs_e) => Err(lhs_e.clone()),
        };
    }
}

impl Sub for ZFuel {
    // Fuel - Fuel
    type Output = FuelResult;
    fn sub(self, rhs: ZFuel) -> Self::Output {
        let result_precision = std::cmp::max(self.precision, rhs.precision);
        let lhs_scaled = ZFuel::scale_units(self.units, self.precision, result_precision)?;
        let rhs_scaled = ZFuel::scale_units(rhs.units, rhs.precision, result_precision)?;

        let diff = lhs_scaled.checked_sub(rhs_scaled).ok_or_else(|| {
            ZFuelError::Range(format!(
                "Overflow in subtraction of z Fuel amount {} - {}",
                self, rhs
            ))
        })?;

        // Range-check the result through the validating constructor so the invariant
        // (|units| <= cap for the chosen precision) is preserved by arithmetic.
        ZFuel::new(diff, result_precision)
    }
}

impl Sub<&ZFuel> for ZFuel {
    // Fuel - &Fuel
    type Output = FuelResult;
    fn sub(self, rhs: &ZFuel) -> Self::Output {
        self - *rhs
    }
}

impl Sub<ZFuel> for &ZFuel {
    // &Fuel - Fuel
    type Output = FuelResult;
    fn sub(self, rhs: ZFuel) -> Self::Output {
        *self - rhs
    }
}

impl Sub for &ZFuel {
    // &Fuel - &Fuel
    type Output = FuelResult;
    fn sub(self, rhs: &ZFuel) -> Self::Output {
        *self - *rhs
    }
}

impl Sub<FuelResult> for ZFuel {
    // Fuel - Result<Fuel, ZFuelError>
    type Output = FuelResult;
    fn sub(self, other: Self::Output) -> Self::Output {
        match other {
            Ok(rhs) => self - rhs,
            Err(rhs_e) => Err(rhs_e),
        }
    }
}

impl Sub<FuelResult> for &ZFuel {
    // &Fuel - Result<Fuel, ZFuelError>
    type Output = FuelResult;
    fn sub(self, other: Self::Output) -> Self::Output {
        match other {
            Ok(rhs) => *self - rhs,
            Err(rhs_e) => Err(rhs_e),
        }
    }
}

impl Sub<&FuelResult> for ZFuel {
    // Fuel - &Result<Fuel, ZFuelError>
    type Output = FuelResult;
    fn sub(self, other: &Self::Output) -> Self::Output {
        match other {
            Ok(rhs) => self - *rhs,
            Err(rhs_e) => Err(rhs_e.clone()),
        }
    }
}

impl Sub<&FuelResult> for &ZFuel {
    // &Fuel - &Result<Fuel, ZFuelError>
    type Output = FuelResult;
    fn sub(self, other: &Self::Output) -> Self::Output {
        match other {
            Ok(rhs) => *self - *rhs,
            Err(rhs_e) => Err(rhs_e.clone()),
        }
    }
}

impl Sub<ZFuel> for FuelResult {
    // Result<Fuel, ZFuelError> - Fuel
    type Output = FuelResult;
    fn sub(self, rhs: ZFuel) -> Self::Output {
        match self {
            Ok(lhs) => lhs - rhs,
            Err(lhs_e) => Err(lhs_e),
        }
    }
}

impl Sub<&ZFuel> for FuelResult {
    // Result<Fuel, ZFuelError> - &Fuel
    type Output = FuelResult;
    fn sub(self, rhs: &ZFuel) -> Self::Output {
        match self {
            Ok(lhs) => lhs - *rhs,
            Err(lhs_e) => Err(lhs_e),
        }
    }
}

impl Sub<ZFuel> for &FuelResult {
    // &Result<Fuel, ZFuelError> - Fuel
    type Output = FuelResult;
    fn sub(self, rhs: ZFuel) -> Self::Output {
        match self {
            Ok(lhs) => *lhs - rhs,
            Err(lhs_e) => Err(lhs_e.clone()),
        }
    }
}

impl Sub<&ZFuel> for &FuelResult {
    // &Result<Fuel, ZFuelError> - &Fuel
    type Output = FuelResult;
    fn sub(self, rhs: &ZFuel) -> Self::Output {
        match self {
            Ok(lhs) => *lhs - *rhs,
            Err(lhs_e) => Err(lhs_e.clone()),
        }
    }
}

impl SubAssign<ZFuel> for FuelResult {
    // Result<Fuel, ZFuelError> -= Fuel
    fn sub_assign(&mut self, rhs: ZFuel) {
        *self = match self {
            Ok(lhs) => ZFuel::from(lhs) - rhs,
            Err(lhs_e) => Err(lhs_e.clone()),
        };
    }
}

impl SubAssign<&ZFuel> for FuelResult {
    // Result<Fuel, ZFuelError> -= &Fuel
    fn sub_assign(&mut self, rhs: &ZFuel) {
        *self = match self {
            Ok(lhs) => ZFuel::from(lhs) - rhs,
            Err(lhs_e) => Err(lhs_e.clone()),
        };
    }
}

/// Fuel * Fraction, Fuel / Fraction -- precise multiplication with rounding up
///
/// Performs exact multiplication: result = (units * numerator) / denominator
/// The result uses maximum precision (6) to ensure fractional results can be represented.
/// When there's a remainder, rounds up (away from zero) to avoid losing value.
/// This ensures that 10 * 1% = 0.1 regardless of input precision.
impl Mul<Fraction> for ZFuel {
    // Fuel * Fraction
    type Output = FuelResult;
    fn mul(self, rhs: Fraction) -> Self::Output {
        // Scale input to maximum precision (6) to ensure fractional results can be represented
        let scaled_units = Self::scale_units(self.units, self.precision, Precision::DEFAULT)?;

        // Try precise multiplication: (units * numerator) / denominator
        if let Some(product) = scaled_units.checked_mul(rhs.numerator as i64) {
            // Check for remainder to round up (away from zero)
            let remainder = product % rhs.denominator as i64;
            let quotient = product / rhs.denominator as i64;

            // Round away from zero based on the sign of the *product* (i.e. the sign of the
            // remainder, since `i64 % i64` in Rust has the same sign as the dividend). Branching
            // on `quotient` is incorrect when the product is small-negative: in that case the
            // quotient is 0 (non-negative) but rounding still needs to go toward -infinity.
            let units = if remainder != 0 {
                if remainder > 0 {
                    quotient
                        .checked_add(1)
                        .ok_or_else(|| ZFuelError::FractionOverflow((self, rhs)))?
                } else {
                    quotient
                        .checked_sub(1)
                        .ok_or_else(|| ZFuelError::FractionOverflow((self, rhs)))?
                }
            } else {
                quotient
            };

            Ok(ZFuel {
                units,
                precision: Precision::DEFAULT,
            })
        } else {
            // Overflow would occur, use divide-first approach with rounding up
            // This avoids overflow while rounding up on remainder (away from zero)
            match scaled_units.checked_div(rhs.denominator as i64) {
                Some(quotient) => match quotient.checked_mul(rhs.numerator as i64) {
                    Some(units) => {
                        // Handle remainder with rounding up (away from zero)
                        let remainder_contribution = scaled_units
                            .checked_rem(rhs.denominator as i64)
                            .and_then(|rem| rem.checked_mul(rhs.numerator as i64))
                            .and_then(|rem_prod| {
                                if rem_prod == 0 {
                                    Some(0)
                                } else if rem_prod > 0 {
                                    // Round up: add (denominator - 1) then divide
                                    rem_prod
                                        .checked_add(rhs.denominator as i64 - 1)
                                        .map(|sum| sum / rhs.denominator as i64)
                                } else {
                                    // Round up (away from zero for negative): subtract (denominator - 1) then divide
                                    rem_prod
                                        .checked_sub(rhs.denominator as i64 - 1)
                                        .map(|diff| diff / rhs.denominator as i64)
                                }
                            })
                            .unwrap_or(0);

                        Ok(ZFuel {
                            units: units + remainder_contribution,
                            precision: Precision::DEFAULT,
                        })
                    }
                    None => Err(ZFuelError::FractionOverflow((self, rhs))),
                },
                None => Err(ZFuelError::FractionOverflow((self, rhs))),
            }
        }
    }
}

impl Mul<&Fraction> for ZFuel {
    // Fuel * &Fraction
    type Output = FuelResult;
    fn mul(self, rhs: &Fraction) -> Self::Output {
        self * *rhs
    }
}

impl Mul<Fraction> for &ZFuel {
    // &Fuel * Fraction
    type Output = FuelResult;
    fn mul(self, rhs: Fraction) -> Self::Output {
        *self * rhs
    }
}

impl Mul<&Fraction> for &ZFuel {
    // &Fuel * &Fraction
    type Output = FuelResult;
    fn mul(self, rhs: &Fraction) -> Self::Output {
        *self * *rhs
    }
}

impl MulAssign<Fraction> for FuelResult {
    // Result<Fuel, ZFuelError> *= Fraction
    fn mul_assign(&mut self, rhs: Fraction) {
        *self = match self {
            Ok(lhs) => ZFuel::from(lhs) * rhs,
            Err(lhs_e) => Err(lhs_e.clone()),
        };
    }
}

impl MulAssign<&Fraction> for FuelResult {
    // Result<Fuel, ZFuelError> *= &Fraction
    fn mul_assign(&mut self, rhs: &Fraction) {
        *self = match self {
            Ok(lhs) => ZFuel::from(lhs) * rhs,
            Err(lhs_e) => Err(lhs_e.clone()),
        };
    }
}

impl Div<Fraction> for ZFuel {
    // Fuel / Fraction
    type Output = FuelResult;
    fn div(self, rhs: Fraction) -> Self::Output {
        self * Fraction {
            numerator: rhs.denominator,
            denominator: rhs.numerator,
        }
    }
}

impl Div<&Fraction> for ZFuel {
    // Fuel / &Fraction
    type Output = FuelResult;
    fn div(self, rhs: &Fraction) -> Self::Output {
        self / *rhs
    }
}

impl Div<Fraction> for &ZFuel {
    // &Fuel / Fraction
    type Output = FuelResult;
    fn div(self, rhs: Fraction) -> Self::Output {
        *self / rhs
    }
}

impl Div<&Fraction> for &ZFuel {
    // &Fuel / &Fraction
    type Output = FuelResult;
    fn div(self, rhs: &Fraction) -> Self::Output {
        *self / *rhs
    }
}

#[cfg(test)]
pub mod tests {
    use crate::fuel::{self, u64_to_i64, FuelResult, Precision, ZFuel, INTLIMIT};
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
    /// smoke test Fuel
    fn fuel_smoke_test() {
        let f1 = ZFuel::from_str("1.0").unwrap();
        //let f1 = ZFuel::from_str( "0x5f5e100" ).unwrap();
        // "1.0" has precision 1, so units = 1 * 10 = 10
        assert_eq!(f1.units, 10);
        assert_eq!(f1.precision.value(), 1);
        // Whole numbered values do not include fractional precision
        let d1 = format!("{}", f1);
        assert_eq!(
            d1,
            match fuel::DECSHOWN {
                1 => "1",
                2 => "1",
                3 => "1",
                4 => "1",
                5 => "1",
                6 => "1",
                7 => "1",
                8 => "1",
                _ => "unknown",
            }
        );

        let f2 = ZFuel::from(-1234567890);
        assert_eq!(f2.units, -1234567890_i64);
        // At least the required amount of precision is always supplied to ensure no loss of data
        let d2 = format!("{}", f2);
        assert_eq!(
            d2,
            match fuel::DECSHOWN {
                6 => "-1234.567890",
                _ => "-1234.56789",
            }
        );

        // Extending out fractions to fill at leas
        let f3 = ZFuel::from_str("999.5").unwrap();
        // "999.5" has precision 1, so units = 999 * 10 + 5 = 9995
        assert_eq!(f3.units, 9995_i64);
        assert_eq!(f3.precision.value(), 1);

        let d3 = format!("{}", f3);
        assert_eq!(
            d3,
            match fuel::DECSHOWN {
                1 => "999.5",
                2 => "999.50",
                3 => "999.500",
                4 => "999.5000",
                5 => "999.50000",
                6 => "999.500000",
                7 => "999.5000000",
                8 => "999.50000000",
                _ => "unknown",
            }
        );

        // Ensure that excessive fractional amounts are truncated silently
        let f4 = ZFuel::from_str("-1234.5678901234567").unwrap();
        assert_eq!(f4.units, -1234567890);
        let d4 = format!("{}", f4);
        assert_eq!(d4, "-1234.56789");

        // See if precision retaining maximums are enforced.  We're assuming i64 is NOT actually
        // implemented as IEEE 754 double-precision (where +/- 2^53-1 is the precision-loss limit).
        // Try to round-trip full-precision z Fuel values through Display "#.##"
        assert_eq!(fuel::MAXVALUE, 9_223_372_036_854_775_807);
        assert_eq!(fuel::MAXRANGE, 9_223_372_036_854_775_807);
        assert_eq!(fuel::MINVALUE, -9_223_372_036_854_775_808);
        assert_eq!(fuel::MINRANGE, 9_223_372_036_854_775_808);

        assert_eq!(
            format!("{:?}", ZFuel::from_str(&"9223372036854.775807")),
            "Ok(Fuel(9223372036854.775807) precision(6))"
        );
        assert_eq!(
            format!("{:?}", ZFuel::from_str(&"0x7fffffffffffffff")),
            "Ok(Fuel(9223372036854.775807) precision(6))"
        );
        assert_eq!(
            format!("{:?}", ZFuel::from_str(&"-9223372036854.775808")),
            "Ok(Fuel(-9223372036854.775808) precision(6))"
        );
        assert_eq!(
            format!("{:?}", ZFuel::from_str(&"-0x8000000000000000")),
            "Ok(Fuel(-9223372036854.775808) precision(6))"
        );

        match ZFuel::from_str( &"9223372036854.775808" ) { // MAXRANGE + 1
            Ok(f) => panic!( "Expected failure due to fuel::MAXRANGE did not occur: ♓{}", f ),
            Err(e) => assert_eq!( format!("{}", e ),
                                  "Fuel Range Error: Exceeded range for z Fuel mantissa 9223372036854000000, fraction 775808" ),
        }
        match ZFuel::from_str( &"-9223372036854.775809" ) {
            Ok(f) => panic!( "Expected failure due to fuel::MINVRANGE did not occur: ♓{}", f ),
            Err(e) => assert_eq!( format!("{}", e ),
                                  "Fuel Range Error: Exceeded range for z Fuel mantissa 9223372036854000000, fraction 775809" ),
        }
    }

    #[test]
    fn fuel_operators() {
        // Fuel + Fuel
        let sum = ZFuel::from_str("1.23").unwrap() + ZFuel::from_str("-1000").unwrap();
        match &sum {
            Ok(ref f) => assert_eq!(format!("{}", f), "-998.77"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        // Result<Fuel,...> + Fuel
        let sum2 = sum + ZFuel::from_str("100").unwrap();
        match &sum2 {
            Ok(ref f) => assert_eq!(format!("{}", f), "-898.77"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        // Fuel + Result<Fuel,...>
        let sum3 = ZFuel::from_str("-1111.23").unwrap() + sum2;
        match &sum3 {
            Ok(ref f) => assert_eq!(format!("{}", f), "-2010"),
            Err(e) => panic!("Expected success, not {}", e),
        }

        // Check all Fuel + Fuel ref variants
        match ZFuel::from(1_000_000) + ZFuel::from(1) {
            Ok(f) => assert_eq!(format!("{}", f), "1.000001"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match ZFuel::from(1_000_000) + &ZFuel::from(2) {
            Ok(f) => assert_eq!(format!("{}", f), "1.000002"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match &ZFuel::from(2_000_000) + ZFuel::from(1) {
            Ok(f) => assert_eq!(format!("{}", f), "2.000001"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match &ZFuel::from(2_000_000) + &ZFuel::from(2) {
            Ok(f) => assert_eq!(format!("{}", f), "2.000002"),
            Err(e) => panic!("Expected success, not {}", e),
        }

        // Check all Result<ZFuel,...> + ZFuel ref variants
        match ZFuel::from_str("1") + ZFuel::from(1) {
            Ok(f) => assert_eq!(format!("{}", f), "1.000001"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match ZFuel::from_str("1") + &ZFuel::from(1) {
            Ok(f) => assert_eq!(format!("{}", f), "1.000001"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match &ZFuel::from_str("1") + ZFuel::from(1) {
            Ok(f) => assert_eq!(format!("{}", f), "1.000001"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match &ZFuel::from_str("1") + &ZFuel::from(1) {
            Ok(f) => assert_eq!(format!("{}", f), "1.000001"),
            Err(e) => panic!("Expected success, not {}", e),
        }

        // Check all ZFuel + Result<ZFuel,...> ref variants
        match ZFuel::from(1) + ZFuel::from_str("1") {
            Ok(f) => assert_eq!(format!("{}", f), "1.000001"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match &ZFuel::from(1) + ZFuel::from_str("1") {
            Ok(f) => assert_eq!(format!("{}", f), "1.000001"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match ZFuel::from(1) + &ZFuel::from_str("1") {
            Ok(f) => assert_eq!(format!("{}", f), "1.000001"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match &ZFuel::from(1) + &ZFuel::from_str("1") {
            Ok(f) => assert_eq!(format!("{}", f), "1.000001"),
            Err(e) => panic!("Expected success, not {}", e),
        }

        // Check all Result<Fuel,...> += Fuel ref variants
        let mut fa = ZFuel::from_str("1");
        fa += ZFuel::from(1);
        match fa {
            Ok(f) => assert_eq!(format!("{}", f), "1.000001"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        fa += &ZFuel::from(-2);
        match fa {
            Ok(f) => assert_eq!(format!("{}", f), "0.999999"),
            Err(e) => panic!("Expected success, not {}", e),
        }

        // Check all ZFuel - ZFuel ref variants: 1.0 - 0.000001
        match ZFuel::from(1_000_000) - ZFuel::from(1) {
            Ok(f) => assert_eq!(format!("{}", f), "0.999999"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match ZFuel::from(1_000_000) - &ZFuel::from(2) {
            Ok(f) => assert_eq!(format!("{}", f), "0.999998"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match &ZFuel::from(2_000_000) - ZFuel::from(1) {
            Ok(f) => assert_eq!(format!("{}", f), "1.999999"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match &ZFuel::from(2_000_000) - &ZFuel::from(2) {
            Ok(f) => assert_eq!(format!("{}", f), "1.999998"),
            Err(e) => panic!("Expected success, not {}", e),
        }

        // Check all Result<ZFuel,...> - ZFuel ref variants: 1.0 - 0.000001
        match ZFuel::from_str("1") - ZFuel::from(1) {
            Ok(f) => assert_eq!(format!("{}", f), "0.999999"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match ZFuel::from_str("1") - &ZFuel::from(1) {
            Ok(f) => assert_eq!(format!("{}", f), "0.999999"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match &ZFuel::from_str("1") - ZFuel::from(1) {
            Ok(f) => assert_eq!(format!("{}", f), "0.999999"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match &ZFuel::from_str("1") - &ZFuel::from(1) {
            Ok(f) => assert_eq!(format!("{}", f), "0.999999"),
            Err(e) => panic!("Expected success, not {}", e),
        }

        // Check all ZFuel - Result<ZFuel,...> ref variants: 0.000001 - 1.0
        match ZFuel::from(1) - ZFuel::from_str("1") {
            Ok(f) => assert_eq!(format!("{}", f), "-0.999999"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match &ZFuel::from(1) - ZFuel::from_str("1") {
            Ok(f) => assert_eq!(format!("{}", f), "-0.999999"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match ZFuel::from(1) - &ZFuel::from_str("1") {
            Ok(f) => assert_eq!(format!("{}", f), "-0.999999"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match &ZFuel::from(1) - &ZFuel::from_str("1") {
            Ok(f) => assert_eq!(format!("{}", f), "-0.999999"),
            Err(e) => panic!("Expected success, not {}", e),
        }

        // Check all Result<ZFuel,...> -= ZFuel ref variants
        let mut fa = ZFuel::from_str("1");
        fa -= ZFuel::from(1);
        match fa {
            Ok(f) => assert_eq!(format!("{}", f), "0.999999"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        fa -= &ZFuel::from(2_000_001);
        match fa {
            Ok(f) => assert_eq!(format!("{}", f), "-1.000002"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        fa -= &ZFuel::from(-2_000_003);
        match fa {
            Ok(f) => assert_eq!(format!("{}", f), "1.000001"),
            Err(e) => panic!("Expected success, not {}", e),
        }

        // And make sure errors produced and propogate; later terms just propogate original Err(_)
        match ZFuel::from( u64_to_i64( true, fuel::MINRANGE, 0_u64, fuel::MINRANGE ).unwrap() ) - ZFuel::from( 1 )  {
            Ok(f) => panic!( "Expected failure, not {}", f ),
            Err(e) => assert_eq!( format!( "{}", e ),
                                  "Fuel Range Error: Overflow in subtraction of z Fuel amount -9223372036854.775808 - 0.000001" ),
        }
        match ZFuel::from( u64_to_i64( true, fuel::MINRANGE, 0_u64, fuel::MINRANGE ).unwrap() ) - ZFuel::from( 1 ) + ZFuel::from( 1 ) {
            Ok(f) => panic!( "Expected failure, not {}", f ),
            Err(e) => assert_eq!( format!( "{}", e ),
                                  "Fuel Range Error: Overflow in subtraction of z Fuel amount -9223372036854.775808 - 0.000001" ),
        }

        // Try negation
        assert_eq!(
            format!("{}", (-ZFuel::from(fuel::MAXVALUE)).unwrap()),
            "-9223372036854.775807"
        );
        assert_eq!(
            format!("{}", (-&ZFuel::from(fuel::MAXVALUE)).unwrap()),
            "-9223372036854.775807"
        );
        // Negating the largest negative value should lead to overflow
        assert_eq!(
            format!("{:?}", -&ZFuel::from(fuel::MINVALUE)),
            "Err(Range(\"Overflow in negation of z Fuel amount -9223372036854.775808\"))"
        );
    }

    #[test]
    fn fuel_comparisons() {
        assert_eq!(ZFuel::from(1_000_001) > ZFuel::from(1_000_000), true);
        assert_eq!(ZFuel::from(1_000_001) < ZFuel::from(1_000_000), false);
        assert_eq!(ZFuel::from(1_000_000) < ZFuel::from(1_000_001), true);

        assert_eq!(ZFuel::from(1_000_000) == ZFuel::from(1_000_001), false);
        assert_eq!(ZFuel::from(1_000_000) <= ZFuel::from(1_000_001), true);
        assert_eq!(ZFuel::from(1_000_000) >= ZFuel::from(1_000_001), false);

        assert_eq!(ZFuel::from(1_000_000) == ZFuel::from(1_000_000), true);
        assert_eq!(ZFuel::from(1_000_000) <= ZFuel::from(1_000_000), true);
        assert_eq!(ZFuel::from(1_000_000) >= ZFuel::from(1_000_000), true);
    }

    #[test]
    fn fuel_comparisons_value_based() {
        // Test that operators now use value-based comparison (ignoring precision)
        let a = ZFuel::new(10, Precision::new(0).unwrap()).unwrap(); // 10
        let b = ZFuel::new(10000000, Precision::new(6).unwrap()).unwrap(); // 10.000000
        assert_eq!(a == b, true); // Value-based equality: 10 == 10.000000
        assert_eq!(a < b, false); // Value-based: 10 is not < 10.000000
        assert_eq!(a > b, false); // Value-based: 10 is not > 10.000000
        assert_eq!(a <= b, true); // Value-based: 10 <= 10.000000
        assert_eq!(a >= b, true); // Value-based: 10 >= 10.000000

        // Test with different values
        let c = ZFuel::new(12345, Precision::new(2).unwrap()).unwrap(); // 123.45
        let d = ZFuel::new(12346000, Precision::new(3).unwrap()).unwrap(); // 123.460
        assert_eq!(c < d, true); // 123.45 < 123.460
        assert_eq!(c > d, false);
        assert_eq!(c <= d, true);
        assert_eq!(c >= d, false);

        // Test with same precision (should work as before)
        let e = ZFuel::new(100, Precision::new(2).unwrap()).unwrap();
        let f = ZFuel::new(200, Precision::new(2).unwrap()).unwrap();
        assert_eq!(e < f, true);
        assert_eq!(e > f, false);
        assert_eq!(e <= f, true);
        assert_eq!(e >= f, false);
    }

    use crate::fraction::Fraction;
    #[test]
    fn fuel_compute_fees() {
        // Transaction fee computation requires computing a percentage, which is typically something like:
        //
        //     amount * ( 100 / <percentage> )
        //
        // where <percentage> is something like 1, 4, 0.25
        //
        // However, we don't want to perform floating point operations, nor prevent the calculation
        // of TX fees on values up to the maximum value, so we can't multiply amounts by numbers
        // before dividing.
        //
        // So, transaction fees have to be computable using division and addition/subtraction only.
        //
        // .25% is 1/400th, 3.5% is 35/1000 is 7/200ths.  So, we'll support multiplying by a ratio,
        // where we will first divide by the denominator before multiplying by the numerator. This
        // can lose precision on small values; for example, taking 3.5% of a value below 200 Holo
        // Fuel::units will result in fees of 0, instead of 7: 199 / 200 * 7 == 0.  And even on
        // larger values, since we're doing integer division, we'll still lose precision: 399 / 200
        // * 7 == 7, not the perhaps expected 13.  So, in essence, we'll always be "rounding down"
        // z Fuel fees.  But, considering that z Fuel is denominated in units of
        // 1/100,000,000th of a z Fuel, these rounding truncation errors will only be significant
        // when computing fees on exceedingly tiny transactions.

        let feepct = Fraction::new(35, 1000).unwrap().reduce();
        assert_eq!((feepct.numerator, feepct.denominator), (7, 200));

        // Observe that we end up losing precision on very small transactions, and always round up.
        //
        // The infinite precision fee calculation should "round up" to H0.000014:
        //     H0.000399 * 7 / 200 == H0.000013965
        // But instead, we lose precision both by the reverse-ordering of multiplying out the
        // Fraction (to avoid overflow on large Fuel values), and through truncation:
        //     H0.000399     / 200 == H0.000001995 =~= H0.000001 * 7 == H0.000007
        // When we round up, we first compute the remainder of the division:
        //     H.000399      % 200 == 199
        // Then we amplify by the numerator and gross it up by 1 less than the denominator:
        //           199 * 7 + 199 == 1592
        // And then see how many denominators worth of rounding error we discarded:
        //              1592 / 200 == 7
        let feeamt = ZFuel {
            units: 399,
            precision: Precision::DEFAULT,
        } * &feepct;
        match &feeamt {
            Ok(ref f) => assert_eq!(format!("{}", f), "0.000014"), // Precise multiplication with rounding up: 399 * 7 / 200 = 13.965, rounded up to 14
            Err(e) => panic!("Expected success, not {}", e),
        }

        // See that division by the inverse Fraction is identical
        let inv_feepct = Fraction {
            denominator: feepct.numerator,
            numerator: feepct.denominator,
        };
        let feeamt = ZFuel {
            units: 399,
            precision: Precision::DEFAULT,
        } / &inv_feepct;
        match &feeamt {
            Ok(ref f) => assert_eq!(format!("{}", f), "0.000014"), // Precise multiplication with rounding up
            Err(e) => panic!("Expected success, not {}", e),
        }

        // And, we can be assured of being able to compute fees on the maximum transaction value,
        // 2^63-1: 9,223,372,036,854,775,807 * 7 / 200 == 322818021289917153.245, so rounded up we
        // should get a fee of: 322818021289917154, or H322818021289.917154
        let amount = ZFuel {
            units: fuel::MAXVALUE,
            precision: Precision::DEFAULT,
        };
        let feeamt = amount * &feepct;
        match feeamt {
            Ok(f) => assert_eq!(format!("{}", f), "322818021289.917154"), // was "322818021289.917154" w/o round up
            Err(e) => panic!("Expected success, not {}", e),
        };
        match ZFuel::new(fuel::MINVALUE, Precision::DEFAULT).unwrap() * &feepct {
            // try -'ve, to ensure round up works
            Ok(f) => assert_eq!(format!("{}", f), "-322818021289.917154"),
            Err(e) => panic!("Expected success, not {}", e),
        };

        // Test all {T,&T} {*,/} {U,&U} combinations
        match ZFuel::from(fuel::MAXVALUE) * Fraction::new(35, 1000).unwrap().reduce() {
            Ok(f) => assert_eq!(format!("{}", f), "322818021289.917154"),
            Err(e) => panic!("Expected success, not {}", e),
        };
        match &ZFuel::from(fuel::MAXVALUE) * Fraction::new(35, 1000).unwrap().reduce() {
            Ok(f) => assert_eq!(format!("{}", f), "322818021289.917154"),
            Err(e) => panic!("Expected success, not {}", e),
        };
        match ZFuel::from(fuel::MAXVALUE) * &Fraction::new(35, 1000).unwrap().reduce() {
            Ok(f) => assert_eq!(format!("{}", f), "322818021289.917154"),
            Err(e) => panic!("Expected success, not {}", e),
        };
        match &ZFuel::from(fuel::MAXVALUE) * &Fraction::new(35, 1000).unwrap().reduce() {
            Ok(ref f) => assert_eq!(format!("{}", f), "322818021289.917154"),
            Err(e) => panic!("Expected success, not {}", e),
        };

        match ZFuel::from(fuel::MAXVALUE) / Fraction::new(1000, 35).unwrap().reduce() {
            Ok(f) => assert_eq!(format!("{}", f), "322818021289.917154"),
            Err(e) => panic!("Expected success, not {}", e),
        };
        match &ZFuel::from(fuel::MAXVALUE) / Fraction::new(1000, 35).unwrap().reduce() {
            Ok(f) => assert_eq!(format!("{}", f), "322818021289.917154"),
            Err(e) => panic!("Expected success, not {}", e),
        };
        match ZFuel::from(fuel::MAXVALUE) / &Fraction::new(1000, 35).unwrap().reduce() {
            Ok(f) => assert_eq!(format!("{}", f), "322818021289.917154"),
            Err(e) => panic!("Expected success, not {}", e),
        };
        match &ZFuel::from(fuel::MAXVALUE) / &Fraction::new(1000, 35).unwrap().reduce() {
            Ok(ref f) => assert_eq!(format!("{}", f), "322818021289.917154"),
            Err(e) => panic!("Expected success, not {}", e),
        };

        // Try in-place multiply; only works with mut Result<Fuel,...>, because result could be erroneous
        let mut feeamt: FuelResult = Ok(ZFuel::from(fuel::MAXVALUE));
        feeamt *= feepct;
        match &feeamt {
            Ok(ref f) => assert_eq!(format!("{}", f), "322818021289.917154"), // Precise multiplication with rounding up
            Err(e) => panic!("Expected success, not {}", e),
        };

        // Force Fuel * Fraction overflow
        assert_eq!(
            format!(
                "{}",
                (ZFuel::new(100, p!(6)).unwrap() * Fraction::new(fuel::MAXVALUE, 2).unwrap())
                    .unwrap_err()
            ),
            "Fuel overflow in ♓0.0001 * 9223372036854775807/2"
        );
    }
    #[test]
    fn test_display_format_properties() {
        // Property: Display format should be parseable back to equivalent value
        let test_cases = [
            ZFuel::new(0, p!(0)).unwrap(),
            ZFuel::new(123, p!(0)).unwrap(),
            ZFuel::new(1230, p!(1)).unwrap(),
            ZFuel::new(12300, p!(2)).unwrap(),
            ZFuel::new(123000, p!(3)).unwrap(),
        ];

        for original in test_cases.iter() {
            let display_str = format!("{}", original);
            let parsed = ZFuel::from_str(&display_str).unwrap();

            // The parsed value should display the same way
            let display_parsed = format!("{}", parsed);
            assert_eq!(display_str, display_parsed);
        }
    }

    // ============================================================
    // Production hardening: parsing, validation, helpers, properties
    // ============================================================

    // ---- u64_to_i64 ----

    #[test]
    fn u64_to_i64_positive_within_range() {
        assert_eq!(u64_to_i64(false, 100, 50, fuel::MAXRANGE).unwrap(), 150);
        assert_eq!(u64_to_i64(false, 0, 0, fuel::MAXRANGE).unwrap(), 0);
        assert_eq!(
            u64_to_i64(false, fuel::MAXRANGE, 0, fuel::MAXRANGE).unwrap(),
            fuel::MAXVALUE
        );
    }

    #[test]
    fn u64_to_i64_negative_within_range() {
        assert_eq!(u64_to_i64(true, 100, 50, fuel::MINRANGE).unwrap(), -150);
        assert_eq!(
            u64_to_i64(true, fuel::MINRANGE, 0, fuel::MINRANGE).unwrap(),
            fuel::MINVALUE
        );
    }

    #[test]
    fn u64_to_i64_rejects_overflow_on_mantissa_plus_fraction() {
        // mantissa.checked_add(fraction) -> None
        let result = u64_to_i64(false, u64::MAX, 1, fuel::MAXRANGE);
        assert!(matches!(result, Err(crate::error::ZFuelError::Range(_))));
    }

    #[test]
    fn u64_to_i64_rejects_value_exceeding_range() {
        assert!(u64_to_i64(false, fuel::MAXRANGE + 1, 0, fuel::MAXRANGE).is_err());
        // Negative overflow: u_units > MINRANGE
        assert!(u64_to_i64(true, fuel::MINRANGE + 1, 0, fuel::MINRANGE).is_err());
    }

    // ---- scale_units ----

    #[test]
    fn scale_units_same_precision_is_identity() {
        for v in &[0i64, 1, -1, 12345, -12345, i64::MAX, i64::MIN] {
            for p in 0..=6u8 {
                let pp = Precision::new(p).unwrap();
                assert_eq!(ZFuel::scale_units(*v, pp, pp).unwrap(), *v);
            }
        }
    }

    #[test]
    fn scale_units_up_multiplies_by_power_of_ten() {
        // 5 at precision 2 (== 0.05) -> precision 6 (== 0.050000) -> 50000
        assert_eq!(ZFuel::scale_units(5, p!(2), p!(6)).unwrap(), 50_000);
        // 0 always scales to 0
        assert_eq!(ZFuel::scale_units(0, p!(0), p!(6)).unwrap(), 0);
        // Negative values too
        assert_eq!(ZFuel::scale_units(-5, p!(2), p!(6)).unwrap(), -50_000);
    }

    #[test]
    fn scale_units_down_truncates_toward_zero() {
        // i64 integer division truncates toward zero
        assert_eq!(ZFuel::scale_units(12_345_678, p!(6), p!(2)).unwrap(), 1234);
        assert_eq!(
            ZFuel::scale_units(-12_345_678, p!(6), p!(2)).unwrap(),
            -1234
        );
    }

    #[test]
    fn scale_units_up_detects_overflow() {
        // i64::MAX cannot be scaled up
        let r = ZFuel::scale_units(i64::MAX, p!(0), p!(6));
        assert!(r.is_err());
        let r = ZFuel::scale_units(i64::MIN, p!(0), p!(6));
        assert!(r.is_err());
    }

    // ---- detect_precision_from_string ----

    #[test]
    fn detect_precision_for_integer() {
        assert_eq!(ZFuel::detect_precision_from_string("123").value(), 0);
        assert_eq!(ZFuel::detect_precision_from_string("-123").value(), 0);
        assert_eq!(ZFuel::detect_precision_from_string("0").value(), 0);
    }

    #[test]
    fn detect_precision_for_decimal() {
        assert_eq!(ZFuel::detect_precision_from_string("1.5").value(), 1);
        assert_eq!(ZFuel::detect_precision_from_string("1.50").value(), 2);
        assert_eq!(ZFuel::detect_precision_from_string("1.500").value(), 3);
        assert_eq!(ZFuel::detect_precision_from_string("0.000001").value(), 6);
    }

    #[test]
    fn detect_precision_caps_at_max() {
        // More than 6 fractional digits should cap at MAX (6)
        assert_eq!(ZFuel::detect_precision_from_string("1.1234567").value(), 6);
        assert_eq!(
            ZFuel::detect_precision_from_string("1.123456789012").value(),
            6
        );
    }

    #[test]
    fn detect_precision_does_not_wrap_on_very_long_fractions() {
        // Regression guard: ensure casting from usize to u8 does not wrap to 0
        // when fractional part length is a multiple of 256.
        let long_frac: String = "1.".to_string() + &"1".repeat(256);
        assert_eq!(
            ZFuel::detect_precision_from_string(&long_frac).value(),
            6,
            "256-char fraction must clamp at MAX (6), not wrap to 0"
        );
        let very_long: String = "1.".to_string() + &"5".repeat(1024);
        assert_eq!(ZFuel::detect_precision_from_string(&very_long).value(), 6);
    }

    #[test]
    fn detect_precision_for_hex_uses_default() {
        assert_eq!(
            ZFuel::detect_precision_from_string("0xff"),
            Precision::DEFAULT
        );
        assert_eq!(
            ZFuel::detect_precision_from_string("-0xff"),
            Precision::DEFAULT
        );
    }

    // ---- ZFuel::check ----

    #[test]
    fn check_accepts_valid_positive_decimal() {
        assert!(ZFuel::check("1.5").unwrap());
        assert!(ZFuel::check("123").unwrap());
        assert!(ZFuel::check("0").unwrap());
        assert!(ZFuel::check("+1.5").unwrap());
    }

    #[test]
    fn check_rejects_negative_amounts() {
        let err = ZFuel::check("-1").unwrap_err();
        assert!(format!("{}", err).contains("Invalid negative amount"));

        let err = ZFuel::check("-1.5").unwrap_err();
        assert!(format!("{}", err).contains("Invalid negative amount"));
    }

    #[test]
    fn check_rejects_garbage_input() {
        assert!(ZFuel::check("abc").is_err());
        assert!(ZFuel::check("1.2.3").is_err());
        assert!(ZFuel::check("").is_err());
    }

    #[test]
    fn check_accepts_underscores_as_separators() {
        assert!(ZFuel::check("1_000").unwrap());
        assert!(ZFuel::check("1_000_000.5").unwrap());
    }

    #[test]
    fn check_accepts_hex() {
        // Hex with valid hex digits a-f must be accepted, mirroring from_str
        assert!(
            ZFuel::check("0xff").unwrap(),
            "check(\"0xff\") must accept hexadecimal digits a-f"
        );
        assert!(ZFuel::check("0x123").unwrap());
        assert!(ZFuel::check("0xabcdef").unwrap());
        // The negative form is rejected by check because of the leading sign
        assert!(ZFuel::check("-0xff").is_err());
    }

    // ---- FromStr edge cases ----

    #[test]
    fn from_str_accepts_whitespace_around_value() {
        let f = ZFuel::from_str(" 1.5 ").unwrap();
        assert_eq!(format!("{}", f), "1.5");

        let f = ZFuel::from_str("\t-1.5\t").unwrap();
        assert_eq!(format!("{}", f), "-1.5");
    }

    #[test]
    fn from_str_handles_explicit_plus_sign() {
        let f = ZFuel::from_str("+1.5").unwrap();
        assert_eq!(format!("{}", f), "1.5");
    }

    #[test]
    fn from_str_handles_empty_mantissa() {
        // ".5" should parse as 0.5
        let f = ZFuel::from_str(".5").unwrap();
        assert_eq!(format!("{}", f), "0.5");
    }

    #[test]
    fn from_str_handles_trailing_dot() {
        // "1." should parse as 1 (precision 0)
        let f = ZFuel::from_str("1.").unwrap();
        assert_eq!(format!("{}", f), "1");
    }

    #[test]
    fn from_str_accepts_h_prefix() {
        let f = ZFuel::from_str("H1.5").unwrap();
        // H prefix forces DEFAULT (6) precision per current implementation
        assert_eq!(f.precision, Precision::DEFAULT);
        assert_eq!(f.units, 1_500_000);
    }

    #[test]
    fn from_str_accepts_unicode_pisces_prefix() {
        let f = ZFuel::from_str("♓1.5").unwrap();
        assert_eq!(f.precision, Precision::DEFAULT);
        assert_eq!(f.units, 1_500_000);
    }

    #[test]
    fn from_str_rejects_empty_string() {
        assert!(ZFuel::from_str("").is_err());
    }

    #[test]
    fn from_str_rejects_whitespace_only() {
        assert!(ZFuel::from_str("   ").is_err());
    }

    #[test]
    fn from_str_rejects_sign_only() {
        assert!(ZFuel::from_str("+").is_err());
        assert!(ZFuel::from_str("-").is_err());
    }

    #[test]
    fn from_str_rejects_non_numeric() {
        assert!(ZFuel::from_str("abc").is_err());
        assert!(ZFuel::from_str("1.2.3").is_err());
        assert!(ZFuel::from_str("1e10").is_err()); // no scientific notation
        assert!(ZFuel::from_str("1,000").is_err()); // no thousands separators (other than _)
    }

    #[test]
    fn from_str_accepts_underscores_as_separators() {
        // Consistency with check(): both should accept underscore-separated digits
        let f = ZFuel::from_str("1_000").unwrap();
        assert_eq!(format!("{}", f), "1000");

        let f = ZFuel::from_str("1_000_000.5").unwrap();
        assert_eq!(format!("{}", f), "1000000.5");
    }

    #[test]
    fn from_str_rejects_value_exceeding_max_range() {
        // MAXRANGE + 1 in units terms
        assert!(ZFuel::from_str("9223372036854.775808").is_err());
        // MINRANGE underflow
        assert!(ZFuel::from_str("-9223372036854.775809").is_err());
    }

    #[test]
    fn from_str_accepts_max_value_at_precision_0() {
        // Largest legal integer at precision 0 is MAXVALUE / 10^6 == 9_223_372_036_854.
        let f = ZFuel::from_str("9223372036854").unwrap();
        assert_eq!(f.units, 9_223_372_036_854);
        assert_eq!(f.precision.value(), 0);

        let f = ZFuel::from_str("-9223372036854").unwrap();
        assert_eq!(f.units, -9_223_372_036_854);
        assert_eq!(f.precision.value(), 0);
    }

    #[test]
    fn from_str_rejects_values_exceeding_max_at_precision_0() {
        // Bound is ZFuel::max_units_at(p=0); anything above must fail. Note: the same digit
        // string at precision 6 *is* a valid input ("9223372036854.775807"), so this rejection
        // is specifically about exceeding the ZFuel value space at precision 0.
        assert!(ZFuel::from_str("9223372036854775807").is_err());
        assert!(ZFuel::from_str("-9223372036854775808").is_err());

        // Just past the precision-0 cap.
        assert!(ZFuel::from_str("9223372036855").is_err());
        assert!(ZFuel::from_str("-9223372036855").is_err());
    }

    #[test]
    fn from_str_rejects_more_than_intlimit_digits() {
        // 14-digit integer exceeds INTLIMIT=13 (regex rejection).
        assert!(ZFuel::from_str("12345678901234").is_err());
        // 20-digit integer is also rejected, of course.
        assert!(ZFuel::from_str("12345678901234567890").is_err());
    }

    #[test]
    fn from_str_truncates_excessive_fractional_digits() {
        // Anything past EXPONENT (6) is silently dropped at the value level
        let f = ZFuel::from_str("1.123456789").unwrap();
        // Precision is capped at 6
        assert_eq!(f.precision, Precision::DEFAULT);
        assert_eq!(f.units, 1_123_456);
    }

    #[test]
    fn from_str_preserves_value_across_long_fraction_inputs() {
        // Regression guard: a fractional string of length 256 must not be misinterpreted
        // as precision 0 (which would scale the parsed units down by 1,000,000).
        let s = "1.".to_string() + &"0".repeat(256);
        let f = ZFuel::from_str(&s).unwrap();
        // 256 trailing zeros: equivalent to "1.0", value 1, precision capped to 6
        assert_eq!(format!("{}", f), "1");

        let s = "0.".to_string() + &"0".repeat(254) + "12";
        let f = ZFuel::from_str(&s).unwrap();
        // Effective value beyond EXPONENT (6) is truncated to zero
        assert_eq!(format!("{}", f), "0");
    }

    #[test]
    fn from_str_hex_basic() {
        let f = ZFuel::from_str("0xff").unwrap();
        assert_eq!(f.units, 0xff);
        assert_eq!(f.precision, Precision::DEFAULT);
    }

    #[test]
    fn from_str_hex_rejects_too_many_digits() {
        // HEXLIMIT is 16
        assert!(ZFuel::from_str("0x10000000000000000").is_err());
    }

    #[test]
    fn from_str_hex_rejects_positive_overflow() {
        // 0x8000000000000000 == MAXRANGE + 1 (as u64), would exceed MAXVALUE for positive
        assert!(ZFuel::from_str("0x8000000000000000").is_err());
        // But the negative form is exactly MINVALUE
        let f = ZFuel::from_str("-0x8000000000000000").unwrap();
        assert_eq!(f.units, fuel::MINVALUE);
    }

    // ---- Display / FromStr roundtrip ----

    #[test]
    fn display_then_parse_roundtrip_preserves_value() {
        let cases = [
            ZFuel::new(0, p!(0)).unwrap(),
            ZFuel::new(1, p!(0)).unwrap(),
            ZFuel::new(-1, p!(0)).unwrap(),
            ZFuel::new(12345, p!(2)).unwrap(),
            ZFuel::new(-12345, p!(2)).unwrap(),
            ZFuel::new(1_000_000, p!(6)).unwrap(),
            ZFuel::new(fuel::MAXVALUE, p!(6)).unwrap(),
            ZFuel::new(fuel::MINVALUE, p!(6)).unwrap(),
        ];
        for original in cases.iter() {
            let s = format!("{}", original);
            let parsed = ZFuel::from_str(&s)
                .unwrap_or_else(|e| panic!("roundtrip failed for {:?}: {}", original, e));
            // Compared by value (which is precision-aware)
            assert_eq!(
                parsed, *original,
                "roundtrip differs for {:?} -> {:?}",
                original, parsed
            );
        }
    }

    // ---- Serde JSON roundtrip ----

    #[test]
    fn serde_json_roundtrip_preserves_value() {
        let cases = [
            ZFuel::new(0, p!(0)).unwrap(),
            ZFuel::new(123, p!(0)).unwrap(),
            ZFuel::new(12345, p!(2)).unwrap(),
            ZFuel::new(-12345, p!(2)).unwrap(),
            ZFuel::new(1_500_000, p!(6)).unwrap(),
            ZFuel::new(-1_500_000, p!(6)).unwrap(),
        ];
        for original in cases.iter() {
            let json = serde_json::to_string(original).expect("serialize");
            // Serializes as a JSON string
            assert!(json.starts_with('\"') && json.ends_with('\"'));
            let decoded: ZFuel = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(decoded, *original);
        }
    }

    #[test]
    fn serde_deserialize_rejects_garbage() {
        let r: Result<ZFuel, _> = serde_json::from_str("\"not a number\"");
        assert!(r.is_err());
    }

    #[test]
    fn serde_deserialize_rejects_non_string_types() {
        let r: Result<ZFuel, _> = serde_json::from_str("123");
        assert!(r.is_err());
    }

    // ---- Algebraic invariants ----

    #[test]
    fn addition_with_zero_is_identity() {
        for &(units, prec) in &[
            (0i64, p!(0)),
            (1, p!(0)),
            (12345, p!(2)),
            (-12345, p!(3)),
            (1_000_000, p!(6)),
        ] {
            let a = ZFuel::new(units, prec).unwrap();
            let zero = ZFuel::zero_precision(prec);
            let r = (a + zero).unwrap();
            assert_eq!(r.units, a.units);
            assert_eq!(r.precision, a.precision);
        }
    }

    #[test]
    fn addition_is_commutative_within_range() {
        let cases = [
            (1i64, 2i64),
            (-5, 7),
            (12345, -67890),
            (i64::MAX / 2, i64::MAX / 4),
            (i64::MIN / 2, 0),
        ];
        for &(x, y) in cases.iter() {
            let a = ZFuel::new(x, p!(6)).unwrap();
            let b = ZFuel::new(y, p!(6)).unwrap();
            let ab = (a + b).expect("a+b must not overflow for these test inputs");
            let ba = (b + a).expect("b+a must not overflow for these test inputs");
            assert_eq!(ab.units, ba.units);
        }
    }

    #[test]
    fn subtraction_is_additive_inverse_within_range() {
        // (a + b) - b == a for non-overflowing inputs
        let cases = [(1i64, 2i64), (-5, 7), (12345, -67890)];
        for &(x, y) in cases.iter() {
            let a = ZFuel::new(x, p!(6)).unwrap();
            let b = ZFuel::new(y, p!(6)).unwrap();
            let sum = (a + b).unwrap();
            let back = (sum - b).unwrap();
            assert_eq!(back.units, a.units);
        }
    }

    #[test]
    fn double_negation_is_identity_for_non_minvalue() {
        for &v in &[0i64, 1, -1, 12345, -12345, fuel::MAXVALUE] {
            let a = ZFuel::new(v, p!(6)).unwrap();
            let neg = (-a).unwrap();
            let back = (-neg).unwrap();
            assert_eq!(back.units, a.units);
        }
    }

    #[test]
    fn negate_minvalue_returns_overflow_error() {
        let a = ZFuel::new(fuel::MINVALUE, p!(6)).unwrap();
        let r = -a;
        assert!(r.is_err());
    }

    #[test]
    fn ordering_is_transitive_within_same_precision() {
        // Build a sorted list and verify total order properties
        let vals: Vec<ZFuel> = [-3i64, -1, 0, 1, 2, 7, 100]
            .iter()
            .map(|v| ZFuel::new(*v, p!(6)).unwrap())
            .collect();
        for window in vals.windows(3) {
            let (a, b, c) = (window[0], window[1], window[2]);
            assert!(a < b);
            assert!(b < c);
            assert!(
                a < c,
                "transitivity broken: {} < {} < {} but !({} < {})",
                a,
                b,
                c,
                a,
                c
            );
        }
    }

    #[test]
    fn ordering_matches_value_across_precisions() {
        // Same nominal value at different precisions: comparison is value-based
        let a = ZFuel::new(1, p!(0)).unwrap(); // 1
        let b = ZFuel::new(1_000_000, p!(6)).unwrap(); // 1.000000
        assert_eq!(a.cmp(&b), std::cmp::Ordering::Equal);
        assert_eq!(a, b);

        let smaller = ZFuel::new(999_999, p!(6)).unwrap(); // 0.999999
        assert!(smaller < a);
        assert!(a > smaller);
    }

    #[test]
    fn from_i64_uses_default_precision() {
        let f: ZFuel = 12345i64.into();
        assert_eq!(f.precision, Precision::DEFAULT);
        assert_eq!(f.units, 12345);
    }

    #[test]
    fn zfuel_constructors_set_expected_fields() {
        let f = ZFuel::new_with_default_precision(42);
        assert_eq!(f.units, 42);
        assert_eq!(f.precision, Precision::DEFAULT);

        let z = ZFuel::zero();
        assert_eq!(z.units, 0);
        assert_eq!(z.precision, Precision::DEFAULT);

        let z = ZFuel::zero_precision(p!(2));
        assert_eq!(z.units, 0);
        assert_eq!(z.precision, p!(2));
    }

    #[test]
    fn multiplication_by_one_over_one_is_identity_value() {
        let one = crate::fraction::Fraction::new(1, 1).unwrap();
        for &v in &[0i64, 1, -1, 12345, -12345] {
            let a = ZFuel::new(v, p!(6)).unwrap();
            let r = (a * one).unwrap();
            // Multiplication always produces precision DEFAULT (6); value preserved
            assert_eq!(r.units, v);
            assert_eq!(r.precision, Precision::DEFAULT);
        }
    }

    #[test]
    fn multiplication_by_zero_fraction_is_zero() {
        let zero_frac = crate::fraction::Fraction::new(0, 5).unwrap();
        let a = ZFuel::new(12345, p!(6)).unwrap();
        let r = (a * zero_frac).unwrap();
        assert_eq!(r.units, 0);
        assert_eq!(r.precision, Precision::DEFAULT);
    }

    #[test]
    fn display_handles_i64_min_at_default_precision() {
        // Regression: at default precision the integer "whole" component equals i64::MIN, and
        // the old `whole.abs()` implementation panicked on overflow. `unsigned_abs()` must be
        // used. With the bounded value-space invariant, MINVALUE is only constructible at
        // Precision::DEFAULT — but the Display fix remains defense-in-depth.
        let f = ZFuel::new(i64::MIN, Precision::DEFAULT).unwrap();
        let _ = format!("{}", f); // must not panic
        let _ = format!("{:?}", f);
    }

    #[test]
    fn display_then_parse_roundtrip_for_minvalue_at_default_precision() {
        // Display + FromStr must round-trip MINVALUE at the only precision where it is legal.
        let original = ZFuel::new(i64::MIN, Precision::DEFAULT).unwrap();
        let rendered = format!("{}", original);
        let parsed = ZFuel::from_str(&rendered)
            .unwrap_or_else(|e| panic!("MINVALUE roundtrip failed: {}", e));
        assert_eq!(parsed, original, "MINVALUE roundtrip mismatch");
    }

    #[test]
    fn debug_format_includes_value_and_precision() {
        let f = ZFuel::new(123, p!(2)).unwrap();
        let dbg = format!("{:?}", f);
        assert!(dbg.contains("1.23"));
        assert!(dbg.contains("precision(2)"));
    }

    // ============================================================
    // Value-space invariant tests
    //
    // These tests codify the contract enforced by the fallible `ZFuel::new`:
    // a ZFuel represents a value in the fixed range ±MAXVALUE / 10^6 ≈ ±9.223 trillion,
    // and `precision` selects how to *represent* that value (0–6 decimal digits),
    // not how *much* value can be stored.
    // ============================================================

    /// Convenience: the per-precision positive cap, as a signed `i64` (always non-negative).
    fn max_at(p: u8) -> i64 {
        ZFuel::max_units_at(Precision::new(p).unwrap()) as i64
    }

    #[test]
    fn new_accepts_zero_at_every_precision() {
        for p in 0..=6u8 {
            let prec = Precision::new(p).unwrap();
            assert!(
                ZFuel::new(0, prec).is_ok(),
                "0 must be legal at precision {}",
                p
            );
        }
    }

    #[test]
    fn new_accepts_max_units_at_each_precision() {
        for p in 0..=6u8 {
            let prec = Precision::new(p).unwrap();
            let cap = max_at(p);
            let f = ZFuel::new(cap, prec)
                .unwrap_or_else(|_| panic!("max_units_at({}) must be legal", p));
            assert_eq!(f.units, cap);
            assert_eq!(f.precision, prec);
        }
    }

    #[test]
    fn new_accepts_min_units_at_each_precision() {
        // At p < 6, |min| == |max| (the asymmetry of i64 is absorbed by the /10^k division).
        for p in 0..6u8 {
            let prec = Precision::new(p).unwrap();
            let cap = max_at(p);
            assert!(
                ZFuel::new(-cap, prec).is_ok(),
                "-cap must be legal at p={}",
                p
            );
        }
        // At p == 6, MINVALUE itself is legal (the only place where |min| > |max|).
        let f = ZFuel::new(fuel::MINVALUE, Precision::DEFAULT).unwrap();
        assert_eq!(f.units, fuel::MINVALUE);
    }

    #[test]
    fn new_rejects_one_past_max_at_low_precision() {
        for p in 0..6u8 {
            let prec = Precision::new(p).unwrap();
            let cap = max_at(p);
            assert!(
                ZFuel::new(cap + 1, prec).is_err(),
                "cap+1 must be rejected at p={}",
                p
            );
        }
    }

    #[test]
    fn new_rejects_one_past_min_at_low_precision() {
        for p in 0..6u8 {
            let prec = Precision::new(p).unwrap();
            let cap = max_at(p);
            assert!(
                ZFuel::new(-cap - 1, prec).is_err(),
                "-cap-1 must be rejected at p={}",
                p
            );
        }
    }

    #[test]
    fn new_rejects_i64_max_min_at_low_precision() {
        for p in 0..6u8 {
            let prec = Precision::new(p).unwrap();
            assert!(
                ZFuel::new(i64::MAX, prec).is_err(),
                "i64::MAX must be rejected at p={}",
                p
            );
            assert!(
                ZFuel::new(i64::MIN, prec).is_err(),
                "i64::MIN must be rejected at p={}",
                p
            );
        }
    }

    #[test]
    fn new_error_message_includes_precision_and_max() {
        let err = ZFuel::new(i64::MAX, Precision::new(0).unwrap()).unwrap_err();
        let msg = format!("{}", err);
        // Loose contract: the message names the precision and a cap. Don't pin exact text.
        assert!(
            msg.contains("precision"),
            "error message must mention precision; got {}",
            msg
        );
        assert!(
            msg.contains("cap") || msg.contains("max") || msg.contains("range"),
            "error message must describe the cap; got {}",
            msg
        );
    }

    #[test]
    fn scale_to_default_never_overflows_for_legal_values() {
        // For every legal ZFuel, scaling to Precision::DEFAULT must be a total operation.
        for p in 0..=6u8 {
            let prec = Precision::new(p).unwrap();
            let cap = max_at(p);
            // Representative sample: zero, ±cap, ±cap/2, ±1, ±42.
            let samples: [i64; 9] = [0, cap, -cap, cap / 2, -cap / 2, 1, -1, 42, -42];
            for &u in samples.iter() {
                if ZFuel::new(u, prec).is_ok() {
                    assert!(
                        ZFuel::scale_units(u, prec, Precision::DEFAULT).is_ok(),
                        "scale_units({}, p{}, DEFAULT) must succeed for legal values",
                        u,
                        p
                    );
                }
            }
            // MINVALUE at DEFAULT is special-cased and must also scale (no-op at DEFAULT).
            if prec == Precision::DEFAULT {
                assert!(ZFuel::scale_units(fuel::MINVALUE, prec, Precision::DEFAULT).is_ok());
            }
        }
    }

    #[test]
    fn to_precision_up_never_errors_for_legal_values() {
        for p in 0..=6u8 {
            let prec = Precision::new(p).unwrap();
            let cap = max_at(p);
            let samples: [i64; 9] = [0, cap, -cap, cap / 2, -cap / 2, 1, -1, 42, -42];
            for &u in samples.iter() {
                let Ok(z) = ZFuel::new(u, prec) else { continue };
                for target_p in p..=6u8 {
                    let target = Precision::new(target_p).unwrap();
                    assert!(
                        z.to_precision(target).is_ok(),
                        "to_precision: legal value {} at p{} must scale up to p{}",
                        u,
                        p,
                        target_p
                    );
                }
            }
        }
    }

    #[test]
    fn display_integer_part_fits_intlimit_for_every_legal_value() {
        // The integer part of any legal ZFuel's Display fits in INTLIMIT digits.
        // Sample includes zero, ±cap, ±42 at every precision, plus MIN/MAX at DEFAULT.
        for p in 0..=6u8 {
            let prec = Precision::new(p).unwrap();
            let cap = max_at(p);
            let samples: [i64; 5] = [0, cap, -cap, 42, -42];
            for &u in samples.iter() {
                let Ok(z) = ZFuel::new(u, prec) else { continue };
                let s = format!("{}", z);
                let int_part = s
                    .trim_start_matches('-')
                    .split('.')
                    .next()
                    .expect("Display must have an integer component");
                assert!(
                    int_part.len() <= INTLIMIT,
                    "Display integer part {} digits (> INTLIMIT={}) for {} at p{}",
                    int_part.len(),
                    INTLIMIT,
                    s,
                    p
                );
            }
        }
        // MINVALUE at DEFAULT: the integer part is "9223372036854", exactly 13 digits.
        let s = format!(
            "{}",
            ZFuel::new(fuel::MINVALUE, Precision::DEFAULT).unwrap()
        );
        let int_part = s
            .trim_start_matches('-')
            .split('.')
            .next()
            .expect("must have integer part");
        assert!(int_part.len() <= INTLIMIT);
    }

    #[test]
    fn mixed_precision_add_succeeds_when_mathematical_sum_fits_default() {
        // Pairs the invariant guarantees `a + b` is a total operation against panics: it
        // may still return `Err(Range)` when the mathematical sum would exceed MAXVALUE at
        // precision 6. We verify both directions.

        // Case 1: sum fits.
        let a = ZFuel::new(1_000, p!(0)).unwrap(); // 1000 (== 1_000_000_000 at p=6)
        let b = ZFuel::new(2_500_000, p!(6)).unwrap(); // 2.5 (== 2_500_000 at p=6)
        let sum = (a + b).expect("1000 + 2.5 must fit");
        // Result is reported at the higher precision (6).
        assert_eq!(sum.precision, Precision::DEFAULT);
        assert_eq!(sum.units, 1_000_000_000 + 2_500_000);

        // Case 2: very-near-cap at p=0 plus a tiny value at p=6 still fits.
        let large_p0 = ZFuel::new(max_at(0) - 1, p!(0)).unwrap(); // just below cap
        let tiny_p6 = ZFuel::new(1, p!(6)).unwrap();
        assert!(
            (large_p0 + tiny_p6).is_ok(),
            "near-cap p0 + tiny p6 must fit"
        );

        // Case 3: cap + cap at the same low precision overflows the value space → clean Err.
        let cap_p0 = ZFuel::new(max_at(0), p!(0)).unwrap();
        let result = cap_p0 + cap_p0;
        assert!(result.is_err(), "cap + cap must report Err, not panic");

        // Case 4: largest legal at p=6 plus 1 unit at p=6 overflows → clean Err.
        let max_p6 = ZFuel::new(fuel::MAXVALUE, p!(6)).unwrap();
        let one_p6 = ZFuel::new(1, p!(6)).unwrap();
        assert!((max_p6 + one_p6).is_err());

        // Subtraction below MINVALUE also reports cleanly.
        let min_p6 = ZFuel::new(fuel::MINVALUE, p!(6)).unwrap();
        assert!((min_p6 - one_p6).is_err());
    }

    #[test]
    fn cross_precision_partial_cmp_is_total_for_legal_values() {
        // For every legal (a, b), partial_cmp must be Some(...) and consistent with the
        // mathematical comparison done by scaling both to precision 6 (which is always safe
        // under the invariant).
        for pa in 0..=6u8 {
            for pb in 0..=6u8 {
                let prec_a = Precision::new(pa).unwrap();
                let prec_b = Precision::new(pb).unwrap();
                let cap_a = max_at(pa);
                let cap_b = max_at(pb);
                let samples_a = [0i64, 1, -1, cap_a, -cap_a, cap_a / 3];
                let samples_b = [0i64, 1, -1, cap_b, -cap_b, cap_b / 3];
                for &ua in samples_a.iter() {
                    for &ub in samples_b.iter() {
                        let Ok(a) = ZFuel::new(ua, prec_a) else {
                            continue;
                        };
                        let Ok(b) = ZFuel::new(ub, prec_b) else {
                            continue;
                        };
                        let cmp = a.partial_cmp(&b);
                        assert!(
                            cmp.is_some(),
                            "partial_cmp must be Some for legal ({},p{}) vs ({},p{})",
                            ua,
                            pa,
                            ub,
                            pb
                        );
                        // Re-derive the expected order by scaling both to precision 6.
                        let a6 = ZFuel::scale_units(ua, prec_a, Precision::DEFAULT).unwrap();
                        let b6 = ZFuel::scale_units(ub, prec_b, Precision::DEFAULT).unwrap();
                        assert_eq!(
                            cmp.unwrap(),
                            a6.cmp(&b6),
                            "cross-precision order mismatch for ({},p{}) vs ({},p{})",
                            ua,
                            pa,
                            ub,
                            pb
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn from_str_post_condition_units_are_legal_for_their_precision() {
        // Every successfully parsed string yields a ZFuel that satisfies the invariant.
        let inputs = [
            "0",
            "0.0",
            "42",
            "-42",
            "1.5",
            "9223372036854",
            "-9223372036854",
            "9223372036854.775807",
            "-9223372036854.775808",
            "0x7fffffffffffffff",
            "-0x8000000000000000",
            "123.456",
            "0.000001",
        ];
        for s in inputs.iter() {
            let z = ZFuel::from_str(s).unwrap_or_else(|e| panic!("{} should parse, got {}", s, e));
            assert!(
                ZFuel::new(z.units, z.precision).is_ok(),
                "from_str({}) produced an out-of-range ZFuel: units={}, precision={}",
                s,
                z.units,
                z.precision.value()
            );
        }
    }
}
