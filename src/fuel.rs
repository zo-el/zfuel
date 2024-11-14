//! The ZFuel ZFuel type and math functions, and JSON serialization support.  Supports Fraction
//! type for computing fractional ZFuel amounts using rational numbers; useful for expressing
//! "percentages" of ZFuel amounts without losing (too much) precision, while retaining the
//! ability to compute ZFuel transaction fees on the largest possible transaction amounts.

use crate::error::ZFuelError;
use crate::fraction::Fraction;
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{char, digit1, space0},
    combinator::{map_res, opt},
    sequence::preceded,
    Err, IResult,
};
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use std::str::FromStr;
use std::{
    cmp::Ordering,
    fmt,
    ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Sub, SubAssign},
    result,
};
///
/// ZFuel -- Account for ZFuel, in fractions of 1/10^18 ( 1/1,000,000th of a unit)
///
/// Ensures that the integer amount never leaves Rust / Web Assembly.  For example, if the i128 value
/// was processed in Javascript, it must not exceed a +/- value that would fit into an IEEE 754
/// double-precision floating point value without loss of precision.  Thus, the no value exceeding
/// +/- 2^53-1 fractional units of ZFuel should be converted into an f64.
///
/// This ZFuel struct is what ensures that we do not pass numeric ZFuel amounts through the WASM
/// boundary.  All precise ZFuel values, such as 2,882,343,476 x 1/1e6 units of ZFuel are
/// represented as Display 'fmt()' values (eg. "2882.343467" ZFuel).  The Display value is precisely
/// convertible back and forth into the internal integer representation without loss of precision,
/// and is also a human-readable fractional amount of ZFuel, it is also the preferred external
/// representation.
///
/// Javascript (and other languages that use IEEE 754 floats to represent integer values) cannot be
/// allowed to compute numeric values that will exceed 2^53-1 (9.0072e15); the capacity of IEEE 754
/// mantissa w/o loss of numerical accuracy, for those platforms that emulate i128 using IEEE 754
/// double-precision floating point.  Allowing 15 total decimal digits in 7 integer and 8 fractional
/// digits (+/-1e15), and 13 hex digits (+/-4.5e15) is safely within this range.  However, we would
/// give up some possibly useful capacity.
///
/// The available range in [0,2^53), with 8 decimal digits after the decimal point, is about 7.95
/// digits: log( 2**53 / 10 ** 8, 10 ) == 7.9545.  So, we would allow up to 8 integer digits, and
/// manually check for precision overflow by comparing against 2**53, and rejecting any value that
/// exceeds the maximum 9.0071e15).  Likewise, we accept 14 hex digits, and check the full precision
/// limits manually.  This would allow only ZFuel account and transaction values up to about
/// 90,071,992 ZFuel; insufficient (there are 177B HOT issued already, so the Holo
/// infrastructure account will be in a debit condition beyond this value).
///
/// With 18 decimal digits of fractional precision (a minimum transaction of 1/1,000,000 of a
/// ZFuel), the range is log( 2**53 / 10 ** 18, 10 ) == 9.9545 digits of ZFuel; almost 10
/// digits of precision, with a max capacity of about 9,007,199,254 ZFuel; still insufficient to
/// represent the debit balance of the Holo organization which issued the HOT.
///
/// Therefore, we allow the full range of i128 values for ZFuel.units -- and disallow/discourage
/// calculation on ZFuel values in Javascript code; unless you use Big values, you *will* (very, very
/// probably) do it wrong, and lose precision with large ZFuel values.
///
/// By allowing the full i128 range for ZFuel units (1/10^18 of a ZFuel), we achieve a maximum
/// range of +/- of log( 2**63 / 10 ** 18 ) == 12.96 digits of ZFuel capacity; about
/// 9,223,372,036,854 (9.223 Trillion) ZFuel account and transaction value capacity; adequate for
/// any single ZFuel account value or Transaction amount.  Any transaction the exceeds these
/// values will fail to complete (as all calculations are strictly bounds-checked).
///
/// The minimum fractional minimum amount of 1/10^18 ZFuel allows for micro-transactions down to
/// 1/1,000,000th (1 millionth) of a ZFuel.  Fee payments lose precision below value of
/// 1/10,000th of a ZFuel; for example, if a micro-transaction of 0.000123 ZFuel is spent, the
/// 1% fee that will be computed and charged could be 0.000001 ZFuel if rounded down, or 0.000002
/// if rounded up.
///
/// Since the system "cost" of extremely tiny transactions is not free, fees on the portion of
/// transactions below the minimum threshold are always rounded up (away from 0).  This doesn't
/// affect the fee calculation of fees on transactions of precision 0.0001 or above (ie. the fee for
/// spending .0021 ZFuel is exactly 0.000021).  However, the fee for spending 0.00213 is computed
/// as 0.000022 (is round up), instead of 0.000021 (normal rounding).  Perhaps surprisingly, the fee
/// to spend 0.000001 ZFuel is 0.000001.  In effect, the fees on extremely tiny transactions
/// increase from 1%, up to 100% fees on the tiniest possible transaction.  This better reflects the
/// actual costs of running the Holo system, and is not an egregious cost; 1,000 such transactions
/// would cost an additional 0.001 ZFuel in fees (vs. fees calculated with infinite precision).
///

// FRACTION -- units of ZFuel are stored to this fixed-point precision.  These must
// be consistent with each-other.  Values after the decimal point are truncated to the
// EXPONENT number of significant decimal places; the remainder are ignored.
pub const EXPONENT: usize = 18; // Up to 18 digits after decimal (>18 truncated)
pub const DENOMINATOR: i64 = 1_000_000_000_000_000_000; // eg. 10 ^ EXPONENT

pub const INTLIMIT: usize = 18; // Up to 18 digits before decimal (~18.96 accepted)
pub const HEXLIMIT: usize = 36; // Up to 36 hex digits (full 128-bit signed twos-complement integer)

// These {MIN,MAX}{VALUE,RANGE} values are *carefully* chosen to avoid the possibility of
// over/underflow at the limits of u128/i128 interactions in ZFuel calculations.  Do not consider
// changing without carefully considering/testing the effects at the limits of possible value.
pub const MAXVALUE: i128 = i128::MAX; // 748288838313422294120286634350736906063837462003712;
pub const MAXRANGE: u128 = MAXVALUE as u128;

pub const MINVALUE: i128 = -MAXVALUE - 1; // == i128::min_value();
pub const MINRANGE: u128 = MAXRANGE + 1;

// DECSHOWN -- default number of decimal places desired after '.' in Display values
pub const DECSHOWN: usize = 1; // could be 1-EXPONENT

#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq)] // Copy req'd for binary op implementations
/// ZFuel, in 1/DENOMINATOR units

pub struct ZFuel {
    pub units: i128,
}

/// fuel::ZFuelResult -- a fully defined custom Result type for ZFuel operations
pub type ZFuelResult = result::Result<ZFuel, ZFuelError>;

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
    pub fn new(units: i128) -> Self {
        ZFuel { units }
    }
    pub fn zero() -> Self {
        ZFuel { units: 0 }
    }
    fn parse_hex(input: &str) -> IResult<&str, (u128, u128), nom::error::Error<&str>> {
        map_res(preceded(tag("0x"), digit1), |hex: &str| {
            u128::from_str_radix(hex, 16).map(|val| (val, 0))
        })(input)
    }

    fn parse_decimal(input: &str) -> IResult<&str, (u128, u128)> {
        let (input, int_part) = opt(digit1)(input)?;
        let (input, frac_part) = opt(preceded(char('.'), digit1))(input)?;
        let int_part = int_part.unwrap_or("0");
        let frac_part = frac_part.unwrap_or("0");
        // Check if integer part exceeds the limit
        if int_part.len() > INTLIMIT {
            return Err(Err::Error(nom::error::Error::new(
                input,
                nom::error::ErrorKind::TooLarge,
            )));
        }
        let mantissa = DENOMINATOR as u128
            * int_part.parse::<u128>().map_err(|_| {
                Err::Error(nom::error::Error::new(input, nom::error::ErrorKind::Digit))
            })?;
        let fraction = format!("{:0<exponent$.exponent$}", frac_part, exponent = EXPONENT)
            .parse::<u128>()
            .map_err(|_| Err::Error(nom::error::Error::new(input, nom::error::ErrorKind::Digit)))?;
        Ok((input, (mantissa, fraction)))
    }
    #[allow(clippy::type_complexity)]
    fn parse_fuel(
        input: &str,
    ) -> IResult<&str, (Option<&str>, (u128, u128)), nom::error::Error<&str>> {
        let (input, _) = space0(input)?;
        let (input, sign) = opt(alt((tag("+"), tag("-"))))(input)?;
        let (input, _) = space0(input)?;
        let (input, value) = alt((Self::parse_hex, Self::parse_decimal))(input)?;
        let (input, _) = space0(input)?;
        Ok((input, (sign, value)))
    }

    /// check: This function validates the input string using the parsers. It checks for a negative sign and returns an error if found; otherwise, it returns Ok(true).
    pub fn check(amount: &str) -> Result<bool, ZFuelError> {
        let clean_amount = amount.replace('_', "");

        match Self::parse_fuel(&clean_amount) {
            Ok((_, (sign, (_, _)))) => match sign {
                Some("-") => Err(ZFuelError::Range(format!(
                    "Invalid negative amount {}",
                    amount
                ))),
                _ => Ok(true),
            },
            Err(_) => Err(ZFuelError::Range(format!(
                "Invalid ZFuel amount {}",
                amount
            ))),
        }
    }
}

/// u128_to_i128 -- range-checked, optionally negating mantissa + fraction for ZFuel.units.  Ensures
/// that supplied range (and fuel MIN/MAX-VALUEs are not exceeded).  This is a subtle operation,
/// which requires us to pre-validate absolute (unsigned) mantissa and fractional fuel unit values
/// before any negative sign is applied.
pub fn u128_to_i128(
    negative: bool,
    mantissa: u128,
    fraction: u128,
    range: u128,
) -> Result<i128, ZFuelError> {
    match mantissa.checked_add(fraction) {
        Some(u_units) => {
            if u_units > range {
                Err(ZFuelError::Range(format!(
                    "Exceeded range for ZFuel mantissa {}, fraction {}",
                    mantissa, fraction
                )))
            } else if negative {
                match u_units.cmp(&MINRANGE) {
                    Ordering::Greater => Err(ZFuelError::Range(format!(
                        "Underflow for ZFuel negative mantissa {}, fraction {}",
                        mantissa, fraction
                    ))),
                    Ordering::Less => Ok(-(u_units as i128)),
                    Ordering::Equal => Ok(MINVALUE),
                }
            } else {
                Ok(u_units as i128)
            }
        }
        None => Err(ZFuelError::Range(format!(
            "Overflow for ZFuel mantissa {}, fraction {}",
            mantissa, fraction
        ))),
    }
}

/// ZFuel::from_str -- Covert from &str; Result may yield Err if parsing fails
///
/// Handles hexadecimal and normal whole or fractional amounts of ZFuel, discarding any
/// precision beyond the 8th (EXPONENT) decimal place of fractional precision.  Returns ZFuelError
/// on any parsing or result value max range errors.
///
impl FromStr for ZFuel {
    type Err = ZFuelError;

    fn from_str(amount: &str) -> Result<Self, Self::Err> {
        // Preprocess input to remove underscores
        let clean_amount = amount.replace('_', "");

        match Self::parse_fuel(&clean_amount) {
            Ok((_, (sign, (mantissa, fraction)))) => {
                let units_res = match sign {
                    Some("-") => u128_to_i128(true, mantissa, fraction, MINRANGE),
                    _ => u128_to_i128(false, mantissa, fraction, MAXRANGE),
                };
                match units_res {
                    Ok(units) => Ok(ZFuel { units }),
                    Err(e) => Err(e),
                }
            }
            Err(_) => Err(ZFuelError::Range(format!(
                "Invalid ZFuel amount {}",
                amount
            ))),
        }
    }
}

/// i128 -> ZFuel for all integer types
impl From<i128> for ZFuel {
    fn from(units: i128) -> ZFuel {
        ZFuel { units }
    }
}

/// & mut ZFuel -> ZFuel required for in-place operators
impl From<&mut ZFuel> for ZFuel {
    fn from(other: &mut ZFuel) -> ZFuel {
        ZFuel { units: other.units }
    }
}

impl From<&ZFuel> for Fraction {
    fn from(fuel: &ZFuel) -> Fraction {
        Fraction {
            numerator: fuel.units,
            denominator: DENOMINATOR.into(),
        }
    }
}

///
/// ZFuel amounts in human-readable Display representation
///
/// All integer numeric forms of ZFuel are deemed to be terms if 1/DENOMINATOR units.  Floating
/// point amounts are not acceptable, due to loss of precision.
///
/// All String/&str forms are deemed to be in "whole.fractional" amounts, and are converted to
/// internal 1/DENOMINATOR units.
///
/// If no fractional units are used, then the ZFuel amount is represented as a whole-numbered value;
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
        let whole = self.units / (DENOMINATOR as i128); //            1234098760 / 10^18 == 1234
        let fraction = self.units - whole * (DENOMINATOR as i128); // 1234098760 - 1234 * 10^18 == 98760
                                                                   // fraction must be < DENOMINATOR, and will be +'ve or -'ve (same sign as self.units)
        if fraction == 0 {
            write!(f, "{}{}", sign, whole.abs())
        } else {
            // Any fractional portion is left-padded with '0' out to 8 (EXPONENT) decimal points,
            // and then trimmed of terminal '0's.  Then, we provide at least DECSHOWN fractional
            // decimal places, 0-filled on the right.  This allows us to tune the default fractional
            // precision of ZFuel, similarly to how dollars is typically shown with 2 decimals of
            // precision, eg. $1.20.                          98760 ==> 098760
            let decimals = format!("{:0>exponent$}", fraction.abs(), exponent = EXPONENT);
            let decimals = decimals.trim_end_matches('0'); // 098760 ==> 09876
            write!(
                f,
                "{}{}.{:0<decshown$}",
                sign,
                whole.abs(),
                decimals,
                decshown = DECSHOWN
            )
        }
    }
}

impl fmt::Debug for ZFuel {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ZFuel({})", self)
    }
}

///
/// ZFuel Operators -- Numerical operations with/without validity check
///
/// Neg, Add, Sub, Mul, Div of ZFuel always results in a checked Result<ZFuel, ZFuelError> value.
/// So, it is necessary to handle the ZFuelError that may result from invalid computations
/// before assigning any valid ZFuel result:
///
/// > let ZFuel: value = ( ZFuel::from_str( "1.0" ) + ZFuel::from_str( "2.0" ) )?
///
/// Attempting to use an existing Result::Err always maintains the lhs-most Err.
///

/// Negation of ZFuel can lead to an error at MINVALUE, so ZFuelResult is returned.  Because we cannot
/// implement Neg for non-local type result::Result<ZFuel,...>, to negate an &ZFuelResult, use
/// something like: fuel_result.to_owned().and_then(|f| -f)
impl Neg for ZFuel {
    // - ZFuel
    type Output = ZFuelResult;
    fn neg(self) -> ZFuelResult {
        Ok(match self.units.checked_neg() {
            Some(units) => ZFuel { units },
            None => {
                return Err(ZFuelError::Range(format!(
                    "Overflow in negation of ZFuel amount {}",
                    self
                )))
            }
        })
    }
}

impl Neg for &ZFuel {
    // - &ZFuel
    type Output = ZFuelResult;
    fn neg(self) -> ZFuelResult {
        -*self
    }
}

impl Add for ZFuel {
    // ZFuel + ZFuel
    type Output = ZFuelResult;
    fn add(self, rhs: ZFuel) -> Self::Output {
        Ok(match self.units.checked_add(rhs.units) {
            Some(units) => ZFuel { units },
            None => {
                return Err(ZFuelError::Range(format!(
                    "Overflow in addition of ZFuel amount {} + {}",
                    self, rhs
                )))
            }
        })
    }
}

impl Add<&ZFuel> for ZFuel {
    // ZFuel + &ZFuel
    type Output = ZFuelResult;
    fn add(self, rhs: &ZFuel) -> Self::Output {
        self + *rhs
    }
}

impl Add<ZFuel> for &ZFuel {
    // &ZFuel + ZFuel
    type Output = ZFuelResult;
    fn add(self, rhs: ZFuel) -> Self::Output {
        *self + rhs
    }
}

impl Add for &ZFuel {
    // &ZFuel + &ZFuel
    type Output = ZFuelResult;
    fn add(self, rhs: &ZFuel) -> Self::Output {
        *self + *rhs
    }
}

impl Add<ZFuelResult> for ZFuel {
    // ZFuel + Result<ZFuel, ZFuelError>
    type Output = ZFuelResult;
    fn add(self, other: Self::Output) -> Self::Output {
        match other {
            Ok(rhs) => self + rhs,
            Err(rhs_e) => Err(rhs_e),
        }
    }
}

impl Add<ZFuelResult> for &ZFuel {
    // &ZFuel + Result<ZFuel, ZFuelError>
    type Output = ZFuelResult;
    fn add(self, other: Self::Output) -> Self::Output {
        match other {
            Ok(rhs) => *self + rhs,
            Err(rhs_e) => Err(rhs_e),
        }
    }
}

impl Add<&ZFuelResult> for ZFuel {
    // ZFuel + &Result<ZFuel, ZFuelError>
    type Output = ZFuelResult;
    fn add(self, other: &Self::Output) -> Self::Output {
        match other {
            Ok(rhs) => self + *rhs,
            Err(rhs_e) => Err(rhs_e.clone()),
        }
    }
}

impl Add<&ZFuelResult> for &ZFuel {
    // &ZFuel + &Result<ZFuel, ZFuelError>
    type Output = ZFuelResult;
    fn add(self, other: &Self::Output) -> Self::Output {
        match other {
            Ok(rhs) => *self + *rhs,
            Err(rhs_e) => Err(rhs_e.clone()),
        }
    }
}

impl Add<ZFuel> for ZFuelResult {
    // Result<ZFuel, ZFuelError> + ZFuel
    type Output = ZFuelResult;
    fn add(self, rhs: ZFuel) -> Self::Output {
        match self {
            Ok(lhs) => lhs + rhs,
            Err(lhs_e) => Err(lhs_e),
        }
    }
}

impl Add<&ZFuel> for ZFuelResult {
    // Result<ZFuel, ZFuelError> + &ZFuel
    type Output = ZFuelResult;
    fn add(self, rhs: &ZFuel) -> Self::Output {
        match self {
            Ok(lhs) => lhs + *rhs,
            Err(lhs_e) => Err(lhs_e),
        }
    }
}

impl Add<ZFuel> for &ZFuelResult {
    // &Result<ZFuel, ZFuelError> + ZFuel
    type Output = ZFuelResult;
    fn add(self, rhs: ZFuel) -> Self::Output {
        match self {
            Ok(lhs) => *lhs + rhs,
            Err(lhs_e) => Err(lhs_e.clone()),
        }
    }
}

impl Add<&ZFuel> for &ZFuelResult {
    // &Result<ZFuel, ZFuelError> + &ZFuel
    type Output = ZFuelResult;
    fn add(self, rhs: &ZFuel) -> Self::Output {
        match self {
            Ok(lhs) => *lhs + *rhs,
            Err(lhs_e) => Err(lhs_e.clone()),
        }
    }
}

impl AddAssign<ZFuel> for ZFuelResult {
    // Result<ZFuel, ZFuelError> += ZFuel
    fn add_assign(&mut self, rhs: ZFuel) {
        *self = match self {
            Ok(lhs) => ZFuel::from(lhs) + rhs,
            Err(lhs_e) => Err(lhs_e.clone()),
        };
    }
}

impl AddAssign<&ZFuel> for ZFuelResult {
    // Result<ZFuel, ZFuelError> += &ZFuel
    fn add_assign(&mut self, rhs: &ZFuel) {
        *self = match self {
            Ok(lhs) => ZFuel::from(lhs) + rhs,
            Err(lhs_e) => Err(lhs_e.clone()),
        };
    }
}

impl Sub for ZFuel {
    // ZFuel - ZFuel
    type Output = ZFuelResult;
    fn sub(self, rhs: ZFuel) -> Self::Output {
        Ok(match self.units.checked_sub(rhs.units) {
            Some(units) => ZFuel { units },
            None => {
                return Err(ZFuelError::Range(format!(
                    "Overflow in subtraction of ZFuel amount {} - {}",
                    self, rhs
                )))
            }
        })
    }
}

impl Sub<&ZFuel> for ZFuel {
    // ZFuel - &ZFuel
    type Output = ZFuelResult;
    fn sub(self, rhs: &ZFuel) -> Self::Output {
        self - *rhs
    }
}

impl Sub<ZFuel> for &ZFuel {
    // &ZFuel - ZFuel
    type Output = ZFuelResult;
    fn sub(self, rhs: ZFuel) -> Self::Output {
        *self - rhs
    }
}

impl Sub for &ZFuel {
    // &ZFuel - &ZFuel
    type Output = ZFuelResult;
    fn sub(self, rhs: &ZFuel) -> Self::Output {
        *self - *rhs
    }
}

impl Sub<ZFuelResult> for ZFuel {
    // ZFuel - Result<ZFuel, ZFuelError>
    type Output = ZFuelResult;
    fn sub(self, other: Self::Output) -> Self::Output {
        match other {
            Ok(rhs) => self - rhs,
            Err(rhs_e) => Err(rhs_e),
        }
    }
}

impl Sub<ZFuelResult> for &ZFuel {
    // &ZFuel - Result<ZFuel, ZFuelError>
    type Output = ZFuelResult;
    fn sub(self, other: Self::Output) -> Self::Output {
        match other {
            Ok(rhs) => *self - rhs,
            Err(rhs_e) => Err(rhs_e),
        }
    }
}

impl Sub<&ZFuelResult> for ZFuel {
    // ZFuel - &Result<ZFuel, ZFuelError>
    type Output = ZFuelResult;
    fn sub(self, other: &Self::Output) -> Self::Output {
        match other {
            Ok(rhs) => self - *rhs,
            Err(rhs_e) => Err(rhs_e.clone()),
        }
    }
}

impl Sub<&ZFuelResult> for &ZFuel {
    // &ZFuel - &Result<ZFuel, ZFuelError>
    type Output = ZFuelResult;
    fn sub(self, other: &Self::Output) -> Self::Output {
        match other {
            Ok(rhs) => *self - *rhs,
            Err(rhs_e) => Err(rhs_e.clone()),
        }
    }
}

impl Sub<ZFuel> for ZFuelResult {
    // Result<ZFuel, ZFuelError> - ZFuel
    type Output = ZFuelResult;
    fn sub(self, rhs: ZFuel) -> Self::Output {
        match self {
            Ok(lhs) => lhs - rhs,
            Err(lhs_e) => Err(lhs_e),
        }
    }
}

impl Sub<&ZFuel> for ZFuelResult {
    // Result<ZFuel, ZFuelError> - &ZFuel
    type Output = ZFuelResult;
    fn sub(self, rhs: &ZFuel) -> Self::Output {
        match self {
            Ok(lhs) => lhs - *rhs,
            Err(lhs_e) => Err(lhs_e),
        }
    }
}

impl Sub<ZFuel> for &ZFuelResult {
    // &Result<ZFuel, ZFuelError> - ZFuel
    type Output = ZFuelResult;
    fn sub(self, rhs: ZFuel) -> Self::Output {
        match self {
            Ok(lhs) => *lhs - rhs,
            Err(lhs_e) => Err(lhs_e.clone()),
        }
    }
}

impl Sub<&ZFuel> for &ZFuelResult {
    // &Result<ZFuel, ZFuelError> - &ZFuel
    type Output = ZFuelResult;
    fn sub(self, rhs: &ZFuel) -> Self::Output {
        match self {
            Ok(lhs) => *lhs - *rhs,
            Err(lhs_e) => Err(lhs_e.clone()),
        }
    }
}

impl SubAssign<ZFuel> for ZFuelResult {
    // Result<ZFuel, ZFuelError> -= ZFuel
    fn sub_assign(&mut self, rhs: ZFuel) {
        *self = match self {
            Ok(lhs) => ZFuel::from(lhs) - rhs,
            Err(lhs_e) => Err(lhs_e.clone()),
        };
    }
}

impl SubAssign<&ZFuel> for ZFuelResult {
    // Result<ZFuel, ZFuelError> -= &ZFuel
    fn sub_assign(&mut self, rhs: &ZFuel) {
        *self = match self {
            Ok(lhs) => ZFuel::from(lhs) - rhs,
            Err(lhs_e) => Err(lhs_e.clone()),
        };
    }
}

/// ZFuel * Fraction, ZFuel / Fraction -- always round up on loss of precision
///
/// If a Fraction's numerator would result in an overflow of the maximum allowable ZFuel amount,
/// produce an Err result.  Non-zero results below the minimum fractional ZFuel value threshold are
/// always rounded up.
///
/// For example, .75% of 1334 == 10.005, or 11 if rounded up.  A Fraction representing .75%,
/// `Fraction::new(3, 400)` multiplied by 0.001334 ZFuel: `ZFuel{ units: 1334 }` would result in a
/// `Some(quotient)` of 1334 / 400 == 3, and then 3 * 3 == 9.
///
/// In general, any ZFuel.units precision below the Fraction.denominator will be lost, because we
/// perform a division by the Fraction.denominator, to avoid overflow on large values.  If we had
/// instead performed the multiplication by the numerator first, we would have have computed 1334 *
/// 3 == 4002, and 4002 / 400 == 10; also correct, but no more useful if our intent is to "round up"
/// since the desired result is 11 (and, it would overflow on large values).  However, here we could
/// clearly detect that 4002 % 400 == 2 remainder, indicating that we must add 1 to the result to
/// round up.
///
/// We must find the remainder of the division by the denominator 400, after multiplying it by the
/// numerator, see if (when rounded up by just less than the denominator), how many multiples of the
/// denominator we missed:
///
/// //          1334 % 400 == 134,
/// //             134 * 3 == 402
/// //     402 + (400 - 1) == 801
/// //           801 / 400 == 2.
/// //
/// Since all of these are small numbers, overflow is not possible (unless the Fraction is huge)
///
/// Note the checked_rem is a signed remainder, not a euclidean modulo, eg. from
/// https://internals.rust-lang.org/t/mathematical-modulo-operator/5952:
///
/// // Remainder operator (%)
/// //   5 %  3 //  2
/// //   5 % -3 //  2
/// //  -5 %  3 // -2
/// //  -5 % -3 // -2
///
/// // Modulo operator (%%)
/// //   5 %%  3 //  2
/// //   5 %% -3 // -1
/// //  -5 %%  3 //  1
/// //  -5 %% -3 // -2
///
/// Therefore, when multiplying by -'ve ZFuel, any checked_rem will be remain -'ve
///
impl Mul<Fraction> for ZFuel {
    // ZFuel * Fraction
    type Output = ZFuelResult;
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn mul(self, rhs: Fraction) -> Self::Output {
        match self.units.checked_div(rhs.denominator) {
            Some(quotient) => match quotient.checked_mul(rhs.numerator) {
                Some(units) => match self
                    .units
                    .checked_rem(rhs.denominator)
                    .and_then(|e| e.checked_mul(rhs.numerator))
                    .and_then(|e| {
                        if e >= 0 {
                            e.checked_add(rhs.denominator - 1)
                        } else {
                            e.checked_sub(rhs.denominator - 1)
                        }
                    })
                    .and_then(|e| e.checked_div(rhs.denominator))
                {
                    Some(extra) => Ok(ZFuel {
                        units: units + extra,
                    }),
                    None => Err(ZFuelError::FractionOverflow((self, rhs))),
                },
                None => Err(ZFuelError::FractionOverflow((self, rhs))),
            },
            None => Err(ZFuelError::FractionOverflow((self, rhs))),
        }
    }
}

impl Mul<&Fraction> for ZFuel {
    // ZFuel * &Fraction
    type Output = ZFuelResult;
    fn mul(self, rhs: &Fraction) -> Self::Output {
        self * *rhs
    }
}

impl Mul<Fraction> for &ZFuel {
    // &ZFuel * Fraction
    type Output = ZFuelResult;
    fn mul(self, rhs: Fraction) -> Self::Output {
        *self * rhs
    }
}

impl Mul<&Fraction> for &ZFuel {
    // &ZFuel * &Fraction
    type Output = ZFuelResult;
    fn mul(self, rhs: &Fraction) -> Self::Output {
        *self * *rhs
    }
}

impl MulAssign<Fraction> for ZFuelResult {
    // Result<ZFuel, ZFuelError> *= Fraction
    fn mul_assign(&mut self, rhs: Fraction) {
        *self = match self {
            Ok(lhs) => ZFuel::from(lhs) * rhs,
            Err(lhs_e) => Err(lhs_e.clone()),
        };
    }
}

impl MulAssign<&Fraction> for ZFuelResult {
    // Result<ZFuel, ZFuelError> *= &Fraction
    fn mul_assign(&mut self, rhs: &Fraction) {
        *self = match self {
            Ok(lhs) => ZFuel::from(lhs) * rhs,
            Err(lhs_e) => Err(lhs_e.clone()),
        };
    }
}

impl Div<Fraction> for ZFuel {
    // ZFuel / Fraction
    type Output = ZFuelResult;
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, rhs: Fraction) -> Self::Output {
        self * Fraction {
            numerator: rhs.denominator,
            denominator: rhs.numerator,
        }
    }
}

impl Div<&Fraction> for ZFuel {
    // ZFuel / &Fraction
    type Output = ZFuelResult;
    fn div(self, rhs: &Fraction) -> Self::Output {
        self / *rhs
    }
}

impl Div<Fraction> for &ZFuel {
    // &ZFuel / Fraction
    type Output = ZFuelResult;
    fn div(self, rhs: Fraction) -> Self::Output {
        *self / rhs
    }
}

impl Div<&Fraction> for &ZFuel {
    // &ZFuel / &Fraction
    type Output = ZFuelResult;
    fn div(self, rhs: &Fraction) -> Self::Output {
        *self / *rhs
    }
}

/*
/// Delta -- a ZFuel value associated with a timestamp
#[derive(Deserialize, Debug, Serialize, Clone, PartialEq, Eq)]
pub struct Delta(pub Timestamp, pub ZFuel);

/// Limit -- Computes and enforces a rolling Period's value.
///
/// We'll be using this for configuring amount/period limits, but will not allow incoming
/// configuration (deserializing) of recent Deltas -- only supports reporting (serializing) of the
/// most recent Deltas for each counterparty.
#[derive(Deserialize, Debug, Serialize, Clone, PartialEq, Eq)]
pub struct Limit {
    pub amount: Option<ZFuel>,   // Some("1000.0") --> limit, None --> not allowed
    pub period: Option<Period>, // Some("1w") --> over time period, None --> each transaction
    #[serde(skip_deserializing, skip_serializing_if = "VecDeque::is_empty")]
    pub recent: VecDeque<Delta>, // Rolling history over period (not included in incoming API calls)
}

impl fmt::Display for Limit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.period {
            None => match &self.amount {
                None // No ZFuel amount or Period limit! Transactions with this agent are explicitly *denied*.
                    => write!(f, "(agent denied)"),
                Some(amount) // ZFuel amount, but no Period specified.  Limit is applied on each Delta's change.
                    => write!(f, "♓{} / tx", amount),
            },
            Some(period) => match &self.amount {
                None // Period, but no ZFuel amount.  Only a single transaction per Period is allowed.
                    => write!(f, "1 tx / {}", period),
                Some(amount) // Both Period and ZFuel; a maximum ZFuel amount for the Period has been specified.
                    => write!(f, "♓{} / {}", amount, period),
            },
        }
    }
}

impl Limit {
    /// Tests to see if *any* transactions are allowed with this counterparty by this (incoming or outgoing) Limit
    pub fn allow(&self) -> Result<(), ZFuelError> {
        if self.period.is_none() && self.amount.is_none() {
            Err(ZFuelError::AgentDenied(self.to_owned()))
        } else {
            Ok(())
        }
    }
    /// delta -- Computes the current value of this ZFuel amount change, effective at timestamp
    ///
    /// Updates self.recent w/ latest Delta's relevant to the .period (hence, needs self: &mut Self)
    ///
    /// For a non-Periodic Limit, this just validates the amount.  For Period-based Limits, a vector
    /// of the last Period's worth of balance changes are kept, and the sum is computed.  If the
    /// supplied value is invalid (exceeds the Limit), or is wildly out of order (ie. older than the
    /// oldest entry already in the `recent` heap), or overflows, or is otherwise suspect, a
    /// ZFuelError will result, indicating failure of the proposed change.  On success, the original
    /// ZFuel value is returned as a ZFuelResult.  If the fuel `change` is already in Err ZFuelResult,
    /// it will be passed through (retaining the Err).
    ///
    /// WARNING: This must be invoked carefully (eg. only once, with each new Delta(timestamp,
    /// change)), or the same "transaction" could easily result in failure.  We know that,
    /// presently, it is invoked during operation of the state machine, which prevents the commit of
    /// duplicate Events.  However, if other validation code is written that accidentally invokes
    /// this more than once (eg. checks first in the state machine, and again later, somewhere
    /// else), we could get erroneous results.  If we *test* for idempotency, here, though -- we
    /// could erroneously detect two sequential, valid, transactions with *identical* amounts, that
    /// happened to be processed in (what appears to be) the same instant of time.  Even if the
    /// system clock is guaranteed to be monotonic and increasing (which they are often *not*), we
    /// can't guarantee that two subsequent Events will have unique timestamps.  So, we do *not*
    /// check for idempotency.
    //TODO: impl Timestamp + Period
    pub fn delta(self: &mut Self, timestamp: &Timestamp, change: &ZFuelResult) -> ZFuelResult {
        // Filter out already `change` that are already Err.
        let change_fuel = match change {
            Err(_e) => return change.to_owned(),
            Ok(f) => f.to_owned(),
        };
        let change_delta = Delta(timestamp.to_owned(), change_fuel);
        match &self.period {
            None => {
                match self.amount {
                    Some(amount) => {
                        // ZFuel amount, but no Period specified.  Limit is applied on each Delta's change.
                        if change_fuel > amount {
                            return Err(ZFuelError::LimitExceeded((
                                self.to_owned(),
                                amount.to_string(),
                                change_delta,
                            )));
                        }
                    }
                    None => {
                        // No ZFuel amount or Period limit! Transactions with this agent are
                        // explicitly *denied*.  For example, if the "default" limits are tight, but
                        // exceptions are specified for certain known accounts, or if certain
                        // counterparties are explicitly disallowed from incoming/outgoing
                        // transactions.  To specify *no* limit, provide empty vector() in
                        // TxLimits.incoming/outgoing (ie. Here's the limits for .incoming -- and
                        // there aren't any).
                        return Err(ZFuelError::AgentDenied(self.to_owned()));
                    }
                }
            }
            Some(period) => {
                // Compute the oldest allowed entry in .recents, by offset from timestamp; the any
                // Deltas >= oldest computed will be purged.  The oldest are at the front of
                // .recents.

                // let oldest = (timestamp.clone() + period)?;
                // Discard .recent Deltas greater or *equal*, so that Deltas that arrive at
                // *exactly* the rate Period don't exceed the Limit.
                while let Some(d) = self.recent.front() {
                    // self.recent.get(0) {
                    if d.0 >= oldest {
                        self.recent.pop_front(); // self.recent.drain(..1).for_each(drop);
                    } else {
                        break;
                    }
                }

                self.recent.push_back(change_delta.clone()); // self.recent.push(change_delta.clone());
                match self.amount {
                    Some(fuel) => {
                        // Both Period and ZFuel; a maximum ZFuel amount for the Period has been
                        // specified.  Ensure we haven't exceeded it.  Sum up all the recent deltas
                        // and ensure we detect overflow, using ZFuelResult + ZFuel
                        let sum = self
                            .recent
                            .iter()
                            .fold(ZFuelResult::from(Ok(ZFuel::from(0))), |acc, d| acc + d.1)?;
                        if sum > fuel {
                            return Err(ZFuelError::LimitExceeded((
                                self.to_owned(),
                                sum.to_string(),
                                change_delta,
                            )));
                        }
                    }
                    None => {
                        // Period, but no ZFuel amount.  Only a single transaction per Period is allowed.
                        println!(
                            "Limit {} appends recent: {:?} len {}",
                            self,
                            &change_delta,
                            self.recent.len()
                        );
                        if self.recent.len() > 1 {
                            return Err(ZFuelError::LimitExceeded((
                                self.to_owned(),
                                ZFuel::from(0).to_string(),
                                change_delta,
                            )));
                        }
                    }
                }
            }
        }

        change.to_owned() // On success, returns the original ZFuel amount
    }
}
*/
#[cfg(test)]
pub mod tests {
    use crate::fuel::{self, u128_to_i128, ZFuel, ZFuelResult};
    use std::str::FromStr;
    #[test]

    fn fuel_check_test() {
        let _ = ZFuel::check("1.0").unwrap();
        match ZFuel::check("-1") {
            Ok(f) => panic!(
                "Expected failure due to fuel being a negative value: ♓{}",
                f
            ),
            Err(e) => assert_eq!(
                format!("{}", e),
                "ZFuel Range Error: Invalid negative amount -1"
            ),
        }
    }
    #[test]
    /// smoke test ZFuel
    fn fuel_smoke_test() {
        let f1 = ZFuel::from_str("0.012");
        assert_eq!(format!("{:?}", f1), "Ok(ZFuel(0.012))");
        let f1 = ZFuel::from_str("1.0").unwrap();
        //let f1 = ZFuel::from_str( "0x5f5e100" ).unwrap();
        assert_eq!(f1.units, fuel::DENOMINATOR as i128);
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

        let f2 = ZFuel::from(-1234567890987654321);
        assert_eq!(f2.units, -1234567890987654321_i128);
        // At least the required amount of precision is always supplied to ensure no loss of data
        let d2 = format!("{}", f2);
        assert_eq!(
            d2,
            match fuel::DECSHOWN {
                6 => "-1234.567890",
                _ => "-1.234567890987654321",
            }
        );

        // Extending out fractions to fill at leas
        let f3 = ZFuel::from_str("999.5").unwrap();
        assert_eq!(f3.units, 999_500_000_000_000_000_000_i128);

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
        let f4 = ZFuel::from_str("-1234.5678901234567890123456").unwrap();
        assert_eq!(f4.units, -1234567890123456789012);
        let d4 = format!("{}", f4);
        assert_eq!(d4, "-1234.567890123456789012");

        // See if precision retaining maximums are enforced.  We're assuming i128 is NOT actually
        // implemented as IEEE 754 double-precision (where +/- 2^53-1 is the precision-loss limit).
        // Try to round-trip full-precision ZFuel values through Display "#.##"
        assert_eq!(
            fuel::MAXVALUE,
            170_141_183_460_469_231_731_687_303_715_884_105_727
        );
        assert_eq!(
            fuel::MAXRANGE,
            170_141_183_460_469_231_731_687_303_715_884_105_727
        );
        assert_eq!(
            fuel::MINVALUE,
            -170_141_183_460_469_231_731_687_303_715_884_105_728
        );
        assert_eq!(
            fuel::MINRANGE,
            170_141_183_460_469_231_731_687_303_715_884_105_728
        );

        assert_eq!(
            format!(
                "{:?}",
                ZFuel::from_str("-1701411834604692.31731687303715884105728")
            ),
            "Ok(ZFuel(-1701411834604692.317316873037158841))"
        );
        assert_eq!(
            format!(
                "{:?}",
                ZFuel::from_str("-1701411834604692.31731687303715884105728")
            ),
            "Ok(ZFuel(-1701411834604692.317316873037158841))"
        );
        match ZFuel::from_str( "0x80000000000000000000000000000000" ) { // MAXRANGE + 1
            Ok(f) => panic!( "Expected failure due to fuel::MAXRANGE did not occur: ♓{}", f ),
            Err(e) => assert_eq!( format!("{}", e ),
                                  "ZFuel Range Error: Exceeded range for ZFuel mantissa 170141183460469231731687303715884105728, fraction 0" ),
        }
        // Max Values that it will accept
        assert_eq!(
            format!("{:?}", ZFuel::from_str("9999999999999999.9999999999999999")),
            "Ok(ZFuel(9999999999999999.9999999999999999))"
        );
        assert_eq!(
            format!(
                "{:?}",
                ZFuel::from_str("-9999999999999999.9999999999999999")
            ),
            "Ok(ZFuel(-9999999999999999.9999999999999999))"
        );
        match ZFuel::from_str("1_000_000_000_000_000_000") {
            Ok(f) => panic!(
                "Expected failure due to fuel::MINVRANGE did not occur: ♓{}",
                f
            ),
            Err(e) => assert_eq!(
                format!("{}", e),
                "ZFuel Range Error: Invalid ZFuel amount 1_000_000_000_000_000_000"
            ),
        }
    }

    #[test]
    fn fuel_operators() {
        // ZFuel + ZFuel
        let sum = ZFuel::from_str("1.23").unwrap() + ZFuel::from_str("-1000").unwrap();
        match &sum {
            Ok(ref f) => assert_eq!(format!("{}", f), "-998.77"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        // Result<ZFuel,...> + ZFuel
        let sum2 = sum + ZFuel::from_str("100").unwrap();
        match &sum2 {
            Ok(ref f) => assert_eq!(format!("{}", f), "-898.77"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        // ZFuel + Result<ZFuel,...>
        let sum3 = ZFuel::from_str("-1111.23").unwrap() + sum2;
        match &sum3 {
            Ok(ref f) => assert_eq!(format!("{}", f), "-2010"),
            Err(e) => panic!("Expected success, not {}", e),
        }

        // Check all ZFuel + ZFuel ref variants
        match ZFuel::from(1_000_000_000_000_000_000) + ZFuel::from(1) {
            Ok(f) => assert_eq!(format!("{}", f), "1.000000000000000001"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match ZFuel::from(1_000_000_000_000_000_000) + &ZFuel::from(2) {
            Ok(f) => assert_eq!(format!("{}", f), "1.000000000000000002"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match &ZFuel::from(2_000_000_000_000_000_000) + ZFuel::from(1) {
            Ok(f) => assert_eq!(format!("{}", f), "2.000000000000000001"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match &ZFuel::from(2_000_000_000_000_000_000) + &ZFuel::from(2) {
            Ok(f) => assert_eq!(format!("{}", f), "2.000000000000000002"),
            Err(e) => panic!("Expected success, not {}", e),
        }

        // Check all Result<ZFuel,...> + ZFuel ref variants
        match ZFuel::from_str("1") + ZFuel::from(1) {
            Ok(f) => assert_eq!(format!("{}", f), "1.000000000000000001"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match ZFuel::from_str("1") + &ZFuel::from(1) {
            Ok(f) => assert_eq!(format!("{}", f), "1.000000000000000001"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match &ZFuel::from_str("1") + ZFuel::from(1) {
            Ok(f) => assert_eq!(format!("{}", f), "1.000000000000000001"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match &ZFuel::from_str("1") + &ZFuel::from(1) {
            Ok(f) => assert_eq!(format!("{}", f), "1.000000000000000001"),
            Err(e) => panic!("Expected success, not {}", e),
        }

        // Check all ZFuel + Result<ZFuel,...> ref variants
        match ZFuel::from(1) + ZFuel::from_str("1") {
            Ok(f) => assert_eq!(format!("{}", f), "1.000000000000000001"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match &ZFuel::from(1) + ZFuel::from_str("1") {
            Ok(f) => assert_eq!(format!("{}", f), "1.000000000000000001"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match ZFuel::from(1) + &ZFuel::from_str("1") {
            Ok(f) => assert_eq!(format!("{}", f), "1.000000000000000001"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match &ZFuel::from(1) + &ZFuel::from_str("1") {
            Ok(f) => assert_eq!(format!("{}", f), "1.000000000000000001"),
            Err(e) => panic!("Expected success, not {}", e),
        }

        // Check all Result<ZFuel,...> += ZFuel ref variants
        let mut fa = ZFuel::from_str("1");
        fa += ZFuel::from(1);
        match fa {
            Ok(f) => assert_eq!(format!("{}", f), "1.000000000000000001"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        fa += &ZFuel::from(-2);
        match fa {
            Ok(f) => assert_eq!(format!("{}", f), "0.999999999999999999"),
            Err(e) => panic!("Expected success, not {}", e),
        }

        // Check all ZFuel - ZFuel ref variants: 1.0 - 0.0000000000000001
        match ZFuel::from(1_000_000_000_000_000_000) - ZFuel::from(1) {
            Ok(f) => assert_eq!(format!("{}", f), "0.999999999999999999"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match ZFuel::from(1_000_000_000_000_000_000) - &ZFuel::from(2) {
            Ok(f) => assert_eq!(format!("{}", f), "0.999999999999999998"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match &ZFuel::from(2_000_000_000_000_000_000) - ZFuel::from(1) {
            Ok(f) => assert_eq!(format!("{}", f), "1.999999999999999999"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match &ZFuel::from(2_000_000_000_000_000_000) - &ZFuel::from(2) {
            Ok(f) => assert_eq!(format!("{}", f), "1.999999999999999998"),
            Err(e) => panic!("Expected success, not {}", e),
        }

        // Check all Result<ZFuel,...> - ZFuel ref variants: 1.0 - 0.0000000000000001
        match ZFuel::from_str("1") - ZFuel::from(1) {
            Ok(f) => assert_eq!(format!("{}", f), "0.999999999999999999"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match ZFuel::from_str("1") - &ZFuel::from(1) {
            Ok(f) => assert_eq!(format!("{}", f), "0.999999999999999999"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match &ZFuel::from_str("1") - ZFuel::from(1) {
            Ok(f) => assert_eq!(format!("{}", f), "0.999999999999999999"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match &ZFuel::from_str("1") - &ZFuel::from(1) {
            Ok(f) => assert_eq!(format!("{}", f), "0.999999999999999999"),
            Err(e) => panic!("Expected success, not {}", e),
        }

        // Check all ZFuel - Result<ZFuel,...> ref variants: 0.000001 - 1.0
        match ZFuel::from(1) - ZFuel::from_str("1") {
            Ok(f) => assert_eq!(format!("{}", f), "-0.999999999999999999"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match &ZFuel::from(1) - ZFuel::from_str("1") {
            Ok(f) => assert_eq!(format!("{}", f), "-0.999999999999999999"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match ZFuel::from(1) - &ZFuel::from_str("1") {
            Ok(f) => assert_eq!(format!("{}", f), "-0.999999999999999999"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        match &ZFuel::from(1) - &ZFuel::from_str("1") {
            Ok(f) => assert_eq!(format!("{}", f), "-0.999999999999999999"),
            Err(e) => panic!("Expected success, not {}", e),
        }

        // Check all Result<ZFuel,...> -= ZFuel ref variants
        let mut fa = ZFuel::from_str("1");
        fa -= ZFuel::from(1);
        match fa {
            Ok(f) => assert_eq!(format!("{}", f), "0.999999999999999999"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        fa -= &ZFuel::from(2_000_000_000_000_000_001);
        match fa {
            Ok(f) => assert_eq!(format!("{}", f), "-1.000000000000000002"),
            Err(e) => panic!("Expected success, not {}", e),
        }
        fa -= &ZFuel::from(-2_000_000_000_000_000_003);
        match fa {
            Ok(f) => assert_eq!(format!("{}", f), "1.000000000000000001"),
            Err(e) => panic!("Expected success, not {}", e),
        }

        // And make sure errors produced and propogate; later terms just propogate original Err(_)
        match ZFuel::from( u128_to_i128( true, fuel::MINRANGE, 0_u128, fuel::MINRANGE ).unwrap() ) - ZFuel::from( 1 )  {
            Ok(f) => panic!( "Expected failure, not {}", f ),
            Err(e) => assert_eq!( format!( "{}", e ),
                                  "ZFuel Range Error: Overflow in subtraction of ZFuel amount -170141183460469231731.687303715884105728 - 0.000000000000000001" ),
        }
        match ZFuel::from( u128_to_i128( true, fuel::MINRANGE, 0_u128, fuel::MINRANGE ).unwrap() ) - ZFuel::from( 1 ) + ZFuel::from( 1 ) {
            Ok(f) => panic!( "Expected failure, not {}", f ),
            Err(e) => assert_eq!( format!( "{}", e ),
                                  "ZFuel Range Error: Overflow in subtraction of ZFuel amount -170141183460469231731.687303715884105728 - 0.000000000000000001" ),
        }

        // Try negation
        assert_eq!(
            format!("{}", (-ZFuel::from(fuel::MAXVALUE)).unwrap()),
            "-170141183460469231731.687303715884105727"
        );
        assert_eq!(
            format!("{}", (-&ZFuel::from(fuel::MAXVALUE)).unwrap()),
            "-170141183460469231731.687303715884105727"
        );
        // Negating the largest negative value should lead to overflow
        assert_eq!(
            format!("{:?}", -&ZFuel::from(fuel::MINVALUE)),
            "Err(Range(\"Overflow in negation of ZFuel amount -170141183460469231731.687303715884105728\"))"
        );
    }

    #[test]
    fn fuel_comparisons() {
        assert!(ZFuel::from(1_000_001) > ZFuel::from(1_000_000));
        assert!(ZFuel::from(1_000_000) < ZFuel::from(1_000_001));

        assert!(ZFuel::from(1_000_001) == ZFuel::from(1_000_001));
        assert!(ZFuel::from(1_000_000) <= ZFuel::from(1_000_001));
        assert!(ZFuel::from(1_000_001) >= ZFuel::from(1_000_000));

        assert!(ZFuel::from(1_000_000) == ZFuel::from(1_000_000));
        assert!(ZFuel::from(1_000_000) <= ZFuel::from(1_000_000));
        assert!(ZFuel::from(1_000_000) >= ZFuel::from(1_000_000));
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
        // ZFuel::units will result in fees of 0, instead of 7: 199 / 200 * 7 == 0.  And even on
        // larger values, since we're doing integer division, we'll still lose precision: 399 / 200
        // * 7 == 7, not the perhaps expected 13.  So, in essence, we'll always be "rounding down"
        // ZFuel fees.  But, considering that ZFuel is denominated in units of
        // 1/100,000,000th of a ZFuel, these rounding truncation errors will only be significant
        // when computing fees on exceedingly tiny transactions.

        let feepct = Fraction::new(35, 1000).unwrap().reduce();
        assert_eq!((feepct.numerator, feepct.denominator), (7, 200));

        // Observe that we end up losing precision on very small transactions, and always round up.
        //
        // The infinite precision fee calculation should "round up" to H0.000014:
        //     H0.000399 * 7 / 200 == H0.000013965
        // But instead, we lose precision both by the reverse-ordering of multiplying out the
        // Fraction (to avoid overflow on large ZFuel values), and through truncation:
        //     H0.000399     / 200 == H0.000001995 =~= H0.000001 * 7 == H0.000007
        // When we round up, we first compute the remainder of the division:
        //     H.000399      % 200 == 199
        // Then we amplify by the numerator and gross it up by 1 less than the denominator:
        //           199 * 7 + 199 == 1592
        // And then see how many denominators worth of rounding error we discarded:
        //              1592 / 200 == 7
        let feeamt = ZFuel { units: 399 } * &feepct;
        match &feeamt {
            Ok(ref f) => assert_eq!(format!("{}", f), "0.000000000000000014"), // was "0.000007" w/o round up
            Err(e) => panic!("Expected success, not {}", e),
        }

        // See that division by the inverse Fraction is identical
        let inv_feepct = Fraction {
            denominator: feepct.numerator,
            numerator: feepct.denominator,
        };
        let feeamt = ZFuel { units: 399 } / &inv_feepct;
        match &feeamt {
            Ok(ref f) => assert_eq!(format!("{}", f), "0.000000000000000014"),
            Err(e) => panic!("Expected success, not {}", e),
        }

        // And, we can be assured of being able to compute fees on the maximum transaction value,
        // 2^63-1: 9,223,372,036,854,775,807 * 7 / 200 == 322818021289917153.245, so rounded up we
        // should get a fee of: 322818021289917154, or H5954941421116423110.609055630055943701
        let amount = ZFuel {
            units: fuel::MAXVALUE,
        };
        let feeamt = amount * &feepct;
        match feeamt {
            Ok(f) => assert_eq!(format!("{}", f), "5954941421116423110.609055630055943701"), // was "322818021289.917153" w/o round up
            Err(e) => panic!("Expected success, not {}", e),
        };
        match ZFuel::new(fuel::MINVALUE) * &feepct {
            // try -'ve, to ensure round up works
            Ok(f) => assert_eq!(format!("{}", f), "-5954941421116423110.609055630055943701"),
            Err(e) => panic!("Expected success, not {}", e),
        };

        // Test all {T,&T} {*,/} {U,&U} combinations
        match ZFuel::from(fuel::MAXVALUE) * Fraction::new(35, 1000).unwrap().reduce() {
            Ok(f) => assert_eq!(format!("{}", f), "5954941421116423110.609055630055943701"),
            Err(e) => panic!("Expected success, not {}", e),
        };
        match &ZFuel::from(fuel::MAXVALUE) * Fraction::new(35, 1000).unwrap().reduce() {
            Ok(f) => assert_eq!(format!("{}", f), "5954941421116423110.609055630055943701"),
            Err(e) => panic!("Expected success, not {}", e),
        };
        match ZFuel::from(fuel::MAXVALUE) * &Fraction::new(35, 1000).unwrap().reduce() {
            Ok(f) => assert_eq!(format!("{}", f), "5954941421116423110.609055630055943701"),
            Err(e) => panic!("Expected success, not {}", e),
        };
        match &ZFuel::from(fuel::MAXVALUE) * &Fraction::new(35, 1000).unwrap().reduce() {
            Ok(ref f) => assert_eq!(format!("{}", f), "5954941421116423110.609055630055943701"),
            Err(e) => panic!("Expected success, not {}", e),
        };

        match ZFuel::from(fuel::MAXVALUE) / Fraction::new(1000, 35).unwrap().reduce() {
            Ok(f) => assert_eq!(format!("{}", f), "5954941421116423110.609055630055943701"),
            Err(e) => panic!("Expected success, not {}", e),
        };
        match &ZFuel::from(fuel::MAXVALUE) / Fraction::new(1000, 35).unwrap().reduce() {
            Ok(f) => assert_eq!(format!("{}", f), "5954941421116423110.609055630055943701"),
            Err(e) => panic!("Expected success, not {}", e),
        };
        match ZFuel::from(fuel::MAXVALUE) / &Fraction::new(1000, 35).unwrap().reduce() {
            Ok(f) => assert_eq!(format!("{}", f), "5954941421116423110.609055630055943701"),
            Err(e) => panic!("Expected success, not {}", e),
        };
        match &ZFuel::from(fuel::MAXVALUE) / &Fraction::new(1000, 35).unwrap().reduce() {
            Ok(ref f) => assert_eq!(format!("{}", f), "5954941421116423110.609055630055943701"),
            Err(e) => panic!("Expected success, not {}", e),
        };

        // Try in-place multiply; only works with mut Result<ZFuel,...>, because result could be erroneous
        let mut feeamt: ZFuelResult = Ok(ZFuel::from(fuel::MAXVALUE));
        feeamt *= feepct;
        match &feeamt {
            Ok(ref f) => assert_eq!(format!("{}", f), "5954941421116423110.609055630055943701"),
            Err(e) => panic!("Expected success, not {}", e),
        };

        // Force ZFuel * Fraction overflow
        assert_eq!(
            format!(
                "{}",
                (ZFuel::new(100) * Fraction::new(fuel::MAXVALUE, 2).unwrap()).unwrap_err()
            ),
            "ZFuel overflow in ♓0.0000000000000001 * 170141183460469231731687303715884105727/2"
        );
    }
}
