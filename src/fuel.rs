//! The Fuel Fuel type and math functions, and JSON serialization support.  Supports Fraction
//! type for computing fractional Fuel amounts using rational numbers; useful for expressing
//! "percentages" of Fuel amounts without losing (too much) precision, while retaining the
//! ability to compute Fuel transaction fees on the largest possible transaction amounts.

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

#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq)] // Copy req'd for binary op implementations
/// z Fuel, in 1/DENOMINATOR units
pub struct ZFuel {
    pub units: i64,
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
    pub fn new(units: i64) -> Self {
        ZFuel { units }
    }
    pub fn zero() -> Self {
        ZFuel { units: 0 }
    }
    fn parse_hex(input: &str) -> IResult<&str, (u64, u64), nom::error::Error<&str>> {
        map_res(preceded(tag("0x"), digit1), |hex: &str| {
            u64::from_str_radix(hex, 16).map(|val| (val, 0))
        })(input)
    }

    fn parse_decimal(input: &str) -> IResult<&str, (u64, u64)> {
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
        let mantissa = DENOMINATOR as u64
            * int_part.parse::<u64>().map_err(|_| {
                Err::Error(nom::error::Error::new(input, nom::error::ErrorKind::Digit))
            })?;
        let fraction = format!("{:0<exponent$.exponent$}", frac_part, exponent = EXPONENT)
            .parse::<u64>()
            .map_err(|_| Err::Error(nom::error::Error::new(input, nom::error::ErrorKind::Digit)))?;
        Ok((input, (mantissa, fraction)))
    }
    #[allow(clippy::type_complexity)]
    fn parse_fuel(
        input: &str,
    ) -> IResult<&str, (Option<&str>, (u64, u64)), nom::error::Error<&str>> {
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

/// Fuel::from_str -- Covert from &str; Result may yield Err if parsing fails
///
/// Handles hexadecimal and normal whole or fractional amounts of z Fuel, discarding any
/// precision beyond the 8th (EXPONENT) decimal place of fractional precision.  Returns ZFuelError
/// on any parsing or result value max range errors.
///
impl FromStr for ZFuel {
    type Err = ZFuelError;

    fn from_str(amount: &str) -> result::Result<Self, Self::Err> {
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

        // RE matched.  Either a hex, and int or a mnt (mantissa, possibly empty) is required.  We
        // will parse the mantissa and fraction as an *unsigned* u64, because we must allow full
        // [0,MINVALUE] range in the mantissa, which is not representable in an i64.
        let mantissa = match caps.name("hex") {
            None => match caps.name("int") {
                None => match caps.name("mnt") {
                    // not hex or int; must be a mantissa (possibly empty, if just ".123")
                    None => {
                        return Err(ZFuelError::Range(
                            // No 'hex', 'int', or 'mnt' found? Failure of FUEL_RE
                            format!("Invalid z Fuel amount {}", amount),
                        ));
                    }
                    Some(mnt) => match mnt.as_str().as_ref() {
                        "" => 0_u64,
                        mnt_str => {
                            DENOMINATOR as u64
                                * u64::from_str_radix(mnt_str, 10).or_else(|_| {
                                    Err(ZFuelError::Range(format!(
                                        "Invalid z Fuel amount {}; bad mantissa {}",
                                        amount,
                                        mnt.as_str()
                                    )))
                                })?
                        }
                    },
                },
                Some(int) => {
                    DENOMINATOR as u64
                        * u64::from_str_radix(int.as_str(), 10).or_else(|_| {
                            Err(ZFuelError::Range(format!(
                                "Invalid z Fuel amount {}; bad int {}",
                                amount,
                                int.as_str()
                            )))
                        })?
                }
            },
            Some(hex) => u64::from_str_radix(hex.as_str(), 16).or_else(|_| {
                Err(ZFuelError::Range(format!(
                    "Invalid z Fuel amount {}; bad hex {}",
                    amount,
                    hex.as_str()
                )))
            })?,
        };
        // Allow up the full capacity of a u64 worth of fractional digits, then truncate/zero-extend
        // to EXPONENT width.
        let fraction: u64 = match caps.name("frc") {
            None => 0,
            Some(fra) => u64::from_str_radix(
                // ".5" ==> "50000000" (truncate/fill to exactly EXPONENT width)
                &format!(
                    "{:0<exponent$.exponent$}",
                    fra.as_str(),
                    exponent = EXPONENT
                ),
                10,
            )
            .or_else(|_| {
                Err(ZFuelError::Range(format!(
                    "Invalid z Fuel amount {}; bad fraction {}",
                    amount,
                    fra.as_str()
                )))
            })?,
        };
        let sign = match caps.name("sig") {
            Some(cap) => cap.as_str(),
            None => "",
        };

        let units_res = match sign {
            "-" => u64_to_i64(true, mantissa, fraction, MINRANGE), // -...
            _ => u64_to_i64(false, mantissa, fraction, MAXRANGE),  // ..., or +...
        };
        let amount_fuel = match units_res {
            Ok(units) => ZFuel { units },
            Err(e) => return Err(e),
        };

        //println!( "z Fuel amount {} ==> sign \"{}\", mantissa {}, fraction {} == {}]",
        //          amount, sign, mantissa, fraction, amount_fuel );

        Ok(amount_fuel)
    }
}

/// i64 -> Fuel for all integer types
impl From<i64> for ZFuel {
    fn from(units: i64) -> ZFuel {
        ZFuel { units }
    }
}

/// & mut Fuel -> Fuel required for in-place operators
impl From<&mut ZFuel> for ZFuel {
    fn from(other: &mut ZFuel) -> ZFuel {
        ZFuel { units: other.units }
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
        let whole = self.units / (DENOMINATOR as i64); //            1234098760 / 10^6 == 1234
        let fraction = self.units - whole * (DENOMINATOR as i64); // 1234098760 - 1234 * 10^6 == 98760
                                                                  // fraction must be < DENOMINATOR, and will be +'ve or -'ve (same sign as self.units)
        if fraction == 0 {
            write!(f, "{}{}", sign, whole.abs())
        } else {
            // Any fractional portion is left-padded with '0' out to 8 (EXPONENT) decimal points,
            // and then trimmed of terminal '0's.  Then, we provide at least DECSHOWN fractional
            // decimal places, 0-filled on the right.  This allows us to tune the default fractional
            // precision of Fuel, similarly to how dollars is typically shown with 2 decimals of
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
        write!(f, "Fuel({})", self)
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
            Some(units) => ZFuel { units },
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
        Ok(match self.units.checked_add(rhs.units) {
            Some(units) => ZFuel { units },
            None => {
                return Err(ZFuelError::Range(format!(
                    "Overflow in addition of z Fuel amount {} + {}",
                    self, rhs
                )))
            }
        })
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
        Ok(match self.units.checked_sub(rhs.units) {
            Some(units) => ZFuel { units },
            None => {
                return Err(ZFuelError::Range(format!(
                    "Overflow in subtraction of z Fuel amount {} - {}",
                    self, rhs
                )))
            }
        })
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

/// Fuel * Fraction, Fuel / Fraction -- always round up on loss of precision
///
/// If a Fraction's numerator would result in an overflow of the maximum allowable z Fuel amount,
/// produce an Err result.  Non-zero results below the minimum fractional Fuel value threshold are
/// always rounded up.
///
/// For example, .75% of 1334 == 10.005, or 11 if rounded up.  A Fraction representing .75%,
/// `Fraction::new(3, 400)` multiplied by 0.001334 Fuel: `Fuel{ units: 1334 }` would result in a
/// `Some(quotient)` of 1334 / 400 == 3, and then 3 * 3 == 9.
///
/// In general, any Fuel.units precision below the Fraction.denominator will be lost, because we
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
/// Therefore, when multiplying by -'ve Fuel, any checked_rem will be remain -'ve
///
impl Mul<Fraction> for ZFuel {
    // Fuel * Fraction
    type Output = FuelResult;
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
    use crate::fuel::{self, u64_to_i64, FuelResult, ZFuel};
    use std::str::FromStr;

    #[test]
    /// smoke test Fuel
    fn fuel_smoke_test() {
        let f1 = ZFuel::from_str("1.0").unwrap();
        //let f1 = ZFuel::from_str( "0x5f5e100" ).unwrap();
        assert_eq!(f1.units, 1 * fuel::DENOMINATOR as i64);
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
        assert_eq!(f3.units, 999_500_000_i64);

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
            "Ok(Fuel(9223372036854.775807))"
        );
        assert_eq!(
            format!("{:?}", ZFuel::from_str(&"0x7fffffffffffffff")),
            "Ok(Fuel(9223372036854.775807))"
        );
        assert_eq!(
            format!("{:?}", ZFuel::from_str(&"-9223372036854.775808")),
            "Ok(Fuel(-9223372036854.775808))"
        );
        assert_eq!(
            format!("{:?}", ZFuel::from_str(&"-0x8000000000000000")),
            "Ok(Fuel(-9223372036854.775808))"
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
        let feeamt = ZFuel { units: 399 } * &feepct;
        match &feeamt {
            Ok(ref f) => assert_eq!(format!("{}", f), "0.000014"), // was "0.000007" w/o round up
            Err(e) => panic!("Expected success, not {}", e),
        }

        // See that division by the inverse Fraction is identical
        let inv_feepct = Fraction {
            denominator: feepct.numerator,
            numerator: feepct.denominator,
        };
        let feeamt = ZFuel { units: 399 } / &inv_feepct;
        match &feeamt {
            Ok(ref f) => assert_eq!(format!("{}", f), "0.000014"),
            Err(e) => panic!("Expected success, not {}", e),
        }

        // And, we can be assured of being able to compute fees on the maximum transaction value,
        // 2^63-1: 9,223,372,036,854,775,807 * 7 / 200 == 322818021289917153.245, so rounded up we
        // should get a fee of: 322818021289917154, or H322818021289.917154
        let amount = ZFuel {
            units: fuel::MAXVALUE,
        };
        let feeamt = amount * &feepct;
        match feeamt {
            Ok(f) => assert_eq!(format!("{}", f), "322818021289.917154"), // was "322818021289.917153" w/o round up
            Err(e) => panic!("Expected success, not {}", e),
        };
        match ZFuel::new(fuel::MINVALUE) * &feepct {
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
            Ok(ref f) => assert_eq!(format!("{}", f), "322818021289.917154"),
            Err(e) => panic!("Expected success, not {}", e),
        };

        // Force Fuel * Fraction overflow
        assert_eq!(
            format!(
                "{}",
                (ZFuel::new(100) * Fraction::new(fuel::MAXVALUE, 2).unwrap()).unwrap_err()
            ),
            "Fuel overflow in ♓0.0001 * 9223372036854775807/2"
        );
    }
}
