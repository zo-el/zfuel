use crate::error::ZFuelError;
// use hdi::prelude::timestamp::Timestamp;
use regex::Regex;
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use std::{convert::TryFrom, fmt, str::FromStr, time::Duration};
/// A human-readable time Period, implemented as a std::time::Duration (which is unsigned).
/// Conversion to/from and Serializable to/from readable form: "1w2d3h4.567s", at full Duration
/// precision; values > 1s w/ ms precision are formatted to fractional seconds w/ full precision,
/// while values < 1s are formatted to integer ms, us or ns as appropriate.  Accepts y/yr/year,
/// w/wk/week, d/dy/day, h/hr/hour, m/min/minute, s/sec/second, ms/millis/millisecond,
/// u/μ/micros/microsecond, n/nanos/nanosecond, singular or plural.  The humantime and
/// parse_duration crates are complex, incompatible with each other, depend on crates and/or do not
/// compile to WASM.
#[derive(Clone, Eq, PartialEq, Hash)]
pub struct Period(Duration);

/// Serialization w/ serde_json to/from String.  This means that a timestamp will be deserialized to
/// an Period specification and validated, which may fail, returning a serde::de::Error.  Upon
/// serialization, the canonicalized Period specification will be used.
impl Serialize for Period {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.to_string())
    }
}

impl<'d> Deserialize<'d> for Period {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'d>,
    {
        let s = String::deserialize(deserializer)?;
        Period::from_str(&s).map_err(|e| de::Error::custom(e.to_string()))
    }
}

// The humantime and parse_duration periods are incompatible; We choose compatibility w/ humantime's
// 365.25 days/yr.  An actual year is about 365.242196 days =~= 31,556,925.7344 seconds.  The
// official "leap year" calculation yields (365 + 1/4 - 1/100 + 1/400) * 86,400 == 31,556,952
// seconds/yr.  We're dealing with human-scale time periods with this data structure, so use the
// simpler definition of a year, to avoid seemingly-random remainders when years are involved.
const YR: u64 = 31_557_600_u64;
const WK: u64 = 604_800_u64;
const DY: u64 = 86_400_u64;
const HR: u64 = 3_600_u64;
const MN: u64 = 60_u64;

/// Outputs the human-readable form of the Period's Duration, eg. "1y2w3d4h56m7.89s", "456ms".
/// Debug output of Period specifier instead of underlying Duration seconds.
impl fmt::Debug for Period {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Period({})", self)
    }
}

impl fmt::Display for Period {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let secs = self.0.as_secs();
        let years = secs / YR;
        if years > 0 {
            write!(f, "{}y", years)?
        }
        let y_secs = secs % YR;
        let weeks = y_secs / WK;
        if weeks > 0 {
            write!(f, "{}w", weeks)?
        }
        let w_secs = y_secs % WK;
        let days = w_secs / DY;
        if days > 0 {
            write!(f, "{}d", days)?
        }
        let d_secs = w_secs % DY;
        let hours = d_secs / HR;
        if hours > 0 {
            write!(f, "{}h", hours)?
        }
        let h_secs = d_secs % HR;
        let minutes = h_secs / MN;
        if minutes > 0 {
            write!(f, "{}m", minutes)?
        }
        let s = h_secs % MN;
        let nsecs = self.0.subsec_nanos();
        let is_ns = (nsecs % 1000) > 0;
        let is_us = (nsecs / 1_000 % 1_000) > 0;
        let is_ms = (nsecs / 1_000_000) > 0;
        if is_ms && (s > 0 || is_ns) {
            // s+ms, or both ms and ns resolution data; default to fractional.
            let ss = format!("{:0>9}", nsecs); // eg.       2100  --> "000002100"
            let ss = ss.trim_end_matches('0'); // eg. "000002100" --> "0000021"
            write!(f, "{}.{}s", s, ss)
        } else if nsecs > 0 || s > 0 {
            // Seconds, and/or sub-seconds remain; auto-scale to s/ms/us/ns, whichever is the finest
            // precision that contains data.
            if s > 0 {
                write!(f, "{}s", s)?;
            }
            if is_ns {
                write!(f, "{}ns", nsecs)
            } else if is_us {
                write!(f, "{}us", nsecs / 1_000)
            } else if is_ms {
                write!(f, "{}ms", nsecs / 1_000_000)
            } else {
                Ok(())
            }
        } else if nsecs == 0 && secs == 0 {
            // A zero Duration
            write!(f, "0s")
        } else {
            // There were either secs or nsecs output above; no further output required
            Ok(())
        }
    }
}

impl FromStr for Period {
    type Err = ZFuelError;

    fn from_str(period_str: &str) -> Result<Self, Self::Err> {
        lazy_static! {
            static ref PERIOD_RE: Regex = Regex::new(
                r"(?xi) # whitespace-mode, case-insensitive
                ^
                (?:\s*(?P<y>\d+)\s*y((((ea)?r)s?)?)?)? # y|yr|yrs|year|years
                (?:\s*(?P<w>\d+)\s*w((((ee)?k)s?)?)?)?
                (?:\s*(?P<d>\d+)\s*d((((a )?y)s?)?)?)?
                (?:\s*(?P<h>\d+)\s*h((((ou)?r)s?)?)?)?
                (?:\s*(?P<m>\d+)\s*m((in(ute)?)s?)?)?  # m|min|minute|mins|minutes
                (?:
                  (?:\s* # seconds mantissa (optional) + fraction (required)
                    (?P<s_man>\d+)?
                    [.,](?P<s_fra>\d+)\s*             s((ec(ond)?)s?)?
                  )?
                | (?:
                    (:?\s*(?P<s> \d+)\s*              s((ec(ond)?)s?)?)?
                    (?:\s*(?P<ms>\d+)\s*(m|(milli))   s((ec(ond)?)s?)?)?
                    (?:\s*(?P<us>\d+)\s*(u|μ|(micro)) s((ec(ond)?)s?)?)?
                    (?:\s*(?P<ns>\d+)\s*(n|(nano))    s((ec(ond)?)s?)?)?
                  )
                )
                \s*
                $"
            )
            .unwrap();
        }

        Ok(Period({
            PERIOD_RE.captures(period_str).map_or_else(
                || {
                    Err(ZFuelError::Generic(format!(
                        "Failed to find Period specification in {:?}",
                        period_str
                    )))
                },
                |cap| {
                    let seconds: u64 = YR
                        * cap
                            .name("y")
                            .map_or("0", |y| y.as_str())
                            .parse::<u64>()
                            .map_err(|e| {
                                ZFuelError::Generic(format!(
                                    "Invalid year(s) in period {:?}: {:?}",
                                    period_str, e
                                ))
                            })?
                        + WK * cap
                            .name("w")
                            .map_or("0", |w| w.as_str())
                            .parse::<u64>()
                            .map_err(|e| {
                                ZFuelError::Generic(format!(
                                    "Invalid week(s) in period {:?}: {:?}",
                                    period_str, e
                                ))
                            })?
                        + DY * cap
                            .name("d")
                            .map_or("0", |d| d.as_str())
                            .parse::<u64>()
                            .map_err(|e| {
                                ZFuelError::Generic(format!(
                                    "Invalid days(s) in period {:?}: {:?}",
                                    period_str, e
                                ))
                            })?
                        + HR * cap
                            .name("h")
                            .map_or("0", |w| w.as_str())
                            .parse::<u64>()
                            .map_err(|e| {
                                ZFuelError::Generic(format!(
                                    "Invalid hour(s) in period {:?}: {:?}",
                                    period_str, e
                                ))
                            })?
                        + MN * cap
                            .name("m")
                            .map_or("0", |m| m.as_str())
                            .parse::<u64>()
                            .map_err(|e| {
                                ZFuelError::Generic(format!(
                                    "Invalid minute(s) in period {:?}: {:?}",
                                    period_str, e
                                ))
                            })?
                        + cap
                            .name("s")
                            .map_or_else(
                                || cap.name("s_man").map_or("0", |s_man| s_man.as_str()),
                                |s| s.as_str(),
                            )
                            .parse::<u64>()
                            .map_err(|e| {
                                ZFuelError::Generic(format!(
                                    "Invalid seconds in period {:?}: {:?}",
                                    period_str, e
                                ))
                            })?;
                    let nanos: u64 = cap
                        .name("s_fra")
                        .map_or(Ok(0_u64), |s_fra| {
                            // ".5" ==> "500000000" (truncate/fill to exactly 9 width)
                            format!("{:0<9.9}", s_fra.as_str()).parse::<u64>()
                        })
                        .map_err(|e| {
                            ZFuelError::Generic(format!(
                                "Invalid fractional seconds in period {:?}: {:?}",
                                period_str, e
                            ))
                        })?
                        + 1_000_000
                            * cap
                                .name("ms")
                                .map_or("0", |ms| ms.as_str())
                                .parse::<u64>()
                                .map_err(|e| {
                                    ZFuelError::Generic(format!(
                                        "Invalid milliseconds in period {:?}: {:?}",
                                        period_str, e
                                    ))
                                })?
                        + 1_000
                            * cap
                                .name("us")
                                .map_or("0", |us| us.as_str())
                                .parse::<u64>()
                                .map_err(|e| {
                                    ZFuelError::Generic(format!(
                                        "Invalid microseconds in period {:?}: {:?}",
                                        period_str, e
                                    ))
                                })?
                        + cap
                            .name("ns")
                            .map_or("0", |ns| ns.as_str())
                            .parse::<u64>()
                            .map_err(|e| {
                                ZFuelError::Generic(format!(
                                    "Invalid nanoseconds in period {:?}: {:?}",
                                    period_str, e
                                ))
                            })?;
                    // Migrate nanoseconds beyond 1s into seconds, to support specifying larger
                    // Periods in terms of ms, us or ns.
                    Ok(Duration::new(
                        seconds + nanos / 1_000_000_000,
                        (nanos % 1_000_000_000) as u32,
                    ))
                },
            )?
        }))
    }
}

impl TryFrom<String> for Period {
    type Error = ZFuelError;
    fn try_from(s: String) -> Result<Self, Self::Error> {
        Period::from_str(&s)
    }
}

impl TryFrom<&str> for Period {
    type Error = ZFuelError;
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        Period::from_str(s)
    }
}

// // Conversion of a Period into a Timeout, in ms.  This is an infallible conversion; if the number of
// // ms. exceeds the capacity of a usize, default to the maximum possible duration.  Since usize is
// // likely a 64-bit value, this will essentially be forever.  Even on 32-bit systems, it will be a
// // long duration, but not forever: 2^32/1000 =~= 2^22 seconds =~= 48 days.  We don't want to use
// // Duration.as_millis(), because its u128 return type are not supported by WASM.
// impl From<Period> for Timeout {
//     fn from(p: Period) -> Self {
//         Timeout(if p.0.as_secs() as usize >= usize::max_value() / 1000 {
//             // The # of seconds overflows the ms-capacity of a usize.  Eg. say a usize could only
//             // contain 123,000 ms.; if the number of seconds was >= 123, then 123 * 1000 + 999 ==
//             // 123,999 would overflow the capacity, while 122,999 wouldn't.
//             usize::max_value()
//         } else {
//             // We know that secs + 1000 * millis won't overflow a usize.
//             (p.0.as_secs() as usize) * 1000 + (p.0.subsec_millis() as usize)
//         })
//     }
// }

// Period --> std::time::Duration
impl From<Period> for Duration {
    fn from(p: Period) -> Self {
        p.0
    }
}

impl From<&Period> for Duration {
    fn from(p: &Period) -> Self {
        p.0.to_owned()
    }
}

// std::time::Duration --> Period
impl From<Duration> for Period {
    fn from(d: Duration) -> Self {
        Period(d)
    }
}

impl From<&Duration> for Period {
    fn from(d: &Duration) -> Self {
        Period(d.to_owned())
    }
}

/*
/// Timestamp +- Into<Period>: Add anything that can be converted into a std::time::Duration; for
/// example, a Timeout or a Period.  On Err, always represents the std::time::Duration as a Period
/// for ease of interpretation.
impl<D: Into<Timestamp>> Add<D> for Period {
    type Output = Timestamp;
    fn add(self, rhs: D) -> Self::Output {
        let dur: Duration = self.into();
        let rhs: Timestamp = rhs.into();
        Timestamp(dur.as_secs() as i64 + rhs.0, rhs.1)
    }
}

impl<D: Into<Timestamp>> Add<D> for &Period {
    type Output = Timestamp;
    fn add(self, rhs: D) -> Self::Output {
        self.to_owned() + rhs
    }
}
*/
