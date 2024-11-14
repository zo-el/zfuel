//! Custom error types for ZFuel transactions
use crate::fraction::Fraction;
use crate::fuel::ZFuel;
use hdi::prelude::*;
use std::fmt;

#[derive(thiserror::Error, Debug, Clone)]
pub enum ZFuelError {
    Range(String),                       // ZFuel range exceeded
    FractionOverflow((ZFuel, Fraction)), // Overflow in ZFuel * Fraction
    // LimitExceeded((Limit, String, Delta)), // An account Limit was exceeded by ZFuel value, by the given transaction Delta
    // AgentDenied(Limit), // All transactions w/ counterparty are denied
    Generic(String), // we want to avoid this one if at all possible and add a new error variant instead
}

// All ZFuelError display logic is in one place which is here
impl fmt::Display for ZFuelError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ZFuelError::Range(s) => write!(f, "ZFuel Range Error: {}", s),
            ZFuelError::FractionOverflow((fuel, fraction)) => {
                write!(f, "ZFuel overflow in ♓{} * {}", fuel, fraction)
            }
            // ZFuelError::LimitExceeded((limit, total, change)) => write!(
            //     f,
            //     "ZFuel Limit {} exceeded with duration total ♓{}, by tx. ♓{}, on {:?}",
            //     limit, total, change.1, change.0
            // ),
            // ZFuelError::AgentDenied(limit) => write!(
            //     f,
            //     "ZFuel Limit {} denies any counterparty transaction",
            //     limit
            // ),
            ZFuelError::Generic(s) => write!(f, "ZFuel Error: {}", s),
        }
    }
}

pub type ZFuelResult<T> = Result<T, ZFuelError>;
impl From<ZFuelError> for WasmError {
    fn from(c: ZFuelError) -> Self {
        wasm_error!(WasmErrorInner::Guest(format!("{:?}", c)))
    }
}
