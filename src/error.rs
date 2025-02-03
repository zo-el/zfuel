//! Custom error types for Fuel transactions
use crate::fraction::Fraction;
use crate::fuel::ZFuel;
use holochain_wasmer_common::{wasm_error, WasmError};
use std::fmt;

#[derive(thiserror::Error, Debug, Clone)]
pub enum ZFuelError {
    Range(String),                       // Fuel range exceeded
    FractionOverflow((ZFuel, Fraction)), // Overflow in Fuel * Fraction
    // AgentDenied(Limit),                 // All transactions w/ counterparty are denied
    // LimitExceeded((Limit, String, Delta)), // An account Limit was exceeded by Fuel value, by the given transaction Delta
    // AgentDenied(Limit), // All transactions w/ counterparty are denied
    Generic(String), // we want to avoid this one if at all possible and add a new error variant instead
}

// All ZFuelError display logic is in one place which is here
impl fmt::Display for ZFuelError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ZFuelError::Range(s) => write!(f, "Fuel Range Error: {}", s),
            ZFuelError::FractionOverflow((fuel, fraction)) => {
                write!(f, "Fuel overflow in ♓{} * {}", fuel, fraction)
            }
            // ZFuelError::AgentDenied(limit) => write!(
            //     f,
            //     "Fuel Limit {} denies any counterparty transaction",
            //     limit
            // ),
            // ZFuelError::LimitExceeded((limit, total, change)) => write!(
            //     f,
            //     "Fuel Limit {} exceeded with duration total ♓{}, by tx. ♓{}, on {:?}",
            //     limit, total, change.1, change.0
            // ),
            // ZFuelError::AgentDenied(limit) => write!(
            //     f,
            //     "Fuel Limit {} denies any counterparty transaction",
            //     limit
            // ),
            ZFuelError::Generic(s) => write!(f, "Fuel Error: {}", s),
        }
    }
}

pub type FuelResult<T> = Result<T, ZFuelError>;
impl From<ZFuelError> for WasmError {
    fn from(c: ZFuelError) -> Self {
        wasm_error!(format!("{:?}", c))
    }
}
