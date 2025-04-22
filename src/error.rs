//! Custom error types for Fuel transactions
use crate::fraction::Fraction;
use crate::fuel::ZFuel;
use holochain_wasmer_common::{wasm_error, WasmError};
use std::fmt;

#[derive(thiserror::Error, Debug, Clone)]
pub enum ZFuelError {
    Range(String),                       // Fuel range exceeded
    FractionOverflow((ZFuel, Fraction)), // Overflow in Fuel * Fraction
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
