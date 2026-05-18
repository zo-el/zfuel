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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fuel::{Precision, ZFuel};

    #[test]
    fn range_display_includes_prefix_and_message() {
        let e = ZFuelError::Range("foo".to_string());
        assert_eq!(format!("{}", e), "Fuel Range Error: foo");
    }

    #[test]
    fn generic_display_includes_prefix_and_message() {
        let e = ZFuelError::Generic("bar".to_string());
        assert_eq!(format!("{}", e), "Fuel Error: bar");
    }

    #[test]
    fn fraction_overflow_display_renders_fuel_and_fraction() {
        let fuel = ZFuel::new(100, Precision::DEFAULT).unwrap();
        let fraction = Fraction::new(35, 1000).unwrap();
        let e = ZFuelError::FractionOverflow((fuel, fraction));
        let s = format!("{}", e);
        assert!(s.starts_with("Fuel overflow in"));
        // Display formats the fuel value and the (reduced) fraction
        assert!(s.contains("0.0001"));
        assert!(s.contains("35/1000") || s.contains("7/200"));
    }

    #[test]
    fn errors_are_clonable() {
        let e = ZFuelError::Range("x".into());
        let cloned = e.clone();
        assert_eq!(format!("{}", e), format!("{}", cloned));

        let e = ZFuelError::Generic("y".into());
        let cloned = e.clone();
        assert_eq!(format!("{}", e), format!("{}", cloned));

        let e = ZFuelError::FractionOverflow((
            ZFuel::new(1, Precision::DEFAULT).unwrap(),
            Fraction::new(1, 2).unwrap(),
        ));
        let cloned = e.clone();
        assert_eq!(format!("{}", e), format!("{}", cloned));
    }

    #[test]
    fn converts_to_wasm_error() {
        // Conversion must not panic and must produce a WasmError whose payload references the original error
        let e = ZFuelError::Range("oops".to_string());
        let wasm: WasmError = e.into();
        let rendered = format!("{:?}", wasm);
        assert!(rendered.contains("oops"));
    }

    #[test]
    fn implements_std_error_trait() {
        // thiserror auto-impls std::error::Error; verify it is usable as a trait object
        fn _accepts_error<E: std::error::Error>(_: &E) {}
        let e = ZFuelError::Generic("z".into());
        _accepts_error(&e);
    }
}
