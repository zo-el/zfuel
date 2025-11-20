//! Implements fee calculation.  The fee structure of Fuel may change over time, but not between
//! roll-outs of new Fuel DNAs.  Therefore, its values and limits can be hard-coded here.

use crate::error::ZFuelError;
use crate::fraction::Fraction;
use crate::fuel::ZFuel;

// ==> 1.0% fee
pub const FEE_PERCENTAGE: Fraction = Fraction {
    numerator: 1,
    denominator: 100,
};

/// tabulate_fee -- compute simple Transaction Fee from amount-based tables
/// Note: Changes to the fee calculation in the future should not lead to overflow panics.
pub fn tabulate_fee(amount: &ZFuel) -> Result<ZFuel, ZFuelError> {
    let fee = (amount * FEE_PERCENTAGE)?;
    Ok(fee)
}

#[cfg(test)]
pub mod tests {
    use crate::fee::*;
    use crate::fuel::Precision;

    /// smoke test Fuel fees
    #[test]
    fn fee_smoke_test() {
        let fee_tab = tabulate_fee(&ZFuel {
            units: 1_230_000,
            precision: Precision::DEFAULT,
        })
        .unwrap();
        assert_eq!(
            fee_tab,
            ZFuel {
                units: 12_300,
                precision: Precision::DEFAULT
            }
        );
    }
}
