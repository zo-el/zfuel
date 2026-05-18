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
    use crate::fuel::{Precision, MAXVALUE, MINVALUE};
    use std::str::FromStr;

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

    #[test]
    fn fee_on_zero_is_zero() {
        let fee = tabulate_fee(&ZFuel::zero()).unwrap();
        assert_eq!(fee.units, 0);
    }

    #[test]
    fn fee_on_negative_amount_is_negative() {
        // Round-up is "away from zero", so for negatives this rounds *down* (more negative).
        let amount = ZFuel::new(-1_230_000, Precision::DEFAULT).unwrap();
        let fee = tabulate_fee(&amount).unwrap();
        assert_eq!(fee.units, -12_300);
    }

    #[test]
    fn fee_on_maxvalue_does_not_overflow() {
        let amount = ZFuel::new(MAXVALUE, Precision::DEFAULT).unwrap();
        let fee = tabulate_fee(&amount).unwrap();
        // 1% of MAXVALUE rounded up away from zero
        // MAXVALUE / 100 = 92233720368547758 r 7, so +1 -> 92233720368547759
        assert_eq!(fee.units, 92_233_720_368_547_759);
    }

    #[test]
    fn fee_on_minvalue_does_not_overflow() {
        let amount = ZFuel::new(MINVALUE, Precision::DEFAULT).unwrap();
        let fee = tabulate_fee(&amount).unwrap();
        // 1% of MINVALUE rounded up (away from zero, so more negative)
        // MINVALUE / 100 = -92233720368547758 r -8, so -1 -> -92233720368547759
        assert_eq!(fee.units, -92_233_720_368_547_759);
    }

    #[test]
    fn fee_rounds_up_for_sub_unit_amounts() {
        // Below 100 units, exact 1% would be a fractional fraction-unit; we round up.
        // 1 unit (0.000001 ZFuel): 1% = 0.00000001, rounded up -> 1 unit
        let fee = tabulate_fee(&ZFuel::new(1, Precision::DEFAULT).unwrap()).unwrap();
        assert_eq!(fee.units, 1);

        // 50 units: 1% = 0.5 units, rounded up -> 1 unit
        let fee = tabulate_fee(&ZFuel::new(50, Precision::DEFAULT).unwrap()).unwrap();
        assert_eq!(fee.units, 1);

        // 99 units: 1% = 0.99 units, rounded up -> 1 unit
        let fee = tabulate_fee(&ZFuel::new(99, Precision::DEFAULT).unwrap()).unwrap();
        assert_eq!(fee.units, 1);

        // 100 units: exactly 1 unit, no rounding
        let fee = tabulate_fee(&ZFuel::new(100, Precision::DEFAULT).unwrap()).unwrap();
        assert_eq!(fee.units, 1);

        // 101 units: 1.01 units -> rounded up to 2
        let fee = tabulate_fee(&ZFuel::new(101, Precision::DEFAULT).unwrap()).unwrap();
        assert_eq!(fee.units, 2);
    }

    #[test]
    fn fee_preserves_precision_default() {
        // Multiplication by a Fraction always produces a value at Precision::DEFAULT (6),
        // regardless of input precision, so the fractional result is representable.
        let amount = ZFuel::from_str("100").unwrap(); // precision 0
        let fee = tabulate_fee(&amount).unwrap();
        assert_eq!(fee.precision, Precision::DEFAULT);
        assert_eq!(fee.units, 1_000_000); // 1.000000
    }

    #[test]
    fn fee_is_one_percent_for_round_values() {
        // 100.000000 -> 1.000000
        let amount = ZFuel::new(100_000_000, Precision::DEFAULT).unwrap();
        let fee = tabulate_fee(&amount).unwrap();
        assert_eq!(format!("{}", fee), "1");

        // 1234.560000 -> 12.345600
        let amount = ZFuel::new(1_234_560_000, Precision::DEFAULT).unwrap();
        let fee = tabulate_fee(&amount).unwrap();
        assert_eq!(format!("{}", fee), "12.3456");
    }

    #[test]
    fn fee_on_small_negative_value_rounds_away_from_zero() {
        // Regression: previously the rounding logic in Mul<Fraction> branched on the quotient's
        // sign. For a small-negative product (quotient == 0, remainder < 0), it returned +1
        // instead of -1, producing a positive fee for a negative amount.
        use crate::fuel::ZFuel;
        let amount = ZFuel::new(-2, Precision::new(5).unwrap()).unwrap();
        let fee = tabulate_fee(&amount).unwrap();
        // 1% of -2 at precision 5 means: scale -2 at p5 to p6 (= -20), then * 1/100.
        // Exact value: -20 / 100 = -0.2, rounded away from zero -> -1 unit at p6.
        assert!(fee.units < 0, "expected negative fee, got {}", fee.units);
        assert_eq!(fee.units, -1);
    }

    #[test]
    fn fee_works_across_input_precisions() {
        // Same nominal value at different input precisions should yield equivalent fees
        let amount_p0 = ZFuel::new(100, Precision::new(0).unwrap()).unwrap(); // 100
        let amount_p2 = ZFuel::new(10000, Precision::new(2).unwrap()).unwrap(); // 100.00
        let amount_p6 = ZFuel::new(100_000_000, Precision::DEFAULT).unwrap(); // 100.000000

        let f0 = tabulate_fee(&amount_p0).unwrap();
        let f2 = tabulate_fee(&amount_p2).unwrap();
        let f6 = tabulate_fee(&amount_p6).unwrap();

        assert_eq!(f0, f2);
        assert_eq!(f2, f6);
    }
}
