import Surreal.Surcomplex.PowerSeriesHom
import Surreal.Surcomplex.Leading

/-!
# Leading data of actual formal-series evaluation

For a nonzero formal series with first degree `m`, evaluation at an actual
infinitesimal has leading coefficient `coeff m f * leadingCoeff x ^ m`.
For nonzero input its leading growth exponent is `m • leadingExponent x`.
These are the explicit leading-term claims in `rem:leading-inj` of the
Hahn-evaluation-at-omega report, in both actual fields.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

@[simp] theorem leadingCoeff_pow (x : SignSequence.{u}) (n : ℕ) :
    leadingCoeff (x ^ n) = leadingCoeff x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ, leadingCoeff_mul, ih]

/-- At valuation zero the leading coefficient is exactly the ordinary residue. -/
theorem leadingCoeff_eq_standardPart_of_valuation_zero (x : SignSequence.{u})
    (hx : valuation x = 0) : leadingCoeff x = standardPart x := by
  have hne : x ≠ 0 := by
    intro h
    rw [h, valuation_zero] at hx
    exact WithTop.top_ne_coe hx
  have he : leadingExponent x = 0 := by
    rw [valuation_of_ne_zero hne] at hx
    exact neg_eq_zero.mp (WithTop.coe_eq_zero.mp hx)
  rw [leadingCoeff_eq_standardPart, he, omegaPower_zero, div_one]

/-- The leading coefficient of evaluated nonzero formal data. Zero input is included. -/
theorem leadingCoeff_powerSeriesEvaluation (x : SignSequence.{u}) (hx : IsInfinitesimal x)
    (f : PowerSeries ℝ) (hf : f ≠ 0) :
    leadingCoeff (powerSeriesEvaluation x hx f) =
      f.coeff f.order.toNat * leadingCoeff x ^ f.order.toNat := by
  have hu := PowerSeries.isUnit_divided_by_X_pow_order hf
  have hv : valuation (powerSeriesEvaluation x hx (PowerSeries.divXPowOrder f)) = 0 := by
    rw [valuation_powerSeriesEvaluation x hx _ hu.ne_zero,
      PowerSeries.order_zero_of_unit hu, ENat.toNat_zero, zero_nsmul]
  have hc := leadingCoeff_eq_standardPart_of_valuation_zero _ hv
  rw [standardPart_powerSeriesEvaluation, PowerSeries.constantCoeff_divXPowOrder] at hc
  conv_lhs => rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f := f)]
  rw [map_mul, map_pow, powerSeriesEvaluation_X, leadingCoeff_mul, leadingCoeff_pow, hc]
  exact mul_comm _ _

/-- Growth exponents multiply by the first nonzero formal degree. -/
theorem leadingExponent_powerSeriesEvaluation (x : SignSequence.{u}) (hx : IsInfinitesimal x)
    (hne : x ≠ 0) (f : PowerSeries ℝ) (hf : f ≠ 0) :
    leadingExponent (powerSeriesEvaluation x hx f) = f.order.toNat • leadingExponent x := by
  have hy : powerSeriesEvaluation x hx f ≠ 0 := by
    intro h
    exact hf (powerSeriesEvaluation_injective x hx hne (h.trans (map_zero _).symm))
  have h := valuation_powerSeriesEvaluation x hx f hf
  rw [valuation_of_ne_zero hy, valuation_of_ne_zero hne, ← WithTop.coe_nsmul] at h
  exact neg_injective (by simpa only [smul_neg] using WithTop.coe_injective h)

end
end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex

noncomputable section

@[simp] theorem leadingCoeff_pow (x : Surcomplex.{u}) (n : ℕ) :
    leadingCoeff (x ^ n) = leadingCoeff x ^ n :=
  leadingCoeffMonoidWithZeroHom.map_pow x n

/-- A valuation-zero surcomplex has its leading coefficient as standard part. -/
theorem leadingCoeff_eq_standardPart_of_valuation_zero (x : Surcomplex.{u})
    (hx : valuation x = 0) : leadingCoeff x = standardPart x := by
  have hne : x ≠ 0 := by
    intro h
    rw [h, valuation_zero] at hx
    exact WithTop.top_ne_coe hx
  have he : leadingExponent x = 0 := by
    rw [valuation_of_ne_zero hne] at hx
    exact neg_eq_zero.mp (WithTop.coe_eq_zero.mp hx)
  rw [leadingCoeff, normalized, he, neg_zero, tMonomial_zero, div_one]

/-- Leading coefficients of evaluated formal data, including zero input. -/
theorem leadingCoeff_powerSeriesEvaluation (x : Surcomplex.{u}) (hx : IsInfinitesimal x)
    (f : PowerSeries ℂ) (hf : f ≠ 0) :
    leadingCoeff (powerSeriesEvaluation x hx f) =
      f.coeff f.order.toNat * leadingCoeff x ^ f.order.toNat := by
  have hu := PowerSeries.isUnit_divided_by_X_pow_order hf
  have hv : valuation (powerSeriesEvaluation x hx (PowerSeries.divXPowOrder f)) = 0 := by
    rw [valuation_powerSeriesEvaluation x hx _ hu.ne_zero,
      PowerSeries.order_zero_of_unit hu, ENat.toNat_zero, zero_nsmul]
  have hc := leadingCoeff_eq_standardPart_of_valuation_zero _ hv
  rw [standardPart_powerSeriesEvaluation, PowerSeries.constantCoeff_divXPowOrder] at hc
  conv_lhs => rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f := f)]
  rw [map_mul, map_pow, powerSeriesEvaluation_X, leadingCoeff_mul, leadingCoeff_pow, hc]
  exact mul_comm _ _

/-- Complex growth exponents obey the same formal-order formula. -/
theorem leadingExponent_powerSeriesEvaluation (x : Surcomplex.{u}) (hx : IsInfinitesimal x)
    (hne : x ≠ 0) (f : PowerSeries ℂ) (hf : f ≠ 0) :
    leadingExponent (powerSeriesEvaluation x hx f) = f.order.toNat • leadingExponent x := by
  have hy : powerSeriesEvaluation x hx f ≠ 0 := by
    intro h
    exact hf (powerSeriesEvaluation_injective x hx hne (h.trans (map_zero _).symm))
  have h := valuation_powerSeriesEvaluation x hx f hf
  rw [valuation_of_ne_zero hy, valuation_of_ne_zero hne, ← WithTop.coe_nsmul] at h
  exact neg_injective (by simpa only [smul_neg, leadingExponent] using WithTop.coe_injective h)

end
end Surreal.Surcomplex
