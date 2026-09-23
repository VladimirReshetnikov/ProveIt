import Surreal.Surcomplex.ExpLog
import Surreal.Surcomplex.PowerSeriesTruncation
import Surreal.Surcomplex.Valuation

/-!
# The first-order factor of the actual infinitesimal exponential

The exact finite factor of `Ex(x)-1` has standard part one. This is the
local complex relative-error input to `trigonometry:cor:phaseisometry`.
-/

universe u

namespace Surreal.Surcomplex

noncomputable section

/-- Removing the linear infinitesimal scale leaves a finite factor of residue one. -/
theorem infExp_sub_one_leading_factor (x : Surcomplex.{u}) (hx : IsInfinitesimal x) :
    ∃ R : Surcomplex.{u}, IsFinite R ∧ standardPart R = 1 ∧ infExp x hx - 1 = x * R := by
  obtain ⟨R, hR, hr, he⟩ := exists_finite_powerSeries_remainder x hx (PowerSeries.exp ℂ) 1
  norm_num [Finset.sum_range_succ, PowerSeries.coeff_exp] at hr he
  exact ⟨R, hR, hr, by change powerSeriesEvaluation x hx (PowerSeries.exp ℂ) - 1 = _; rw [he]; ring⟩

/-- The exponential displacement preserves exact valuation at every infinitesimal, including zero. -/
theorem valuation_infExp_sub_one (x : Surcomplex.{u}) (hx : IsInfinitesimal x) :
    valuation (infExp x hx - 1) = valuation x := by
  obtain ⟨R, hR, hr, he⟩ := infExp_sub_one_leading_factor x hx
  have hv := (valuation_eq_zero_iff_standardPart_ne_zero hR).mpr (by rw [hr]; norm_num)
  rw [he, valuation_mul, hv, add_zero]

/-- The complex relative error from the linear term is infinitesimal. -/
theorem infinitesimal_infExp_sub_one_div_sub_one (x : Surcomplex.{u})
    (hx : IsInfinitesimal x) (hne : x ≠ 0) : IsInfinitesimal ((infExp x hx - 1) / x - 1) := by
  obtain ⟨R, hR, hr, he⟩ := infExp_sub_one_leading_factor x hx
  rw [he, mul_div_cancel_left₀ _ hne]
  simpa only [hr, map_one] using infinitesimal_sub_standardPart hR

end
end Surreal.Surcomplex
