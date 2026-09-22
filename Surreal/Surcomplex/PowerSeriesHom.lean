import Surreal.Algebra.PowerSeriesHom
import Surreal.Foundations.SignSequencePowerSeries
import Surreal.Surcomplex.PowerSeries

/-!
# Actual formal evaluation: injectivity and the infinitesimal criterion

The algebraic clauses of `thm:exact` in the evaluation-at-omega report:
an actual surreal is the image of the formal variable under a homomorphism
from rational formal series exactly when it is infinitesimal. The analogous
criterion for real coefficients includes a coefficient-fixing witness.
Nonzero infinitesimal evaluation is injective, and its valuation is determined
by the first nonzero formal degree.

Strong additivity and uniqueness among strongly additive homomorphisms are
separate obligations; no uniqueness among arbitrary ring maps is claimed.
-/

universe u v

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- Every formal-variable image in the actual ordered field is infinitesimal. -/
theorem isInfinitesimal_map_powerSeries_X {K : Type v} [Field K] [CharZero K]
    (φ : PowerSeries K →+* SignSequence.{u}) : IsInfinitesimal (φ PowerSeries.X) := by
  rw [isInfinitesimal_iff_forall_nat_abs_lt]
  exact Surreal.FormalPowerSeries.abs_map_X_lt_one_div φ

/-- A surreal is a possible rational formal-variable image exactly when infinitesimal. -/
theorem exists_rat_powerSeriesHom_iff (x : SignSequence.{u}) :
    (∃ φ : PowerSeries ℚ →+* SignSequence.{u}, φ PowerSeries.X = x) ↔
      IsInfinitesimal x := by
  constructor
  · rintro ⟨φ, rfl⟩
    exact isInfinitesimal_map_powerSeries_X φ
  · intro hx
    refine ⟨(powerSeriesEvaluation x hx).comp (PowerSeries.map (algebraMap ℚ ℝ)), ?_⟩
    simp only [RingHom.comp_apply, PowerSeries.map_X, powerSeriesEvaluation_X]

/-- The real-coefficient criterion includes a homomorphism fixing every ordinary real. -/
theorem exists_real_powerSeriesHom_iff (x : SignSequence.{u}) :
    (∃ φ : PowerSeries ℝ →+* SignSequence.{u},
      φ PowerSeries.X = x ∧ ∀ r, φ (PowerSeries.C r) = ofReal r) ↔
      IsInfinitesimal x := by
  constructor
  · rintro ⟨φ, hx, _⟩
    rw [← hx]
    exact isInfinitesimal_map_powerSeries_X φ
  · intro hx
    exact ⟨powerSeriesEvaluation x hx, powerSeriesEvaluation_X x hx,
      powerSeriesEvaluation_C x hx⟩

/-- Actual evaluation at a nonzero infinitesimal is injective. -/
theorem powerSeriesEvaluation_injective (x : SignSequence.{u}) (hx : IsInfinitesimal x)
    (hne : x ≠ 0) : Function.Injective (powerSeriesEvaluation x hx) :=
  Surreal.FormalPowerSeries.injective_of_X_ne_zero _
    (by simpa only [powerSeriesEvaluation_X] using hne)

/-- Evaluation has trivial kernel exactly for the nonzero infinitesimal arguments. -/
theorem powerSeriesEvaluation_injective_iff (x : SignSequence.{u}) (hx : IsInfinitesimal x) :
    Function.Injective (powerSeriesEvaluation x hx) ↔ x ≠ 0 := by
  constructor
  · intro hi hzero
    have h : powerSeriesEvaluation x hx PowerSeries.X = powerSeriesEvaluation x hx 0 := by
      rw [powerSeriesEvaluation_X, map_zero, hzero]
    exact PowerSeries.X_ne_zero (hi h)
  · exact powerSeriesEvaluation_injective x hx

/-- The first nonzero formal degree determines the actual valuation, including
zero input and constant-term cases. -/
theorem valuation_powerSeriesEvaluation (x : SignSequence.{u}) (hx : IsInfinitesimal x)
    (f : PowerSeries ℝ) (hf : f ≠ 0) :
    valuation (powerSeriesEvaluation x hx f) = f.order.toNat • valuation x := by
  have hv : valuation (powerSeriesEvaluation x hx (PowerSeries.divXPowOrder f)) = 0 := by
    apply le_antisymm
    · apply le_of_not_gt
      rw [← isInfinitesimal_iff_valuation_pos, isInfinitesimal_powerSeriesEvaluation_iff,
        PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff]
      exact hf
    · exact (isFinite_iff_valuation_nonneg _).mp (isFinite_powerSeriesEvaluation x hx _)
  conv_lhs => rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f := f)]
  rw [map_mul, map_pow, powerSeriesEvaluation_X, valuation_mul, valuation.map_pow, hv, _root_.add_zero]

end
end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex

noncomputable section

/-- Complex formal evaluation at a nonzero infinitesimal is injective. -/
theorem powerSeriesEvaluation_injective (x : Surcomplex.{u}) (hx : IsInfinitesimal x)
    (hne : x ≠ 0) : Function.Injective (powerSeriesEvaluation x hx) :=
  Surreal.FormalPowerSeries.injective_of_X_ne_zero _
    (by simpa only [powerSeriesEvaluation_X] using hne)

/-- Injectivity fails exactly at the zero argument. -/
theorem powerSeriesEvaluation_injective_iff (x : Surcomplex.{u}) (hx : IsInfinitesimal x) :
    Function.Injective (powerSeriesEvaluation x hx) ↔ x ≠ 0 := by
  constructor
  · intro hi hzero
    have h : powerSeriesEvaluation x hx PowerSeries.X = powerSeriesEvaluation x hx 0 := by
      rw [powerSeriesEvaluation_X, map_zero, hzero]
    exact PowerSeries.X_ne_zero (hi h)
  · exact powerSeriesEvaluation_injective x hx

/-- The complex valuation is the formal order times the input valuation. -/
theorem valuation_powerSeriesEvaluation (x : Surcomplex.{u}) (hx : IsInfinitesimal x)
    (f : PowerSeries ℂ) (hf : f ≠ 0) :
    valuation (powerSeriesEvaluation x hx f) = f.order.toNat • valuation x := by
  have hv : valuation (powerSeriesEvaluation x hx (PowerSeries.divXPowOrder f)) = 0 := by
    apply (valuation_eq_zero_iff_standardPart_ne_zero (isFinite_powerSeriesEvaluation x hx _)).mpr
    rw [standardPart_powerSeriesEvaluation, ne_eq, PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff]
    exact hf
  conv_lhs => rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f := f)]
  rw [map_mul, map_pow, powerSeriesEvaluation_X, valuation_mul, valuation.map_pow, hv, _root_.add_zero]

end
end Surreal.Surcomplex
