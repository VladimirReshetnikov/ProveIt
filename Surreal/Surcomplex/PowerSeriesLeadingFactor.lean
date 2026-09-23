import Surreal.Algebra.PowerSeriesLeadingFactor
import Surreal.Surcomplex.PowerSeriesLeading

/-!
# The infinitesimal relative error in actual leading-term evaluation

For both actual fields, every nonzero ordinary-coefficient formal series
is its leading monomial times one plus an actual infinitesimal. This supplies
the relative-error clause of `trigonometry:lem:leading`; the existing valuation
and leading-coefficient formulas supply its remaining clauses.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- The exact evaluated leading monomial has an infinitesimal relative error. -/
theorem exists_infinitesimal_powerSeries_factor (x : SignSequence.{u})
    (hx : IsInfinitesimal x) (f : PowerSeries ℝ) (hf : f ≠ 0) :
    ∃ ξ : SignSequence.{u}, IsInfinitesimal ξ ∧
      powerSeriesEvaluation x hx f =
        ofReal (f.coeff f.order.toNat) * x ^ f.order.toNat * (1 + ξ) := by
  refine ⟨powerSeriesEvaluation x hx (FormalPowerSeries.leadingRemainder f), ?_, ?_⟩
  · exact (isInfinitesimal_powerSeriesEvaluation_iff _ _ _).mpr
      (FormalPowerSeries.constantCoeff_leadingRemainder f hf)
  · have h := congrArg (powerSeriesEvaluation x hx)
      (FormalPowerSeries.eq_leading_mul_one_add_remainder f hf)
    simpa only [map_mul, map_add, map_pow, map_one, powerSeriesEvaluation_C,
      powerSeriesEvaluation_X] using h

end

end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex

noncomputable section

/-- The exact evaluated leading monomial has an infinitesimal relative error. -/
theorem exists_infinitesimal_powerSeries_factor (x : Surcomplex.{u})
    (hx : IsInfinitesimal x) (f : PowerSeries ℂ) (hf : f ≠ 0) :
    ∃ ξ : Surcomplex.{u}, IsInfinitesimal ξ ∧
      powerSeriesEvaluation x hx f =
        ofComplex (f.coeff f.order.toNat) * x ^ f.order.toNat * (1 + ξ) := by
  refine ⟨powerSeriesEvaluation x hx (FormalPowerSeries.leadingRemainder f), ?_, ?_⟩
  · exact (isInfinitesimal_powerSeriesEvaluation_iff _ _ _).mpr
      (FormalPowerSeries.constantCoeff_leadingRemainder f hf)
  · have h := congrArg (powerSeriesEvaluation x hx)
      (FormalPowerSeries.eq_leading_mul_one_add_remainder f hf)
    simpa only [map_mul, map_add, map_pow, map_one, powerSeriesEvaluation_C,
      powerSeriesEvaluation_X] using h

end

end Surreal.Surcomplex
