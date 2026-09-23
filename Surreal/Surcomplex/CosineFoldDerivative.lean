import Surreal.Surcomplex.CosineFoldSeries
import Surreal.Surcomplex.PowerSeriesDerivative

/-!
# Actual derivatives and the double-zero series of the cosine fold

The formal derivative evaluates to the actual fine derivative at every
infinitesimal angle. Separated roots have nonzero derivative, while the
zero-parameter series has native formal order two. These are analytic
prerequisites for `trigonometry:thm:fold`. The polynomial-coordinate
convention for angular multiplicity still requires a separate bridge.
-/

universe u

namespace Surreal.Surcomplex.CosineFold

open Foundations

noncomputable section

/-- The actual fine derivative of the cosine germ is minus the sine germ. -/
theorem fineHasDerivAt_cos (θ : Surcomplex.{u}) (hθ : IsInfinitesimal θ) :
    FineHasDerivAt (powerSeriesFunction Analytic.complexCosSeries) (-infSin θ hθ) θ := by
  have h := fineHasDerivAt_powerSeriesFunction Analytic.complexCosSeries θ hθ
  rw [Analytic.derivative_complexCosSeries, map_neg] at h
  exact h

/-- Every separated root has a nonzero actual fine derivative. -/
theorem derivative_ne_zero_at_root (τ θ : Surcomplex.{u}) (hτ : IsInfinitesimal τ)
    (hτ0 : τ ≠ 0) (hθ : IsInfinitesimal θ) (he : infCos θ hθ = 1 - τ) :
    -infSin θ hθ ≠ 0 := by
  obtain ⟨s, hs, hsq⟩ := exists_infinitesimal_sq_eq (τ / 2) (infinitesimal_div_two hτ)
  rcases (solutions_iff τ s θ hs hsq hθ).mp he with h | h
  · subst θ
    exact neg_ne_zero.mpr (sin_branch_ne_zero τ s hs hsq hτ0)
  · subst θ
    rw [infSin_neg, neg_neg]
    exact sin_branch_ne_zero τ s hs hsq hτ0

/-- The zero-parameter ordinary formal germ has exact order two. -/
theorem collision_series_order : (Analytic.complexCosSeries - 1).order = 2 := by
  apply PowerSeries.order_eq_nat.mpr
  constructor
  · norm_num [map_sub, Analytic.coeff_complexCosSeries_two, PowerSeries.coeff_one]
  · intro n hn
    interval_cases n
    · simp [PowerSeries.coeff_zero_eq_constantCoeff]
    · simp

/-- The order-two statement holds as well after embedding all coefficients in the actual field. -/
theorem actual_collision_series_order :
    (PowerSeries.map (ofComplex : ℂ →+* Surcomplex.{u}) (Analytic.complexCosSeries - 1)).order = 2 := by
  apply PowerSeries.order_eq_nat.mpr
  have ho := PowerSeries.order_eq_nat.mp collision_series_order
  constructor
  · simpa only [PowerSeries.coeff_map, ne_eq, map_eq_zero] using ho.1
  · intro n hn
    simp only [PowerSeries.coeff_map, ho.2 n hn, map_zero]

/-- The zero-parameter double root has an exact quadratic factor with nonzero residue. -/
theorem collision_exact_factor (θ : Surcomplex.{u}) (hθ : IsInfinitesimal θ) :
    ∃ R : Surcomplex.{u}, IsFinite R ∧ standardPart R = -(1 / 2 : ℂ) ∧ R ≠ 0 ∧
      infCos θ hθ - 1 = θ ^ 2 * R := by
  obtain ⟨R, hR, hr, he⟩ := exists_finite_powerSeries_remainder θ hθ
    (Analytic.complexCosSeries - 1) 2
  have hc : (Analytic.complexCosSeries - 1).coeff 2 = -(1 / 2 : ℂ) := by
    simp [Analytic.coeff_complexCosSeries_two]
  rw [hc] at hr
  have hn : R ≠ 0 := by
    intro hz
    have hh := congrArg Complex.re hr
    simp [hz, standardPart] at hh
  refine ⟨R, hR, hr, hn, ?_⟩
  simpa [Finset.sum_range_succ, PowerSeries.coeff_zero_eq_constantCoeff,
    infCos] using he

/-- The exact first-order expansion around any infinitesimal center has a finite tail. -/
theorem local_exact_expansion (θ h : Surcomplex.{u})
    (hθ : IsInfinitesimal θ) (hh : IsInfinitesimal h) :
    ∃ R : Surcomplex.{u}, IsFinite R ∧
      infCos (θ + h) (infinitesimal_add hθ hh) =
        infCos θ hθ - infSin θ hθ * h + h ^ 2 * R := by
  refine ⟨powerSeriesTranslationRemainder Analytic.complexCosSeries θ h hθ hh, ?_, ?_⟩
  · exact isFinite_mvPowerSeriesEvaluation _ _ _
  · have he := powerSeriesEvaluation_add_eq_linear_add_sq_mul Analytic.complexCosSeries θ h hθ hh
    rw [Analytic.derivative_complexCosSeries, map_neg] at he
    simpa only [infCos, infSin, neg_mul, sub_eq_add_neg] using he

end
end Surreal.Surcomplex.CosineFold
