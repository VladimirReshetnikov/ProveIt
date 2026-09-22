import Surreal.Surcomplex.PowerSeriesStrongHom

/-!
# The real-algebra clause of formal evaluation

The ordinary real embedding supplies the coefficient algebra used here.
With that structure explicit, infinitesimal evaluation is a native Mathlib
algebra homomorphism, and an actual surreal occurs as the image of its formal
variable exactly when infinitesimal. This is clause (iv) of `thm:exact` in
the Hahn-evaluation-at-omega report. The preceding strongly additive theorem
supplies clause (iii); uniqueness is not asserted for arbitrary algebra maps.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- The ordinary-real coefficient algebra on the actual sign field. -/
abbrev powerSeriesCoefficientAlgebra : Algebra ℝ SignSequence.{u} := ofReal.toAlgebra

attribute [local instance] powerSeriesCoefficientAlgebra

/-- Formal evaluation as a native algebra homomorphism over ordinary real coefficients. -/
def powerSeriesEvaluationAlgHom (x : SignSequence.{u}) (hx : IsInfinitesimal x) :
    PowerSeries ℝ →ₐ[ℝ] SignSequence.{u} where
  __ := powerSeriesEvaluation x hx
  commutes' r := powerSeriesEvaluation_C x hx r

@[simp] theorem powerSeriesEvaluationAlgHom_apply (x : SignSequence.{u})
    (hx : IsInfinitesimal x) (f : PowerSeries ℝ) :
    powerSeriesEvaluationAlgHom x hx f = powerSeriesEvaluation x hx f := rfl

/-- The algebra-homomorphism clause in the exact variable-image criterion. -/
theorem exists_real_powerSeriesAlgHom_iff (x : SignSequence.{u}) :
    (∃ φ : PowerSeries ℝ →ₐ[ℝ] SignSequence.{u}, φ PowerSeries.X = x) ↔
      IsInfinitesimal x := by
  constructor
  · rintro ⟨φ, hx⟩
    rw [← hx]
    exact isInfinitesimal_map_powerSeries_X φ.toRingHom
  · intro hx
    exact ⟨powerSeriesEvaluationAlgHom x hx, powerSeriesEvaluation_X x hx⟩

/-- All four alternatives in the source theorem coincide on the actual carrier. -/
theorem powerSeries_variable_image_equivalences (x : SignSequence.{u}) :
    ((∃ φ : PowerSeries ℚ →+* SignSequence.{u}, φ PowerSeries.X = x) ↔ IsInfinitesimal x) ∧
    (IsInfinitesimal x ↔ ∃ φ : PowerSeries ℝ →+* SignSequence.{u},
      φ PowerSeries.X = x ∧ (∀ c, φ (PowerSeries.C c) = ofReal c) ∧
        PowerSeriesStronglyAdditive φ) ∧
    (IsInfinitesimal x ↔ ∃ φ : PowerSeries ℝ →ₐ[ℝ] SignSequence.{u},
      φ PowerSeries.X = x) :=
  ⟨exists_rat_powerSeriesHom_iff x, (exists_powerSeriesStrongHom_iff x).symm,
    (exists_real_powerSeriesAlgHom_iff x).symm⟩

end
end Surreal.Foundations.SignSequence
