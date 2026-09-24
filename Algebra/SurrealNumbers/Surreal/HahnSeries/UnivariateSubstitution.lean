import Surreal.HahnSeries.MvComposition
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Univariate substitution into multivariate Hahn evaluation

Multivariate evaluation on the single variable `Unit` agrees with native
univariate evaluation. The proof reindexes the finite coefficient sums by
the equivalence between `Unit →₀ ℕ` and `ℕ`. Thus a zero-constant multivariate
series can be substituted into a univariate series before or after evaluation.
It connects the evaluation clauses of `a:cor:complexsub` to univariate calculus.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ R : Type*} [AddCommMonoid Γ] [LinearOrder Γ]
  [IsOrderedCancelAddMonoid Γ] [CommRing R]

/-- The multivariate and univariate constructions agree on the single variable. -/
theorem mvEvaluate_unit (x : R⟦Γ⟧) (hx : 0 < x.orderTop) (f : PowerSeries R) :
    mvEvaluate (fun _ : Unit => x) (fun _ => hx) f = evaluate x hx f := by
  classical
  apply _root_.HahnSeries.ext
  funext g
  rw [coeff_mvEvaluate, coeff_evaluate]
  apply finsum_eq_of_bijective (Finsupp.uniqueEquiv () : (Unit →₀ ℕ) ≃ ℕ)
    (Finsupp.uniqueEquiv ()).bijective
  intro d
  rw [← PowerSeries.coeff_def (R := R) (s := d) rfl]
  simp

/-- Univariate substitution into a zero-constant multivariate inner series
commutes with admissible Hahn evaluation. -/
theorem mvEvaluate_powerSeries_subst {σ : Type*} [Fintype σ]
    (x : σ → R⟦Γ⟧) (hx : ∀ i, 0 < (x i).orderTop)
    (B : MvPowerSeries σ R) (hB : MvPowerSeries.constantCoeff B = 0)
    (f : PowerSeries R) :
    mvEvaluate x hx (PowerSeries.subst B f) =
      evaluate (mvEvaluate x hx B)
        (orderTop_mvEvaluate_pos_of_constantCoeff_zero x hx B hB) f := by
  rw [PowerSeries.subst_def, mvEvaluate_subst x hx f (fun _ => B) (fun _ => hB)]
  exact mvEvaluate_unit _ _ f

end

end Surreal.HahnSeries
