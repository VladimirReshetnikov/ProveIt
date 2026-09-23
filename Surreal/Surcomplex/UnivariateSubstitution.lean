import Surreal.HahnSeries.UnivariateSubstitution
import Surreal.Foundations.SignSequenceMvPowerSeries
import Surreal.Foundations.SignSequencePowerSeries
import Surreal.Surcomplex.MvPowerSeries
import Surreal.Surcomplex.PowerSeries

/-!
# Univariate substitution under actual multivariate evaluation

For real and complex actual infinitesimals, the multivariate evaluator on one
variable is the univariate evaluator. Substituting a zero-constant multivariate
series into a univariate series therefore commutes with actual evaluation.
The ordinary coefficient series are arbitrary; no analytic convergence is used.
This supplies the actual-field substitution bridge for `a:cor:complexsub`.
-/

universe u v

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- The actual multivariate and univariate evaluators agree on one variable. -/
theorem mvPowerSeriesEvaluation_unit (x : SignSequence.{u}) (hx : IsInfinitesimal x)
    (f : PowerSeries ℝ) :
    mvPowerSeriesEvaluation (fun _ : Unit => x) (fun _ => hx) f =
      powerSeriesEvaluation x hx f := by
  change hahnEmbedding _ _ (Surreal.HahnSeries.mvEvaluate _ _ f) =
    hahnEmbedding _ _ (Surreal.HahnSeries.evaluate _ _ f)
  congr 1
  exact Surreal.HahnSeries.mvEvaluate_unit _ _ f

/-- A zero-constant multivariate inner series may be evaluated before univariate substitution. -/
theorem mvPowerSeriesEvaluation_powerSeries_subst {σ : Type v} [Fintype σ]
    (x : σ → SignSequence.{u}) (hx : ∀ i, IsInfinitesimal (x i))
    (B : MvPowerSeries σ ℝ) (hB : MvPowerSeries.constantCoeff B = 0)
    (f : PowerSeries ℝ) :
    mvPowerSeriesEvaluation x hx (PowerSeries.subst B f) =
      powerSeriesEvaluation (mvPowerSeriesEvaluation x hx B)
        ((isInfinitesimal_mvPowerSeriesEvaluation_iff x hx B).mpr hB) f := by
  rw [PowerSeries.subst_def,
    mvPowerSeriesEvaluation_subst x hx f (fun _ => B) (fun _ => hB)]
  exact mvPowerSeriesEvaluation_unit _ _ f

end
end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex

noncomputable section

/-- The actual multivariate and univariate evaluators agree on one variable. -/
theorem mvPowerSeriesEvaluation_unit (x : Surcomplex.{u}) (hx : IsInfinitesimal x)
    (f : PowerSeries ℂ) :
    mvPowerSeriesEvaluation (fun _ : Unit => x) (fun _ => hx) f =
      powerSeriesEvaluation x hx f := by
  change hahnEmbedding _ _ (Surreal.HahnSeries.mvEvaluate _ _ f) =
    hahnEmbedding _ _ (Surreal.HahnSeries.evaluate _ _ f)
  congr 1
  exact Surreal.HahnSeries.mvEvaluate_unit _ _ f

/-- A zero-constant multivariate inner series may be evaluated before univariate substitution. -/
theorem mvPowerSeriesEvaluation_powerSeries_subst {σ : Type v} [Fintype σ]
    (x : σ → Surcomplex.{u}) (hx : ∀ i, IsInfinitesimal (x i))
    (B : MvPowerSeries σ ℂ) (hB : MvPowerSeries.constantCoeff B = 0)
    (f : PowerSeries ℂ) :
    mvPowerSeriesEvaluation x hx (PowerSeries.subst B f) =
      powerSeriesEvaluation (mvPowerSeriesEvaluation x hx B)
        ((isInfinitesimal_mvPowerSeriesEvaluation_iff x hx B).mpr hB) f := by
  rw [PowerSeries.subst_def,
    mvPowerSeriesEvaluation_subst x hx f (fun _ => B) (fun _ => hB)]
  exact mvPowerSeriesEvaluation_unit _ _ f

end
end Surreal.Surcomplex
