import Surreal.Algebra.PowerSeriesTranslation
import Surreal.Surcomplex.UnivariateSubstitution
import Surreal.Surcomplex.MvPowerSeriesBounds
import Surreal.Surcomplex.PowerSeriesFineDerivative

/-!
# Fine differentiation at every actual infinitesimal

Formal two-variable substitution supplies an exact quadratic Taylor remainder
around every infinitesimal center. Multivariate evaluation bounds this remainder
uniformly over every infinitesimal increment. The resulting difference quotient
therefore converges for all positive surreal tolerances, and its derivative is
the evaluation of the native formal derivative. No partial-sum limit is used.
This is the all-infinitesimal differentiation step in `trigonometry:prop:lift`.
-/

universe u

open Filter Topology

namespace Surreal.Foundations.SignSequence


noncomputable section

private def translationArguments (x h : SignSequence.{u}) : Bool → SignSequence.{u} :=
  fun b => if b then h else x

private theorem translationArguments_infinitesimal (x h : SignSequence.{u})
    (hx : IsInfinitesimal x) (hh : IsInfinitesimal h) :
    ∀ b, IsInfinitesimal (translationArguments x h b) := by
  intro b
  cases b
  · exact hx
  · exact hh

private theorem translation_add_infinitesimal {x h : SignSequence.{u}}
    (hx : IsInfinitesimal x) (hh : IsInfinitesimal h) : IsInfinitesimal (x + h) :=
  infinitesimal_add hx hh

/-- The actual second-order remainder around a possibly nonzero infinitesimal center. -/
def powerSeriesTranslationRemainder (f : PowerSeries ℝ) (x h : SignSequence.{u})
    (hx : IsInfinitesimal x) (hh : IsInfinitesimal h) : SignSequence.{u} :=
  mvPowerSeriesEvaluation (translationArguments x h) (translationArguments_infinitesimal x h hx hh)
    (FormalPowerSeries.translationSecondRemainder f)

/-- The exact first-order expansion, with a jointly evaluated quadratic remainder. -/
theorem powerSeriesEvaluation_add_eq_linear_add_sq_mul (f : PowerSeries ℝ)
    (x h : SignSequence.{u}) (hx : IsInfinitesimal x) (hh : IsInfinitesimal h) :
    powerSeriesEvaluation (x + h) (translation_add_infinitesimal hx hh) f =
      powerSeriesEvaluation x hx f +
        powerSeriesEvaluation x hx (PowerSeries.derivative ℝ f) * h +
        h ^ 2 * powerSeriesTranslationRemainder f x h hx hh := by
  let t := translationArguments x h
  have ht := translationArguments_infinitesimal x h hx hh
  have hs (g : PowerSeries ℝ) :
      mvPowerSeriesEvaluation t ht (PowerSeries.subst (MvPowerSeries.X false) g) =
        powerSeriesEvaluation x hx g := by
    rw [mvPowerSeriesEvaluation_powerSeries_subst t ht _ (by simp)]
    simp only [mvPowerSeriesEvaluation_X, t, translationArguments, Bool.false_eq_true, if_false]
  have ha : mvPowerSeriesEvaluation t ht
      (PowerSeries.subst (MvPowerSeries.X false + MvPowerSeries.X true) f) =
      powerSeriesEvaluation (x + h) (translation_add_infinitesimal hx hh) f := by
    rw [mvPowerSeriesEvaluation_powerSeries_subst t ht _ (by simp)]
    simp only [map_add, mvPowerSeriesEvaluation_X, t, translationArguments,
      Bool.false_eq_true, if_false, if_true]
  have he := congrArg (mvPowerSeriesEvaluation t ht)
    (FormalPowerSeries.subst_add_eq_subst_add_derivative_mul_add_sq_mul f)
  simpa only [ha, map_add, map_mul, map_pow, hs, mvPowerSeriesEvaluation_X,
    t, translationArguments, if_true, powerSeriesTranslationRemainder] using he

/-- The same ordinary bound works for every infinitesimal center and increment. -/
theorem abs_powerSeriesTranslationRemainder_lt (f : PowerSeries ℝ) (x h : SignSequence.{u})
    (hx : IsInfinitesimal x) (hh : IsInfinitesimal h) :
    |powerSeriesTranslationRemainder f x h hx hh| < ofReal (|f.coeff 2| + 1) := by
  simpa only [powerSeriesTranslationRemainder,
    FormalPowerSeries.constantCoeff_translationSecondRemainder] using
    abs_mvPowerSeriesEvaluation_lt (translationArguments x h) (translationArguments_infinitesimal x h hx hh)
      (FormalPowerSeries.translationSecondRemainder f)

/-- Formal evaluation differentiates at every infinitesimal, including nonordinary centers. -/
theorem fineHasDerivAt_powerSeriesFunction (f : PowerSeries ℝ) (x : SignSequence.{u})
    (hx : IsInfinitesimal x) :
    FineHasDerivAt (powerSeriesFunction f)
      (powerSeriesEvaluation x hx (PowerSeries.derivative ℝ f)) x := by
  have hM : (0 : SignSequence.{u}) < ofReal (|f.coeff 2| + 1) := by
    simpa only [map_zero] using ofReal_strictMono
      (show (0 : ℝ) < |f.coeff 2| + 1 by positivity)
  apply fineHasDerivAt_of_quadratic_remainder _ _ _ _ hM
  have hsmall : {h : SignSequence.{u} | IsInfinitesimal h} ∈ 𝓝 0 :=
    infinitesimals_mem_nhds_zero
  filter_upwards [hsmall] with h hh
  refine ⟨powerSeriesTranslationRemainder f x h hx hh, ?_, (abs_powerSeriesTranslationRemainder_lt f x h hx hh).le⟩
  simpa only [powerSeriesFunction_of_isInfinitesimal f x hx,
    powerSeriesFunction_of_isInfinitesimal f (x + h) (translation_add_infinitesimal hx hh)] using
    powerSeriesEvaluation_add_eq_linear_add_sq_mul f x h hx hh

/-- Evaluation is fine-continuous throughout its open infinitesimal domain. -/
theorem continuousAt_powerSeriesFunction (f : PowerSeries ℝ) (x : SignSequence.{u})
    (hx : IsInfinitesimal x) : ContinuousAt (powerSeriesFunction f) x :=
  (fineHasDerivAt_powerSeriesFunction f x hx).continuousAt

end
end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex

open Foundations

noncomputable section

private def translationArguments (x h : Surcomplex.{u}) : Bool → Surcomplex.{u} :=
  fun b => if b then h else x

private theorem translationArguments_infinitesimal (x h : Surcomplex.{u})
    (hx : IsInfinitesimal x) (hh : IsInfinitesimal h) :
    ∀ b, IsInfinitesimal (translationArguments x h b) := by
  intro b
  cases b
  · exact hx
  · exact hh

private theorem translation_add_infinitesimal {x h : Surcomplex.{u}}
    (hx : IsInfinitesimal x) (hh : IsInfinitesimal h) : IsInfinitesimal (x + h) :=
  ⟨SignSequence.infinitesimal_add hx.1 hh.1, SignSequence.infinitesimal_add hx.2 hh.2⟩

/-- The actual second-order remainder around a possibly nonzero infinitesimal center. -/
def powerSeriesTranslationRemainder (f : PowerSeries ℂ) (x h : Surcomplex.{u})
    (hx : IsInfinitesimal x) (hh : IsInfinitesimal h) : Surcomplex.{u} :=
  mvPowerSeriesEvaluation (translationArguments x h) (translationArguments_infinitesimal x h hx hh)
    (FormalPowerSeries.translationSecondRemainder f)

/-- The exact first-order expansion, with a jointly evaluated quadratic remainder. -/
theorem powerSeriesEvaluation_add_eq_linear_add_sq_mul (f : PowerSeries ℂ)
    (x h : Surcomplex.{u}) (hx : IsInfinitesimal x) (hh : IsInfinitesimal h) :
    powerSeriesEvaluation (x + h) (translation_add_infinitesimal hx hh) f =
      powerSeriesEvaluation x hx f +
        powerSeriesEvaluation x hx (PowerSeries.derivative ℂ f) * h +
        h ^ 2 * powerSeriesTranslationRemainder f x h hx hh := by
  let t := translationArguments x h
  have ht := translationArguments_infinitesimal x h hx hh
  have hs (g : PowerSeries ℂ) :
      mvPowerSeriesEvaluation t ht (PowerSeries.subst (MvPowerSeries.X false) g) =
        powerSeriesEvaluation x hx g := by
    rw [mvPowerSeriesEvaluation_powerSeries_subst t ht _ (by simp)]
    simp only [mvPowerSeriesEvaluation_X, t, translationArguments, Bool.false_eq_true, if_false]
  have ha : mvPowerSeriesEvaluation t ht
      (PowerSeries.subst (MvPowerSeries.X false + MvPowerSeries.X true) f) =
      powerSeriesEvaluation (x + h) (translation_add_infinitesimal hx hh) f := by
    rw [mvPowerSeriesEvaluation_powerSeries_subst t ht _ (by simp)]
    simp only [map_add, mvPowerSeriesEvaluation_X, t, translationArguments,
      Bool.false_eq_true, if_false, if_true]
  have he := congrArg (mvPowerSeriesEvaluation t ht)
    (FormalPowerSeries.subst_add_eq_subst_add_derivative_mul_add_sq_mul f)
  simpa only [ha, map_add, map_mul, map_pow, hs, mvPowerSeriesEvaluation_X,
    t, translationArguments, if_true, powerSeriesTranslationRemainder] using he

/-- The same ordinary bound works for every infinitesimal center and increment. -/
theorem modulus_powerSeriesTranslationRemainder_lt (f : PowerSeries ℂ) (x h : Surcomplex.{u})
    (hx : IsInfinitesimal x) (hh : IsInfinitesimal h) :
    modulus (powerSeriesTranslationRemainder f x h hx hh) < SignSequence.ofReal (norm (f.coeff 2) + 1) := by
  simpa only [powerSeriesTranslationRemainder,
    FormalPowerSeries.constantCoeff_translationSecondRemainder] using
    modulus_mvPowerSeriesEvaluation_lt (translationArguments x h) (translationArguments_infinitesimal x h hx hh)
      (FormalPowerSeries.translationSecondRemainder f)

/-- Formal evaluation differentiates at every infinitesimal, including nonordinary centers. -/
theorem fineHasDerivAt_powerSeriesFunction (f : PowerSeries ℂ) (x : Surcomplex.{u})
    (hx : IsInfinitesimal x) :
    FineHasDerivAt (powerSeriesFunction f)
      (powerSeriesEvaluation x hx (PowerSeries.derivative ℂ f)) x := by
  have hM : (0 : SignSequence.{u}) < SignSequence.ofReal (norm (f.coeff 2) + 1) := by
    simpa only [map_zero] using SignSequence.ofReal_strictMono
      (show (0 : ℝ) < norm (f.coeff 2) + 1 by positivity)
  apply fineHasDerivAt_of_quadratic_remainder _ _ _ _ hM
  have hsmall : {h : Surcomplex.{u} | IsInfinitesimal h} ∈ 𝓝 0 :=
    isClopen_setOf_isInfinitesimal.isOpen.mem_nhds
      ⟨SignSequence.infinitesimal_zero, SignSequence.infinitesimal_zero⟩
  filter_upwards [hsmall] with h hh
  refine ⟨powerSeriesTranslationRemainder f x h hx hh, ?_, (modulus_powerSeriesTranslationRemainder_lt f x h hx hh).le⟩
  simpa only [powerSeriesFunction_of_isInfinitesimal f x hx,
    powerSeriesFunction_of_isInfinitesimal f (x + h) (translation_add_infinitesimal hx hh)] using
    powerSeriesEvaluation_add_eq_linear_add_sq_mul f x h hx hh

/-- Evaluation is fine-continuous throughout its open infinitesimal domain. -/
theorem continuousAt_powerSeriesFunction (f : PowerSeries ℂ) (x : Surcomplex.{u})
    (hx : IsInfinitesimal x) : ContinuousAt (powerSeriesFunction f) x :=
  (fineHasDerivAt_powerSeriesFunction f x hx).continuousAt

end
end Surreal.Surcomplex

