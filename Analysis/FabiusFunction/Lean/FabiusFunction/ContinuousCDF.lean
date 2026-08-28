import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.CDF

/-!
# Continuous cumulative distribution functions

This module collects measure-theoretic facts about real cumulative distribution
functions that are independent of the Fabius construction.

The main results say that a probability measure with no atoms has a continuous
CDF, that invariance under an affine reflection gives the corresponding CDF
symmetry, and that an everywhere pointwise derivative of a CDF is its Lebesgue
density.  Monotonicity supplies the derivative's nonnegativity and local
integrability automatically.
-/

open Function MeasureTheory ProbabilityTheory Set

namespace Fabius

set_option autoImplicit false
noncomputable section

/-- The CDF of an atomless real probability measure is continuous. -/
theorem continuous_cdf_of_nullSingleton
    (mu : Measure ℝ) [IsProbabilityMeasure mu] [NullSingletonClass mu] :
    Continuous (cdf mu) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hzero : (cdf mu).measure {x} = 0 := by
    rw [ProbabilityTheory.measure_cdf]
    exact measure_singleton x
  rw [StieltjesFunction.measure_singleton] at hzero
  have hsub : cdf mu x - leftLim (cdf mu) x ≤ 0 :=
    ENNReal.ofReal_eq_zero.mp hzero
  have hleft : leftLim (cdf mu) x = cdf mu x :=
    le_antisymm ((ProbabilityTheory.monotone_cdf mu).leftLim_le le_rfl)
      (sub_nonpos.mp hsub)
  rw [(ProbabilityTheory.monotone_cdf mu).continuousAt_iff_leftLim_eq_rightLim,
    (cdf mu).rightLim_eq, hleft]

/-- If a real probability measure is invariant under reflection about `a / 2`,
then its CDF satisfies `F (a - x) = 1 - F x`.

The null-singleton hypothesis is exactly what permits replacing the open
half-line below `x` by the closed half-line at `x`.
-/
theorem cdf_reflection_sub
    (mu : Measure ℝ) [IsProbabilityMeasure mu] [NullSingletonClass mu]
    {a : ℝ} (hmu : mu.map (fun y : ℝ => a - y) = mu) (x : ℝ) :
    cdf mu (a - x) = 1 - cdf mu x := by
  calc
    cdf mu (a - x) = mu.real (Iic (a - x)) := by
      rw [ProbabilityTheory.cdf_eq_real]
    _ = (mu.map (fun y : ℝ => a - y)).real (Iic (a - x)) := by
      rw [hmu]
    _ = mu.real ((fun y : ℝ => a - y) ⁻¹' Iic (a - x)) := by
      rw [map_measureReal_apply (by fun_prop) measurableSet_Iic]
    _ = mu.real (Ici x) := by
      have hset : ((fun y : ℝ => a - y) ⁻¹' Iic (a - x)) = Ici x := by
        ext y
        change (a - y ≤ a - x) ↔ x ≤ y
        constructor <;> intro hy <;> linarith
      rw [hset]
    _ = mu.real (Iio x)ᶜ := by rw [compl_Iio]
    _ = 1 - mu.real (Iio x) :=
      probReal_compl_eq_one_sub measurableSet_Iio
    _ = 1 - mu.real (Iic x) := by
      rw [measureReal_congr Iio_ae_eq_Iic]
    _ = 1 - cdf mu x := by
      rw [ProbabilityTheory.cdf_eq_real]

/-- An everywhere pointwise derivative of a probability CDF is the
Radon--Nikodym density of the measure with respect to Lebesgue measure.

The proof identifies the two measures on every interval `(a, b]` by the
fundamental theorem of calculus.  Monotonicity of the CDF supplies both
nonnegativity and local integrability of the derivative, so no continuity or
prior absolute-continuity hypothesis is needed.
-/
theorem measure_eq_withDensity_of_cdf_hasDerivAt
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (f : ℝ → ℝ)
    (hderiv : ∀ x, HasDerivAt (cdf mu) (f x) x) :
    mu = (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (f x)) := by
  refine Measure.ext_of_Ioc mu _ ?_
  intro a b hab
  have hmono : Monotone (cdf mu) := ProbabilityTheory.monotone_cdf mu
  have hnonneg : ∀ x, 0 ≤ f x := fun x =>
    (hderiv x).nonneg_of_monotone hmono
  have hf_eq_deriv : f = deriv (cdf mu) := by
    funext x
    exact (hderiv x).deriv.symm
  have hint : IntervalIntegrable f volume a b := by
    rw [hf_eq_deriv]
    exact (hmono.monotoneOn (uIcc a b)).intervalIntegrable_deriv
  have hfund :
      (∫ x in a..b, f x) = cdf mu b - cdf mu a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _hx => hderiv x) hint
  have hInt : IntegrableOn f (Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mp hint
  rw [← ProbabilityTheory.measure_cdf mu, StieltjesFunction.measure_Ioc,
    withDensity_apply _ measurableSet_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall hnonneg),
    ← intervalIntegral.integral_of_le hab.le, hfund]

end
end Fabius
