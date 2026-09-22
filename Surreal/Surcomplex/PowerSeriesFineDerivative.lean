import Surreal.Surcomplex.PowerSeriesRemainder
import Surreal.Surcomplex.FineDerivative
import Surreal.Surcomplex.StandardPartTopology

/-!
# Fine differentiation of actual formal evaluation at zero

Formal evaluation is defined on the open infinitesimal domain. Extending it
by zero outside that domain gives a total function with the same local
behavior at zero. Its fine derivative is the ordinary linear coefficient,
using the uniformly bounded exact quadratic remainder. In particular this
is a genuine fine-neighborhood limit, not a claim about convergence of
partial sums or only ordinary-sized tolerances.
-/

universe u

open Filter Topology
open scoped Classical

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- A total extension of formal evaluation from the open infinitesimal domain. -/
def powerSeriesFunction (f : PowerSeries ℝ) (x : SignSequence.{u}) : SignSequence.{u} :=
  if hx : IsInfinitesimal x then powerSeriesEvaluation x hx f else 0

@[simp] theorem powerSeriesFunction_of_isInfinitesimal (f : PowerSeries ℝ)
    (x : SignSequence.{u}) (hx : IsInfinitesimal x) :
    powerSeriesFunction f x = powerSeriesEvaluation x hx f := by
  simp only [powerSeriesFunction, dif_pos hx]

@[simp] theorem powerSeriesFunction_zero (f : PowerSeries ℝ) :
    powerSeriesFunction f (0 : SignSequence.{u}) = ofReal (f.coeff 0) := by
  rw [powerSeriesFunction_of_isInfinitesimal f 0 infinitesimal_zero, powerSeriesEvaluation_zero]
  rw [PowerSeries.coeff_zero_eq_constantCoeff]

/-- The first formal coefficient is the fine derivative of evaluation at zero. -/
theorem fineHasDerivAt_powerSeriesFunction_zero (f : PowerSeries ℝ) :
    FineHasDerivAt (powerSeriesFunction f) (ofReal (f.coeff 1)) (0 : SignSequence.{u}) := by
  have hM : (0 : SignSequence.{u}) < ofReal (|f.coeff 2| + 1) := by
    simpa only [map_zero] using ofReal_strictMono
      (show (0 : ℝ) < |f.coeff 2| + 1 by positivity)
  apply fineHasDerivAt_of_quadratic_remainder _ _ _ _ hM
  filter_upwards [infinitesimals_mem_nhds_zero] with x hx
  refine ⟨powerSeriesSecondRemainder x hx f, ?_, (abs_powerSeriesSecondRemainder_lt x hx f).le⟩
  simpa only [_root_.zero_add, powerSeriesFunction_zero,
    powerSeriesFunction_of_isInfinitesimal f x hx] using
    powerSeriesEvaluation_eq_linear_add_sq_mul x hx f

/-- Formal evaluation is continuous at zero for the native fine topology. -/
theorem continuousAt_powerSeriesFunction_zero (f : PowerSeries ℝ) :
    ContinuousAt (powerSeriesFunction f) (0 : SignSequence.{u}) :=
  (fineHasDerivAt_powerSeriesFunction_zero f).continuousAt

end
end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- A total extension of formal evaluation from the open infinitesimal domain. -/
def powerSeriesFunction (f : PowerSeries ℂ) (x : Surcomplex.{u}) : Surcomplex.{u} :=
  if hx : IsInfinitesimal x then powerSeriesEvaluation x hx f else 0

@[simp] theorem powerSeriesFunction_of_isInfinitesimal (f : PowerSeries ℂ)
    (x : Surcomplex.{u}) (hx : IsInfinitesimal x) :
    powerSeriesFunction f x = powerSeriesEvaluation x hx f := by
  simp only [powerSeriesFunction, dif_pos hx]

@[simp] theorem powerSeriesFunction_zero (f : PowerSeries ℂ) :
    powerSeriesFunction f (0 : Surcomplex.{u}) = ofComplex (f.coeff 0) := by
  rw [powerSeriesFunction_of_isInfinitesimal f 0
    ⟨SignSequence.infinitesimal_zero, SignSequence.infinitesimal_zero⟩,
    powerSeriesEvaluation_zero]
  rw [PowerSeries.coeff_zero_eq_constantCoeff]

/-- The first formal coefficient is the fine derivative of evaluation at zero. -/
theorem fineHasDerivAt_powerSeriesFunction_zero (f : PowerSeries ℂ) :
    FineHasDerivAt (powerSeriesFunction f) (ofComplex (f.coeff 1)) (0 : Surcomplex.{u}) := by
  have hM : (0 : SignSequence.{u}) < SignSequence.ofReal (norm (f.coeff 2) + 1) := by
    simpa only [map_zero] using SignSequence.ofReal_strictMono
      (show (0 : ℝ) < norm (f.coeff 2) + 1 by positivity)
  apply fineHasDerivAt_of_quadratic_remainder _ _ _ _ hM
  have hsmall : {x : Surcomplex.{u} | IsInfinitesimal x} ∈ 𝓝 0 :=
    isClopen_setOf_isInfinitesimal.isOpen.mem_nhds
      ⟨SignSequence.infinitesimal_zero, SignSequence.infinitesimal_zero⟩
  filter_upwards [hsmall] with x hx
  refine ⟨powerSeriesSecondRemainder x hx f, ?_, (modulus_powerSeriesSecondRemainder_lt x hx f).le⟩
  simpa only [zero_add, powerSeriesFunction_zero,
    powerSeriesFunction_of_isInfinitesimal f x hx] using
    powerSeriesEvaluation_eq_linear_add_sq_mul x hx f

/-- Formal evaluation is continuous at zero for the native surcomplex fine topology. -/
theorem continuousAt_powerSeriesFunction_zero (f : PowerSeries ℂ) :
    ContinuousAt (powerSeriesFunction f) (0 : Surcomplex.{u}) :=
  (fineHasDerivAt_powerSeriesFunction_zero f).continuousAt

end
end Surreal.Surcomplex
