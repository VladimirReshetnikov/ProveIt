/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Fourier.CoefficientResidualCharacter

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

theorem coefficientTorusCharacter_fiber_integrable {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (μ : Measure (CoefficientTorus (K := K) U)) [IsFiniteMeasure μ]
    (y : CoefficientTorus (K := Empty) U) :
    Integrable (fun x => coefficientTorusCharacter U frequency (coefficientFiberMap U t y x)) μ := by
  have hc : Continuous (coefficientTorusCharacter U frequency) :=
    quotientLinearCharacter_continuous _ _ _
      (coefficientArrayFunctional U frequency).continuous_of_finiteDimensional
  apply Integrable.of_bound (hc.comp (coefficientFiberMap_continuous U t y)).aestronglyMeasurable 1
  exact ae_of_all μ (fun x => (quotientLinearCharacter_norm _ _ _ _).le)

theorem coefficientTorusCharacter_fiberAverage {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [MeasurableAdd₂ (CoefficientTorus (K := K) U)]
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (y : CoefficientTorus (K := Empty) U) :
    coefficientFiberAverage U μ t (coefficientTorusCharacter U frequency) y =
      if coefficientResidualFunctional U t frequency = 0 then
        coefficientTorusCharacter U frequency (constantCoefficientTorusMap U y) else 0 := by
  unfold coefficientFiberAverage
  simp_rw [coefficientTorusCharacter_fiber]
  rw [integral_const_mul, quotientLinearCharacter_integral]
  split_ifs <;> simp

theorem coefficientTorusCharacter_fiberAverage_evaluation {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [MeasurableAdd₂ (CoefficientTorus (K := K) U)]
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (x : CoefficientTorus (K := K) U) :
    coefficientFiberAverage U μ t (coefficientTorusCharacter U frequency) (coefficientEvaluationTorus U t x) =
      if coefficientResidualFunctional U t frequency = 0 then coefficientTorusCharacter U frequency x else 0 := by
  rw [coefficientTorusCharacter_fiberAverage]
  by_cases h : coefficientResidualFunctional U t frequency = 0
  · rw [ite_eq_left h, ite_eq_left h]
    have he := coefficientTorusCharacter_fiber U t frequency (coefficientEvaluationTorus U t x) x
    simpa only [coefficientFiberMap_retraction, h, quotientLinearCharacter_zero, mul_one] using he.symm
  · simp only [ite_eq_right h]

end Erdos3.VectorPolynomial

end

end OAI
