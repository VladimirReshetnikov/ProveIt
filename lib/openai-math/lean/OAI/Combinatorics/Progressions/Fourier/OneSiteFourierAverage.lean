import OAI.Combinatorics.Progressions.Estimates.CoefficientFiberOrthogonality
import OAI.Combinatorics.Progressions.Estimates.OneSiteResidualFactor

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

theorem coefficientTorusFourierSum_fiber_integrable {K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [IsFiniteMeasure μ]
    (y : CoefficientTorus (K := Empty) U) :
    Integrable (fun x => coefficientTorusFourierSum U frequency c (coefficientFiberMap U t y x)) μ := by
  apply integrable_finsetSum
  intro a _
  exact (coefficientTorusCharacter_fiber_integrable U t (frequency a) μ y).const_mul (c a)

theorem coefficientTorusFourierSum_fiberAverage {K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (t : K → ℤ) (difference : Fin 0 → K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (x : CoefficientTorus (K := K) U) :
    coefficientFiberAverage U μ t (coefficientTorusFourierSum U frequency c) (coefficientEvaluationTorus U t x) =
      ∑ a, if affineCubeModeFactors U t difference (frequency a) then
        c a * coefficientTorusCharacter U (frequency a) x else 0 := by
  change (∫ z, ∑ a, c a * coefficientTorusCharacter U (frequency a)
    (coefficientFiberMap U t (coefficientEvaluationTorus U t x) z) ∂μ) = _
  rw [integral_finsetSum _ (fun a _ =>
    (coefficientTorusCharacter_fiber_integrable U t (frequency a) μ _).const_mul (c a))]
  simp only [integral_const_mul]
  change (∑ a, c a * coefficientFiberAverage U μ t (coefficientTorusCharacter U (frequency a))
    (coefficientEvaluationTorus U t x)) = _
  simp only [coefficientTorusCharacter_fiberAverage_evaluation,
    coefficientResidualFunctional_eq_zero_iff_oneSite U t difference, mul_ite, mul_zero]

theorem affineCubeFourierProjection_eq_fiberAverage {I K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (t : K → ℤ) (difference : Fin 0 → K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (b : Option K → I → ℝ) :
    affineCubeFourierProjection U t difference frequency p c b =
      coefficientFiberAverage U μ t (coefficientTorusFourierSum U frequency c)
        (coefficientEvaluationTorus U t (affineSampleCoefficientTorus U p hm b)) := by
  rw [coefficientTorusFourierSum_fiberAverage U t difference]
  simp only [coefficientTorusCharacter_sample U _ p hp hm b, affineCubeFourierProjection]

end Erdos3.BooleanCubeKernel

end

end OAI
