import Mathlib.MeasureTheory.Group.Integral
import OAI.Combinatorics.Progressions.Estimates.AllocatedFiberCap

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators

variable {K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem coefficientTorusCharacter_add (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (y x : CoefficientTorus (K := K) U) :
    coefficientTorusCharacter U frequency (y+x) =
      coefficientTorusCharacter U frequency y * coefficientTorusCharacter U frequency x :=
  quotientLinearCharacter_add _ _ _ _ _

theorem coefficientTorusFourierSum_add
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (y x : CoefficientTorus (K := K) U) :
    coefficientTorusFourierSum U frequency c (y+x) =
      coefficientTorusFourierSum U frequency
        (fun a => c a * coefficientTorusCharacter U (frequency a) y) x := by
  simp only [coefficientTorusFourierSum, coefficientTorusCharacter_add, mul_assoc]

theorem coefficientFourier_translate_norm
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (y : CoefficientTorus (K := K) U) :
    (∑ a, ‖c a * coefficientTorusCharacter U (frequency a) y‖) = ∑ a, ‖c a‖ := by
  simp only [norm_mul, coefficientTorusCharacter_norm, mul_one]

theorem coefficientFourier_translate_approx (D : CoefficientTorus (K := K) U → ℝ)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ) {δ : ℝ}
    (happrox : ∀ x, ‖(D x : ℂ) - coefficientTorusFourierSum U frequency c x‖ ≤ δ)
    (y x : CoefficientTorus (K := K) U) :
    ‖(D (y+x) : ℂ) - coefficientTorusFourierSum U frequency
      (fun a => c a * coefficientTorusCharacter U (frequency a) y) x‖ ≤ δ := by
  rw [← coefficientTorusFourierSum_add]
  exact happrox (y+x)

theorem bounded_coefficient_translate_fiber_integrable
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [IsFiniteMeasure μ]
    (D : CoefficientTorus (K := K) U → ℝ) (hD : Measurable D)
    {M : ℝ} (hbound : ∀ x, ‖D x‖ ≤ M)
    (y : CoefficientTorus (K := K) U) (t : K → ℤ)
    (z : CoefficientTorus (K := Empty) U) :
    Integrable (fun x => D (y + coefficientFiberMap U t z x)) μ := by
  apply Integrable.of_bound
    (hD.comp (measurable_const.add (coefficientFiberMap_continuous U t z).measurable)).aestronglyMeasurable M
  exact ae_of_all μ (fun x => hbound _)

end Erdos3.VectorPolynomial

end

end OAI
