import OAI.Combinatorics.Progressions.Polynomial.PolynomialTranslationSeries

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

theorem polynomialTranslate_exponentialCoordinate_series_of_nilpotent (x : σ → ℚ)
    {P : MvPolynomial σ ℚ} {n : ℕ}
    (hP : ((scalarDirectionalDerivative x).toLinearMap ^ (n + 1)) P = 0) :
    polynomialTranslate x (polynomialExponentialCoordinate x P) =
      ∑ i ∈ Finset.range (n + 1),
        (((i + 1).factorial : ℚ)⁻¹) • ((scalarDirectionalDerivative x).toLinearMap ^ i) P := by
  rw [polynomialTranslate_exponentialCoordinate]
  exact polynomialExponentialCoordinate_neg_series_of_nilpotent x hP

theorem polynomialTranslate_exponentialCoordinate_series
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (x : σ → ℚ)
    {P : MvPolynomial σ ℚ} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    polynomialTranslate x (polynomialExponentialCoordinate x P) =
      ∑ i ∈ Finset.range (n + 1),
        (((i + 1).factorial : ℚ)⁻¹) • ((scalarDirectionalDerivative x).toLinearMap ^ i) P :=
  polynomialTranslate_exponentialCoordinate_series_of_nilpotent x
    (scalarDirectionalDerivative_pow_eq_zero_of_weightedSupport w hw x hP)

end Erdos3

end

end OAI
