import OAI.Combinatorics.Progressions.Estimates.CoefficientModeRationalDecomposition

namespace OAI

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators Classical

theorem coefficientMode_paired_bias_lt_of_rank {I K J : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] [Fintype J] {n : ℕ}
    (frequency : (K →₀ ℕ) → J → ℤ) (a : Fin (n + 1) → K → ℤ)
    (p : VectorPolynomial I ℝ (J → ℝ)) (hp : Homogeneous (n + 1) p)
    (W : Submodule ℝ (J → ℝ)) (N s : I → ℕ) (hs : ∀ k, 0 < s k)
    {ζ R B : ℝ} (hζ : 0 < ζ) (hN : ∀ k, multiaffineBiasBudget n ζ ≤ N k)
    (H : I → ℝ) (hH : ∀ k, 0 < H k) {A : ℝ} (hA : 0 ≤ A)
    (hscale : ∀ k, H k ≤ A * ((s k : ℝ) * (N k : ℝ)))
    (hrank : HasLayerSamplingRank (n + 1) H R W p)
    (hrow : ∀ j, |(integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ)| ≤ B)
    (hrowBudget : ((n + 1).factorial : ℝ) * B ≤ R)
    (hnonzero : ∃ w : W,
      (∑ j, (integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ) * w.val j) ≠ 0)
    (hdenom : (∏ j : Fin (n + 1) → I,
      (multiaffineBiasBudget n ζ * ∏ i, (s (j i) : ℝ))) ≤ R)
    (hcoeff : (Fintype.card I : ℝ) ^ (n + 1) * (A ^ (n + 1) * multiaffineBiasBudget n ζ) ≤ R) :
    ‖𝔼 x : Fin (n + 1) → ∀ k, Fin (N k),
      𝔼 y : Fin (n + 1) → ∀ k, Fin (N k),
        character ((polynomialTopSymbol (n + 1) (coefficientModePolynomial
          (coefficientFunctional (fun d j => (frequency d j : ℝ))) p)
          (fun i z => (a i z.1 : ℝ) *
            ((s z.2 : ℝ) * ((x i z.2).val : ℝ) - (s z.2 : ℝ) * ((y i z.2).val : ℝ))) : ℝ) :
              CircleFourier.Circle)‖ < ζ := by
  by_contra hn
  obtain ⟨D, hD, hDb, E, Q, heq, he⟩ := coefficientMode_integer_row_decomposition
    frequency a p hp N s hs hζ hN H hH hA hscale (le_of_not_gt hn)
  have ha (j : J) : |(factorialContractedRow frequency a j : ℝ)| ≤ R :=
    (factorialContractedRow_bound frequency a hrow j).trans hrowBudget
  obtain ⟨w, hw⟩ := hnonzero
  apply hrank.not_approximation hp (factorialContractedRow frequency a) ha
    ⟨w, factorialContractedRow_nonzero frequency a w.val hw⟩
  apply polynomialRationalApproximation_of_decomposition _ R _ E Q D hD
    (hDb.trans hdenom) heq
  intro α
  exact (he α).trans (div_le_div_of_nonneg_right hcoeff (monomialScale_pos _ hH α).le)

end Erdos3.VectorPolynomial

end

end OAI
