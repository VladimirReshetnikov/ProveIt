import OAI.Combinatorics.Progressions.Estimates.DenseProductApproximation

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem dense_product_approximation_density (e : ℕ)
    {X : Fin e → Type*} [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    (v : ∀ i, X i → ℤ) (hv : ∀ i, Function.Injective (v i)) (N : Fin e → ℕ)
    {η θ ε : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hN : ∀ i, denseProductDensityBudget e η ≤ N i)
    (hcard : ∀ i, N i ≤ Fintype.card (X i))
    (hbound : ∀ i x, |v i x| ≤ (N i : ℤ))
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1/denseProductDensityBudget e η)
    (hdensity : η ≤ nearIntegerDensity
      (fun x : ∀ i, X i => θ * ∏ i, (v i (x i) : ℝ)) ε) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ denseProductDensityBudget e η ∧
      NearInteger (denseProductDensityBudget e η*ε / ∏ i, (N i : ℝ)) ((q : ℝ)*θ) := by
  obtain ⟨hB, hBη, _⟩ := reciprocal_density_ceil hη hη1
  have hKB := denseProductBudget_ceil_le e hη hη1
  have hKN : ∀ i, denseProductBudget e ⌈1/η⌉₊ ≤ N i := by
    intro i
    exact_mod_cast hKB.trans (hN i)
  have hKp : (0 : ℝ) < denseProductBudget e ⌈1/η⌉₊ := by
    exact_mod_cast denseProductBudget_pos e ⌈1/η⌉₊ hB
  have hsmall' : ε ≤ 1/(denseProductBudget e ⌈1/η⌉₊ : ℝ) :=
    hsmall.trans (one_div_le_one_div_of_le hKp hKB)
  obtain ⟨q, hq, hqK, hnear⟩ := dense_product_approximation e ⌈1/η⌉₊ hB
    v hv N hKN hcard hbound hε hsmall' (hBη.trans hdensity)
  refine ⟨q, hq, (Nat.cast_le.mpr hqK).trans hKB, nearInteger_mono hnear ?_⟩
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hKB hε)
    (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg (N i)))

end Erdos3

end

end OAI
