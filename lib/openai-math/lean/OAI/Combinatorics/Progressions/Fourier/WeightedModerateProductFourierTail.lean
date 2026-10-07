import OAI.Combinatorics.Progressions.Sampling.WeightedCubeGridDensity

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem weightedModerateGridProduct_truncation_le {B : Type*} [Fintype B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U : ℝ}
    (hc : ∀ b, ScalarCubePrimitiveBudget (c b) A U)
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (ζ : ℕ → ℝ) (m : ℕ) (hζ : ∀ i ≤ m, 0 < ζ i ∧ ζ i ≤ 1)
    (hclen : ∀ i ≤ m, ∀ b, localizedMajorArcLengthBudget n U (ζ i) ≤ (c b).length)
    (hlen : ∀ i ≤ m, ∀ b j, localizedMajorArcLengthBudget n U (ζ i) ≤ (s b j).length)
    {M : ℕ} (hM : 0 < M) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n)
    (offset : B → ℝ) (Q H : ℕ → ℕ)
    (hQ : ∀ i ≤ m, ∀ b, (localizedMajorArcBudget n U (ζ i) * ((c b).modulus none * U ^ n)) ^ J.card ≤ Q i)
    (hH : ∀ i ≤ m, ∀ b, M * (localizedMajorArcErrorBudget n U (ζ i) /
      (((c b).modulus none * (c b).length : ℝ) * ∏ j, ((s b j).length : ℝ))) ≤ H i)
    (ψ : (J → Fin M) → ℂ) (hψ : ∀ k, ‖ψ k‖ ≤ 1) :
    ‖(∑ k, (∏ b, weightedModerateGridCoefficient (c b) (s b) (offset b) M J k) * ψ k) -
        ∑ k ∈ rationalGridMajorBox J M (Q 0) (H 0),
          (∏ b, weightedModerateGridCoefficient (c b) (s b) (offset b) M J k) * ψ k‖ ≤
      gridBlockTailBudget M J.card (Fintype.card B) Q H ζ m := by
  let S i := rationalGridMajorBox J M (Q i) (H i)
  have hsmall : ∀ i ≤ m, ∀ b k, k ∉ S i →
      ‖weightedModerateGridCoefficient (c b) (s b) (offset b) M J k‖ ≤ ζ i := by
    intro i hi b k hk
    by_contra hnot
    exact hk (weightedModerateGridCoefficient_mem_major (c b) (s b) A hA (hc b) (h b)
      (hζ i hi).1 (hζ i hi).2 (hclen i hi b) (hlen i hi b) (offset b) hM J hJ
      (hQ i hi b) (hH i hi b) k (le_of_lt (lt_of_not_ge hnot)))
  have ht := product_spectrum_truncation_levels
    (fun b k => weightedModerateGridCoefficient (c b) (s b) (offset b) M J k) ψ hψ S ζ m
      (fun i hi => (hζ i hi).1.le) hsmall
  apply ht.trans
  apply add_le_add
  · apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_right
    · simpa only [Fintype.card_coe] using rationalGridMajorBox_card J M (Q (i + 1)) (H (i + 1))
    · exact pow_nonneg (hζ i (by have := Finset.mem_range.mp hi; omega)).1.le _
  · exact le_of_eq (by simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Nat.cast_pow])

end Erdos3

end

end OAI
