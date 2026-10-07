import OAI.Combinatorics.Progressions.Probability.AnisotropicSmoothPairLaw

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def smoothPairProductDensity {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) (L : ℝ) (hH : ∀ i, 0 < H i) (hL : 0 < L)
    (y : I → Fin 2 → ℝ) : ℝ :=
  ∏ i, affinePairRowDensity t u k hne (H i) L (hH i) hL
    (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2)) (y i)

theorem smoothPairProductDensity_regularity {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) (L : ℝ) (hH : ∀ i, 0 < H i) (hL : 0 < L)
    {C κ : ℝ} (hC : 1 ≤ C) (hκ : 0 < κ)
    (ht : |(t k : ℝ) / L| ≤ C) (hu : |(u k : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|) :
    let B : ℝ≥0 := Real.toNNReal (1 + 2 * (4 * C / κ) ^ 2 * 2 ^ Fintype.card {j : J // j ≠ k})
    let K : ℝ≥0 := Real.toNNReal (2 * (4 * C / κ) ^ 3 * (smoothPairRowLipschitz k : ℝ) *
      2 ^ Fintype.card {j : J // j ≠ k})
    (∀ y, |smoothPairProductDensity t u k hne H L hH hL y| ≤ (B : ℝ) ^ Fintype.card I) ∧
      LipschitzWith (Fintype.card I * K * B ^ Fintype.card I)
        (smoothPairProductDensity t u k hne H L hH hL) := by
  dsimp only
  let B : ℝ≥0 := Real.toNNReal (1 + 2 * (4 * C / κ) ^ 2 * 2 ^ Fintype.card {j : J // j ≠ k})
  let K : ℝ≥0 := Real.toNNReal (2 * (4 * C / κ) ^ 3 * (smoothPairRowLipschitz k : ℝ) *
    2 ^ Fintype.card {j : J // j ≠ k})
  have hB : 1 ≤ B := by
    apply NNReal.coe_le_coe.mp
    dsimp only [B]
    rw [Real.coe_toNNReal _ (by positivity)]
    simp only [NNReal.coe_one]
    exact le_add_of_nonneg_right (by positivity)
  have hlip (i : I) : LipschitzWith K (fun y : I → Fin 2 → ℝ =>
      affinePairRowDensity t u k hne (H i) L (hH i) hL
        (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2)) (y i)) := by
    have h := smooth_affinePairRowDensity_lipschitz t u k hne (hH i) hL hC hκ ht hu hgap
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (h.dist_le_mul (x i) (y i)).trans
      (mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) K.coe_nonneg)
  have hcap (i : I) (y : I → Fin 2 → ℝ) :
      |affinePairRowDensity t u k hne (H i) L (hH i) hL
        (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2)) (y i)| ≤ B := by
    have h := smooth_affinePairRowDensity_cap t u k hne (hH i) hL hC hκ ht hu hgap (y i)
    dsimp only [B]
    rw [Real.coe_toNNReal _ (by positivity)]
    linarith
  exact bounded_lipschitz_real_prod _ hB hlip hcap

end Erdos3

end

end OAI
