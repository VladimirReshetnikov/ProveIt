import OAI.Combinatorics.Progressions.Fourier.IntegerSupportTorus
import OAI.Combinatorics.Progressions.Lattices.WeightedModerateIntegerSupport

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def blockJetScaleBound (q h b : ℕ) (A : ℝ) : ℝ :=
  b * 2 ^ h * ((q + 1 : ℕ) : ℝ) ^ h * A

theorem blockJetScaleBound_nonneg (q h b : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    0 ≤ blockJetScaleBound q h b A := by unfold blockJetScaleBound; positivity

theorem weightedCubeJetBound_le_scale {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
    {n : ℕ} (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    {A K : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hvol : ∀ b, (∏ j, ((s b j).length : ℝ)) ≤ A * K)
    (S : Finset I) (hS : S.card ≤ n + 1) :
    (weightedCubeJetBound s S : ℝ) ≤ blockJetScaleBound (Fintype.card I) (n + 1) (Fintype.card B) A * K := by
  classical
  simp only [weightedCubeJetBound, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    Int.cast_prod, Int.cast_natCast, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  calc
    _ ≤ ∑ _b : B, (2 : ℝ) ^ (n + 1) * ((Fintype.card I + 1 : ℕ) : ℝ) ^ (n + 1) * (A * K) := by
      apply Finset.sum_le_sum
      intro b _
      calc
        _ ≤ (2 : ℝ) ^ S.card * (((Fintype.card I + 1 : ℕ) : ℝ) ^ (n + 1) * (A * K)) := by
          gcongr
          exact hvol b
        _ ≤ _ := by
          have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hS
          have hh := mul_le_mul_of_nonneg_right hp
            (show 0 ≤ ((Fintype.card I + 1 : ℕ) : ℝ) ^ (n + 1) * (A * K) by positivity)
          nlinarith only [hh]
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, blockJetScaleBound]; ring

theorem weightedModerateJetBound_le_scale {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
    {n : ℕ} (c : B → NormalizedScalarCubeSource Empty)
    (s : B → Fin n → NormalizedScalarCubeSource I) (offset : B → ℤ)
    {A K : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hvol : ∀ b, (|(offset b : ℝ)| + (c b).length) * (∏ j, ((s b j).length : ℝ)) ≤ A * K)
    (S : Finset I) (hS : S.card ≤ n) :
    (weightedModerateJetBound c s offset S : ℝ) ≤
      blockJetScaleBound (Fintype.card I) n (Fintype.card B) A * K := by
  classical
  simp only [weightedModerateJetBound, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    Int.cast_prod, Int.cast_natCast, Int.cast_add, Int.cast_abs, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc
    _ = ∑ b : B, (2 : ℝ) ^ S.card * ((Fintype.card I + 1 : ℕ) : ℝ) ^ n *
        ((|(offset b : ℝ)| + (c b).length) * (∏ j, ((s b j).length : ℝ))) := by
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ ≤ ∑ _b : B, (2 : ℝ) ^ n * ((Fintype.card I + 1 : ℕ) : ℝ) ^ n * (A * K) := by
      apply Finset.sum_le_sum
      intro b _
      calc
        _ ≤ (2 : ℝ) ^ S.card * ((Fintype.card I + 1 : ℕ) : ℝ) ^ n * (A * K) := by
          exact mul_le_mul_of_nonneg_left (hvol b) (by positivity)
        _ ≤ _ := by
          have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hS
          have hh := mul_le_mul_of_nonneg_right hp
            (show 0 ≤ ((Fintype.card I + 1 : ℕ) : ℝ) ^ n * (A * K) by positivity)
          nlinarith only [hh]
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, blockJetScaleBound]; ring

end Erdos3

end

end OAI
