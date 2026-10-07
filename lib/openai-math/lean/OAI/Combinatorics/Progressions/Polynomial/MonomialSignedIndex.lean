import Mathlib

namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_positive_monomial_index (Λ : Submodule ℤ E) (α : E) (k N : ℕ)
    (n : ℤ) (hn : n ≠ 0) (hnN : |n| ≤ (N : ℤ))
    (m : E) (hm : m ∈ Λ) {R : ℝ} (happrox : ‖(n : ℝ) ^ k • α - m‖ < R) :
    ∃ q : ℕ, 0 < q ∧ q ≤ N ∧ ∃ v ∈ Λ, ‖(q : ℝ) ^ k • α - v‖ < R := by
  by_cases hsign : 0 ≤ n
  · let q := n.toNat
    have hqZ : (q : ℤ) = n := Int.toNat_of_nonneg hsign
    have hqR : (q : ℝ) = (n : ℝ) := by exact_mod_cast hqZ
    refine ⟨q, by omega, ?_, m, hm, ?_⟩
    · rw [abs_of_nonneg hsign] at hnN
      omega
    · simpa only [hqR] using happrox
  · let q := (-n).toNat
    have hqZ : (q : ℤ) = -n := Int.toNat_of_nonneg (by omega)
    have hqR : (q : ℝ) = -(n : ℝ) := by exact_mod_cast hqZ
    have hv : (-1 : ℝ) ^ k • m ∈ Λ := by
      have h := Λ.smul_mem ((-1 : ℤ) ^ k) hm
      simpa only [← Int.cast_smul_eq_zsmul ℝ, Int.cast_pow, Int.cast_neg, Int.cast_one] using h
    refine ⟨q, by omega, ?_, (-1 : ℝ) ^ k • m, hv, ?_⟩
    · rw [abs_of_neg (by omega)] at hnN
      omega
    · rw [hqR, neg_eq_neg_one_mul, mul_pow, mul_smul, ← smul_sub, norm_smul]
      simpa only [norm_pow, norm_neg, norm_one, one_pow, one_mul] using happrox

end Erdos3

end

end OAI
