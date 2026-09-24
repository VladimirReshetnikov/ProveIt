import Mathlib.Tactic

/-!
# The unsquared arithmetic factor

For a positive divisor `B` and a nonnegative dividend `C`, the refined
relation-combining product can use these parameters without squaring them.
The positive radical offset again leaves exactly divisibility and positivity.
-/

namespace Diophantine.RefinedRelationCombiningArithmetic

theorem sum_rational_of_factor {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
    {B C D T n : ℤ} {s : K} (hB : B ≠ 0)
    (h : (B : K) * n + C -
      (B : K) * (2 * D - 1) * ((C : K) + T + s) = 0) :
    ∃ q : ℚ, s = algebraMap ℚ K q := by
  let b : ℤ := B * (2 * D - 1)
  let a : ℤ := B * n + C - b * (C + T)
  have hb : b ≠ 0 := mul_ne_zero hB (by omega)
  have hbK : (b : K) ≠ 0 := by exact_mod_cast hb
  refine ⟨(a : ℚ) / b, ?_⟩
  simp only [map_div₀, map_intCast]
  apply (eq_div_iff hbK).mpr
  dsimp [a, b]
  push_cast
  linear_combination -h

theorem conditions_of_factor {B C D T : ℤ} {n : ℕ}
    (hB : 0 < B) (hC : 0 ≤ C) (hT : 1 ≤ T)
    (h : B * n + C = B * (2 * D - 1) * (C + T)) :
    B ∣ C ∧ 0 < D := by
  constructor
  · refine ⟨(2 * D - 1) * (C + T) - n, ?_⟩
    nlinarith [h]
  · by_contra hD
    have hd : 2 * D - 1 < 0 := by omega
    have ht : 0 < C + T := by omega
    have hright : B * (2 * D - 1) * (C + T) < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hB hd) ht
    have hleft : 0 ≤ B * n + C := by positivity
    omega

theorem exists_factor_of_conditions {B C D T : ℤ}
    (hB : 0 < B) (hC : 0 ≤ C) (hT : 1 ≤ T) (hdiv : B ∣ C) (hD : 0 < D) :
    ∃ n : ℕ, B * n + C = B * (2 * D - 1) * (C + T) := by
  obtain ⟨k, hk⟩ := hdiv
  have hk0 : 0 ≤ k := by
    by_contra hneg
    have := mul_neg_of_pos_of_neg hB (show k < 0 by omega)
    omega
  have hkC : k ≤ C := by
    have := mul_nonneg (show 0 ≤ B - 1 by omega) hk0
    nlinarith [hk]
  have hd : 1 ≤ 2 * D - 1 := by omega
  have ht : 0 ≤ C + T := by omega
  have hprod : C + T ≤ (2 * D - 1) * (C + T) := by
    nlinarith [mul_nonneg (show 0 ≤ (2 * D - 1) - 1 by omega) ht]
  have hn : 0 ≤ (2 * D - 1) * (C + T) - k := by omega
  refine ⟨((2 * D - 1) * (C + T) - k).toNat, ?_⟩
  rw [Int.toNat_of_nonneg hn, hk]
  ring

theorem factor_iff {B C D T : ℤ} (hB : 0 < B) (hC : 0 ≤ C) (hT : 1 ≤ T) :
    (∃ n : ℕ, B * n + C = B * (2 * D - 1) * (C + T)) ↔
      B ∣ C ∧ 0 < D := by
  constructor
  · rintro ⟨n, hn⟩
    exact conditions_of_factor hB hC hT hn
  · rintro ⟨hdiv, hD⟩
    exact exists_factor_of_conditions hB hC hT hdiv hD

end Diophantine.RefinedRelationCombiningArithmetic
