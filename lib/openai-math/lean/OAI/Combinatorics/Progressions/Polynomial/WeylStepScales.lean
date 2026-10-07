import Mathlib

namespace OAI

section

namespace Erdos3

def weylNextBudget (k B K : ℕ) : ℕ :=
  2 * K + 32 * B ^ 2 + 128 * B ^ 2 * K +
    65536 * 2 ^ k * B ^ 4 * K ^ 3 +
    128 * (k + 1) * B ^ 2 * K ^ 2 + 98304 * 2 ^ k * B ^ 4 * K ^ 3

theorem weylNextBudget_bounds (k B K : ℕ) :
    2 * K ≤ weylNextBudget k B K ∧
    32 * B ^ 2 ≤ weylNextBudget k B K ∧
    128 * B ^ 2 * K ≤ weylNextBudget k B K ∧
    65536 * 2 ^ k * B ^ 4 * K ^ 3 ≤ weylNextBudget k B K ∧
    128 * (k + 1) * B ^ 2 * K ^ 2 ≤ weylNextBudget k B K ∧
    98304 * 2 ^ k * B ^ 4 * K ^ 3 ≤ weylNextBudget k B K := by
  unfold weylNextBudget
  omega

def weylBudget : ℕ → ℕ → ℕ
  | 0, B => B
  | j + 1, B => weylNextBudget (j + 1) B (weylBudget j (8 * B ^ 2))

theorem weylBudget_pos (j : ℕ) {B : ℕ} (hB : 0 < B) : 0 < weylBudget j B := by
  cases j with
  | zero => exact hB
  | succ j =>
    have hb : 0 < 32 * B ^ 2 := by positivity
    exact lt_of_lt_of_le hb (weylNextBudget_bounds _ _ _).2.1

end Erdos3

end

section

namespace Erdos3

open Polynomial
open scoped BigOperators

noncomputable def weylBudgetPolynomial : ℕ → Polynomial ℕ
  | 0 => X
  | j + 1 =>
    let R := (weylBudgetPolynomial j).comp (C 8 * X ^ 2)
    C 2 * R + C 32 * X ^ 2 + C 128 * X ^ 2 * R +
      C (65536 * 2 ^ (j + 1)) * X ^ 4 * R ^ 3 +
      C (128 * (j + 2)) * X ^ 2 * R ^ 2 + C (98304 * 2 ^ (j + 1)) * X ^ 4 * R ^ 3

theorem weylBudgetPolynomial_eval (j B : ℕ) :
    (weylBudgetPolynomial j).eval B = weylBudget j B := by
  induction j generalizing B with
  | zero => simp only [weylBudgetPolynomial, eval_X, weylBudget]
  | succ j ih =>
    simp only [weylBudgetPolynomial, eval_add, eval_mul, eval_pow, eval_C, eval_X,
      eval_comp, ih, weylBudget, weylNextBudget]

theorem natPolynomial_eval_le_one_mul_pow (P : Polynomial ℕ) {B : ℕ} (hB : 1 ≤ B) :
    P.eval B ≤ P.eval 1 * B ^ P.natDegree := by
  rw [eval_eq_sum_range, eval_eq_sum_range]
  simp only [one_pow, mul_one, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  exact Nat.mul_le_mul_left _ (pow_le_pow_right' hB (by simpa only [Finset.mem_range,
    Nat.lt_succ_iff] using hi))

theorem weylBudget_polynomial_bound (j : ℕ) :
    ∃ A d : ℕ, 0 < A ∧ 0 < d ∧ ∀ B : ℕ, 1 ≤ B → weylBudget j B ≤ A * B ^ d := by
  let P := weylBudgetPolynomial j
  refine ⟨P.eval 1, P.natDegree + 1, ?_, by omega, ?_⟩
  · change 0 < (weylBudgetPolynomial j).eval 1
    rw [weylBudgetPolynomial_eval]
    exact weylBudget_pos j (by decide)
  · intro B hB
    rw [← weylBudgetPolynomial_eval]
    exact (natPolynomial_eval_le_one_mul_pow P hB).trans
      (Nat.mul_le_mul_left _ (pow_le_pow_right' hB (by omega)))

end Erdos3

end

section

namespace Erdos3

def weylShiftDenom (B K : ℕ) : ℕ := 128 * B ^ 2 * K

noncomputable def weylShiftDensity (B K : ℕ) : ℝ := 1 / (32 * (B : ℝ) ^ 2 * K)

noncomputable def weylShiftError (k N K : ℕ) : ℝ := (2 : ℝ) ^ k * K / (N : ℝ) ^ k

theorem weylShiftDenom_pos {B K : ℕ} (hB : 0 < B) (hK : 0 < K) :
    0 < weylShiftDenom B K := by unfold weylShiftDenom; positivity

theorem weylShiftDensity_pos {B K : ℕ} (hB : 0 < B) (hK : 0 < K) :
    0 < weylShiftDensity B K := by unfold weylShiftDensity; positivity

theorem weylShiftDensity_le_one {B K : ℕ} (hB : 0 < B) (hK : 0 < K) :
    weylShiftDensity B K ≤ 1 := by
  have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  unfold weylShiftDensity
  apply (div_le_one (by positivity : 0 < 32 * (B : ℝ) ^ 2 * K)).mpr
  have hsq : (1 : ℝ) ≤ (B : ℝ) ^ 2 := one_le_pow₀ hBR
  nlinarith only [mul_le_mul hsq hKR (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg (B : ℝ))]

theorem weylShiftDensity_mul_denom {B K : ℕ} (hB : 0 < B) (hK : 0 < K) :
    weylShiftDensity B K * weylShiftDenom B K = 4 := by
  unfold weylShiftDensity weylShiftDenom
  push_cast
  have hb : (B : ℝ) ≠ 0 := by positivity
  have hk : (K : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem weylShiftDensity_card_bound {N B K : ℕ} (hB : 0 < B) (hK : 0 < K)
    (hN : 2 ≤ N) :
    (K : ℝ) * (weylShiftDensity B K * N) ≤ (1 / (B : ℝ)) ^ 2 * (N / 2 : ℕ) / 8 := by
  have hb : (B : ℝ) ≠ 0 := by positivity
  have hk : (K : ℝ) ≠ 0 := by positivity
  have hn : (N : ℝ) ≤ 4 * (N / 2 : ℕ) := by exact_mod_cast (show N ≤ 4 * (N / 2) by omega)
  have hleft : (K : ℝ) * (weylShiftDensity B K * N) = (N : ℝ) / (32 * (B : ℝ) ^ 2) := by
    unfold weylShiftDensity
    field_simp
  have hright : (1 / (B : ℝ)) ^ 2 * (N / 2 : ℕ) / 8 =
      (4 * (N / 2 : ℕ) : ℝ) / (32 * (B : ℝ) ^ 2) := by field_simp; ring
  rw [hleft, hright]
  exact div_le_div_of_nonneg_right hn (by positivity)

theorem weylShiftError_small {k N B K : ℕ} (hk : 0 < k) (hB : 0 < B)
    (hK : 0 < K) (hN : 0 < N)
    (hlarge : 65536 * 2 ^ k * B ^ 4 * K ^ 3 ≤ N) :
    16 * ((weylShiftDenom B K : ℝ) * weylShiftError k N K) ≤ weylShiftDensity B K := by
  have hBR : (B : ℝ) ≠ 0 := by positivity
  have hKR : (K : ℝ) ≠ 0 := by positivity
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpower : (N : ℝ) ≤ (N : ℝ) ^ k := le_self_pow₀ hNR hk.ne'
  have hl : (65536 : ℝ) * 2 ^ k * (B : ℝ) ^ 4 * (K : ℝ) ^ 3 ≤ (N : ℝ) ^ k :=
    (by exact_mod_cast hlarge : (65536 : ℝ) * 2 ^ k * (B : ℝ) ^ 4 * (K : ℝ) ^ 3 ≤ N).trans hpower
  unfold weylShiftDensity
  apply (le_div_iff₀ (by positivity : 0 < 32 * (B : ℝ) ^ 2 * K)).mpr
  have hid : 16 * ((weylShiftDenom B K : ℝ) * weylShiftError k N K) *
      (32 * (B : ℝ) ^ 2 * K) =
      (65536 * (2 : ℝ) ^ k * (B : ℝ) ^ 4 * (K : ℝ) ^ 3) / (N : ℝ) ^ k := by
    unfold weylShiftDenom weylShiftError
    push_cast
    ring
  rw [hid]
  exact (div_le_one (by positivity : 0 < (N : ℝ) ^ k)).mpr hl

theorem weylShiftError_of_half_length {k N M K : ℕ} (hM : 0 < M) (hN : 0 < N)
    (hhalf : N ≤ 2 * M) :
    (K : ℝ) / (M : ℝ) ^ k ≤ weylShiftError k N K := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : (N : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast hhalf
  have hp := pow_le_pow_left₀ hNR.le hh k
  rw [mul_pow] at hp
  unfold weylShiftError
  apply (div_le_div_iff₀ (by positivity : 0 < (M : ℝ) ^ k) (by positivity : 0 < (N : ℝ) ^ k)).mpr
  have hm := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (α := ℝ) K)
  nlinarith only [hm]

theorem weylShiftError_output (k N B K : ℕ) :
    24 * weylShiftDenom B K * weylShiftError k N K / (weylShiftDensity B K * N) =
      (98304 * (2 : ℝ) ^ k * (B : ℝ) ^ 4 * (K : ℝ) ^ 3) / (N : ℝ) ^ (k + 1) := by
  unfold weylShiftDenom weylShiftError weylShiftDensity
  push_cast
  rw [pow_succ]
  field_simp
  ring

end Erdos3

end

end OAI
