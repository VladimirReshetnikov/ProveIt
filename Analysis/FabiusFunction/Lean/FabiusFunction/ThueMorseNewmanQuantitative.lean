import FabiusFunction.ThueMorseNewman
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Newman's theorem, quantitative form

`ThueMorseNewman` proves the *sign* of Newman's phenomenon: the
multiples of three below `N` with even binary weight outnumber those
with odd binary weight, `N₃(N) = T₀(N) ≥ 1`.  Newman (1969) also gave
the *size*: `N₃(N)` grows like `N^α` with `α = log₄3 = 0.7924…`, his
constants being `1/20 < N₃(N)/N^α < 5`.  This module derives the growth
from the same base-four step bracket

`3·T₀(M) - 2 ≤ T₀(4M+s) ≤ 3·T₀(M) + 2`   (`s < 4`)

by iterating it: subtracting `1` turns the lower bound into
`T₀(4M+s) - 1 ≥ 3·(T₀(M) - 1)`, adding `1` turns the upper bound into
`T₀(4M+s) + 1 ≤ 3·(T₀(M) + 1)`, and each base-four digit contributes
one factor of `3`.  Since `3 = 4^α`, a cutoff with `k` base-four digits
above the seed contributes `3^k = (4^k)^α`.

* `two_le_thueMorseResidueSum_three_zero` — the seed `T₀(N) ≥ 2` for
  `N ≥ 4`, from the sixteen values `T₀(0..15)` and the bracket.
* `three_pow_add_one_le_thueMorseResidueSum_three_zero` — the integer
  lower bound `T₀(N) ≥ 3^k + 1` for `N ≥ 4^(k+1)`.
* `thueMorseResidueSum_three_zero_add_one_le` — the integer upper bound
  `T₀(N) + 1 ≤ 2·3^k` for `N < 4^(k+1)`.
* `newman_lower_bound`, `newman_upper_bound` — **the quantitative
  Newman theorem**: for every `N ≥ 1`,

  `N^(log₄3) / 9 ≤ N₃(N) ≤ 2·N^(log₄3)`,

  with constants `1/9` and `2` that improve Newman's `1/20` and `5`
  (numerically the ratio `N₃(N)/N^α` ranges over `[0.418…, 1]` for
  `N < 2^16`).
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ## The first sixteen values -/

private theorem sign_four : thueMorseSign 4 = -1 := by
  have h := thueMorseSign_two_mul 2
  norm_num at h
  exact h

private theorem sign_three : thueMorseSign 3 = 1 := by
  have h := thueMorseSign_two_mul_add_one 1
  norm_num at h
  exact h

private theorem sign_five : thueMorseSign 5 = 1 := by
  have h := thueMorseSign_two_mul_add_one 2
  norm_num at h
  exact h

private theorem sign_six : thueMorseSign 6 = 1 := by
  have h := thueMorseSign_two_mul 3
  norm_num [sign_three] at h
  exact h

private theorem sign_seven : thueMorseSign 7 = -1 := by
  have h := thueMorseSign_two_mul_add_one 3
  norm_num [sign_three] at h
  exact h

private theorem sign_eight : thueMorseSign 8 = -1 := by
  have h := thueMorseSign_two_mul 4
  norm_num [sign_four] at h
  exact h

private theorem sign_nine : thueMorseSign 9 = 1 := by
  have h := thueMorseSign_two_mul_add_one 4
  norm_num [sign_four] at h
  exact h

private theorem sign_ten : thueMorseSign 10 = 1 := by
  have h := thueMorseSign_two_mul 5
  norm_num [sign_five] at h
  exact h

private theorem sign_eleven : thueMorseSign 11 = -1 := by
  have h := thueMorseSign_two_mul_add_one 5
  norm_num [sign_five] at h
  exact h

private theorem sign_twelve : thueMorseSign 12 = 1 := by
  have h := thueMorseSign_two_mul 6
  norm_num [sign_six] at h
  exact h

private theorem sign_thirteen : thueMorseSign 13 = -1 := by
  have h := thueMorseSign_two_mul_add_one 6
  norm_num [sign_six] at h
  exact h

private theorem sign_fourteen : thueMorseSign 14 = -1 := by
  have h := thueMorseSign_two_mul 7
  norm_num [sign_seven] at h
  exact h

private theorem sign_fifteen : thueMorseSign 15 = 1 := by
  have h := thueMorseSign_two_mul_add_one 7
  norm_num [sign_seven] at h
  exact h

/-- **The seed**: `T₀(N) ≥ 2` for every `N ≥ 4`.  On `4 ≤ N < 16` this
is read off the first sixteen signs (`T₀ = 2,2,2,3,3,3,4,4,4,5,5,5`);
beyond, the bracket gives `T₀(N) ≥ 3·2 - 2 = 4`. -/
theorem two_le_thueMorseResidueSum_three_zero : ∀ N : ℕ, 4 ≤ N →
    2 ≤ thueMorseResidueSum 3 0 N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    by_cases h16 : N < 16
    · interval_cases N <;>
        norm_num [thueMorseResidueSum, Finset.sum_range_succ, sign_three,
          sign_four, sign_five, sign_six, sign_seven, sign_eight,
          sign_nine, sign_ten, sign_eleven, sign_twelve, sign_thirteen,
          sign_fourteen, sign_fifteen]
    · have hIH := ih (N / 4) (by omega) (by omega)
      have hb := (thueMorseResidueSum_three_zero_bracket N).1
      linarith

/-! ## Integer growth bounds -/

/-- **Integer lower bound**: `T₀(N) ≥ 3^k + 1` whenever `N ≥ 4^(k+1)`.
Each base-four digit above the seed multiplies `T₀ - 1` by at least
three. -/
theorem three_pow_add_one_le_thueMorseResidueSum_three_zero (k : ℕ) :
    ∀ N : ℕ, 4 * 4 ^ k ≤ N →
      (3 : ℤ) ^ k + 1 ≤ thueMorseResidueSum 3 0 N := by
  induction k with
  | zero =>
      intro N hN
      have h := two_le_thueMorseResidueSum_three_zero N (by simpa using hN)
      simpa using h
  | succ k ih =>
      intro N hN
      have hM : 4 * 4 ^ k ≤ N / 4 := by
        rw [pow_succ] at hN
        omega
      have hIH := ih (N / 4) hM
      have hb := (thueMorseResidueSum_three_zero_bracket N).1
      rw [pow_succ]
      linarith

/-- **Integer upper bound**: `T₀(N) + 1 ≤ 2·3^k` whenever `N < 4^(k+1)`.
Each base-four digit multiplies `T₀ + 1` by at most three, starting
from `T₀(0..3) + 1 ≤ 2`. -/
theorem thueMorseResidueSum_three_zero_add_one_le (k : ℕ) :
    ∀ N : ℕ, N < 4 ^ (k + 1) →
      thueMorseResidueSum 3 0 N + 1 ≤ 2 * (3 : ℤ) ^ k := by
  induction k with
  | zero =>
      intro N hN
      rw [thueMorseResidueSum_three_zero_of_lt_four N (by simpa using hN)]
      split_ifs <;> norm_num
  | succ k ih =>
      intro N hN
      have hM : N / 4 < 4 ^ (k + 1) := by
        rw [pow_succ] at hN
        omega
      have hIH := ih (N / 4) hM
      have hb := (thueMorseResidueSum_three_zero_bracket N).2
      rw [pow_succ]
      linarith

/-! ## The power law -/

/-- `(4^j)^(log₄3) = 3^j`. -/
theorem four_pow_rpow_logb_four_three (j : ℕ) :
    ((4 : ℝ) ^ j) ^ (Real.logb 4 3) = (3 : ℝ) ^ j := by
  have h43 : (4 : ℝ) ^ (Real.logb 4 3) = 3 :=
    Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
    Real.rpow_mul (by norm_num), h43, Real.rpow_natCast]

/-- **The quantitative Newman theorem, lower bound**: for every
`N ≥ 1`, `N₃(N) ≥ N^(log₄3) / 9`.  (Newman's constant was `1/20`.) -/
theorem newman_lower_bound (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) ^ (Real.logb 4 3) / 9 ≤ (thueMorseResidueSum 3 0 N : ℝ) := by
  have hα : 0 ≤ Real.logb 4 3 := Real.logb_nonneg (by norm_num) (by norm_num)
  by_cases h4 : N < 4
  · -- `T₀ = 1` and `N^α ≤ 4^α = 3`
    rw [thueMorseResidueSum_three_zero_of_lt_four N h4, if_neg (by omega)]
    have hle : (N : ℝ) ^ (Real.logb 4 3) ≤ (4 : ℝ) ^ (Real.logb 4 3) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast h4.le) hα
    rw [Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)] at hle
    push_cast
    linarith
  · -- `4^(k+1) ≤ N < 4^(k+2)` with `k + 1 = log₄ N`
    obtain ⟨k, hk⟩ : ∃ k, Nat.log 4 N = k + 1 := by
      have h1 : 0 < Nat.log 4 N := Nat.log_pos (by norm_num) (by omega)
      exact ⟨Nat.log 4 N - 1, by omega⟩
    have hlow : 4 ^ (k + 1) ≤ N := by
      have := Nat.pow_log_le_self 4 (by omega : N ≠ 0)
      rwa [hk] at this
    have hhigh : N < 4 ^ (k + 2) := by
      have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 4) N
      rwa [hk] at this
    have hint := three_pow_add_one_le_thueMorseResidueSum_three_zero k N
      (by rw [pow_succ] at hlow; linarith)
    have hreal : (N : ℝ) ^ (Real.logb 4 3) ≤ (3 : ℝ) ^ (k + 2) := by
      rw [← four_pow_rpow_logb_four_three]
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hhigh.le) hα
    have hcast : ((3 : ℤ) ^ k + 1 : ℤ) ≤ thueMorseResidueSum 3 0 N := hint
    have hcast' : ((3 : ℝ) ^ k + 1 : ℝ) ≤ (thueMorseResidueSum 3 0 N : ℝ) := by
      exact_mod_cast hcast
    have h9 : (3 : ℝ) ^ (k + 2) = 9 * 3 ^ k := by ring
    linarith

/-- **The quantitative Newman theorem, upper bound**: for every `N`,
`N₃(N) ≤ 2·N^(log₄3)`.  (Newman's constant was `5`.) -/
theorem newman_upper_bound (N : ℕ) :
    (thueMorseResidueSum 3 0 N : ℝ) ≤ 2 * (N : ℝ) ^ (Real.logb 4 3) := by
  have hα : 0 ≤ Real.logb 4 3 := Real.logb_nonneg (by norm_num) (by norm_num)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [thueMorseResidueSum_three_zero_of_lt_four 0 (by norm_num), if_pos rfl]
    push_cast
    positivity
  · set k := Nat.log 4 N with hk
    have hlow : 4 ^ k ≤ N := Nat.pow_log_le_self 4 hN.ne'
    have hhigh : N < 4 ^ (k + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num : 1 < 4) N
    have hint := thueMorseResidueSum_three_zero_add_one_le k N hhigh
    have hreal : (3 : ℝ) ^ k ≤ (N : ℝ) ^ (Real.logb 4 3) := by
      rw [← four_pow_rpow_logb_four_three]
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hlow) hα
    have hcast : (thueMorseResidueSum 3 0 N : ℝ) + 1 ≤ 2 * (3 : ℝ) ^ k := by
      exact_mod_cast hint
    linarith

/-- **The quantitative Newman theorem** (two-sided): for every `N ≥ 1`,
`N^(log₄3) / 9 ≤ N₃(N) ≤ 2·N^(log₄3)`. -/
theorem newman_quantitative (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) ^ (Real.logb 4 3) / 9 ≤ (thueMorseResidueSum 3 0 N : ℝ) ∧
      (thueMorseResidueSum 3 0 N : ℝ) ≤ 2 * (N : ℝ) ^ (Real.logb 4 3) :=
  ⟨newman_lower_bound N hN, newman_upper_bound N⟩

end Fabius
