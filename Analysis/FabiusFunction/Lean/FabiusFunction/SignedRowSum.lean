import FabiusFunction.ThueMorseBinomialLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The signed row sum of Pascal's triangle

This file formalizes the atlas's signed row sum `p1:eq:S-pascal-exact`,

`S(n) = ∑_{k=1}^{n} (-1)^{C(n,k)} = n + 2 - 2^{wt(n) + 1}`,

and the two displays of `p1:cor:mod-three-sine` that rewrite the odd-count
residue formula through it:

* `τ(n) = (2n + S(n)) mod 3`, and
* `τ(n) = (4/3) sin²(π (n - S(n)) / 3)`.

## Idea

Each term `(-1)^{C(n,k)}` is `1 - 2·[C(n,k) odd]`, so the sum over a full row
is `(n+1) - 2 ν(n)` with `ν(n)` the number of odd entries, which the corpus
knows as `card_oddBinomialIndices = 2^{wt(n)}`.  Dropping the `k = 0` term
(always odd, contributing `-1`) gives `S(n)`.  The residue display then
follows from the two-cycle `2^r mod 3 = (r mod 2) + 1` by integer
arithmetic that `omega` discharges once `2^{wt(n)}` is made an atom; the
sine display is the same two-cycle read through `sin²(2π/3) = 3/4`.

## Main declarations

* `signedRowSum n` — `S(n)`.
* `sum_range_neg_one_pow_choose` — the full-row sum `(n+1) - 2^{wt(n)+1}`.
* `signedRowSum_eq` — **`p1:eq:S-pascal-exact`**.
* `thueMorseBit_eq_two_mul_add_signedRowSum_emod_three` — **`p1:eq:pascal-mod3`**.
* `thueMorseBit_eq_sin_sq_pi_sub_signedRowSum_div_three` — **`p1:eq:pascal-sine`**.
-/

set_option autoImplicit false

namespace Fabius

open Finset Real

/-! ## The full-row sum -/

/-- `(-1)^c = 1 - 2·[c odd]`, as integers. -/
theorem neg_one_pow_eq_one_sub_two_ite (c : ℕ) :
    (-1 : ℤ) ^ c = 1 - 2 * (if Odd c then 1 else 0) := by
  rcases Nat.even_or_odd c with h | h
  · rw [h.neg_one_pow, if_neg (Nat.not_odd_iff_even.mpr h)]
    norm_num
  · rw [h.neg_one_pow, if_pos h]
    norm_num

/-- The signed sum over a full row of Pascal's triangle:
`∑_{k=0}^{n} (-1)^{C(n,k)} = (n + 1) - 2^{wt(n)+1}`. -/
theorem sum_range_neg_one_pow_choose (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℤ) ^ n.choose k = (n + 1 : ℤ) - 2 ^ (binaryWeight n + 1) := by
  simp_rw [neg_one_pow_eq_one_sub_two_ite]
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one, ← mul_sum, sum_boole]
  have hset : ((range (n + 1)).filter fun k => Odd (n.choose k)) = oddBinomialIndices n := rfl
  rw [hset, card_oddBinomialIndices]
  push_cast
  ring

/-! ## The signed row sum -/

/-- The atlas's signed row sum `S(n) = ∑_{k=1}^{n} (-1)^{C(n,k)}`. -/
def signedRowSum (n : ℕ) : ℤ := ∑ k ∈ Icc 1 n, (-1 : ℤ) ^ n.choose k

/-- The full-row sum is the `k = 0` term plus `S(n)`. -/
theorem sum_range_neg_one_pow_choose_eq_add_signedRowSum (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℤ) ^ n.choose k = (-1 : ℤ) ^ n.choose 0 + signedRowSum n := by
  have hIcc : Icc 1 n = (range (n + 1)).filter (fun k => 1 ≤ k) := by
    ext k
    simp only [mem_Icc, mem_filter, mem_range]
    omega
  have h0 : (range (n + 1)).filter (fun k => ¬ 1 ≤ k) = {0} := by
    ext k
    simp only [mem_filter, mem_range, mem_singleton]
    omega
  rw [signedRowSum, hIcc,
    ← sum_filter_add_sum_filter_not (range (n + 1)) (fun k => 1 ≤ k)]
  simp only [h0, sum_singleton]
  ring

/-- **`p1:eq:S-pascal-exact`**: `S(n) = n + 2 - 2^{wt(n)+1}`. -/
theorem signedRowSum_eq (n : ℕ) :
    signedRowSum n = (n : ℤ) + 2 - 2 ^ (binaryWeight n + 1) := by
  have h := sum_range_neg_one_pow_choose n
  rw [sum_range_neg_one_pow_choose_eq_add_signedRowSum, Nat.choose_zero_right, pow_one] at h
  linarith

/-! ## The mod-three corollary -/

/-- **`p1:eq:pascal-mod3`**: `τ(n) = (2n + S(n)) mod 3`. -/
theorem thueMorseBit_eq_two_mul_add_signedRowSum_emod_three (n : ℕ) :
    (thueMorseBit n : ℤ) = (2 * n + signedRowSum n) % 3 := by
  rw [signedRowSum_eq, thueMorseBit, pow_succ]
  have h2 : ((2 : ℤ) ^ binaryWeight n) % 3 = ((binaryWeight n % 2 + 1 : ℕ) : ℤ) := by
    exact_mod_cast two_pow_mod_three_eq_mod_two_add_one (binaryWeight n)
  push_cast at h2 ⊢
  generalize (2 : ℤ) ^ binaryWeight n = t at h2 ⊢
  omega

/-- `n - S(n) = 2^{wt(n)+1} - 2` is `6k` or `6k + 2` according to the parity of
`wt(n)`: the integer `k` is exhibited explicitly. -/
theorem two_pow_succ_sub_two_eq (n : ℕ) :
    ∃ k : ℤ, (2 : ℤ) ^ (binaryWeight n + 1) - 2 = 6 * k + 2 * (thueMorseBit n : ℤ) := by
  have h2 : ((2 : ℤ) ^ binaryWeight n) % 3 = ((binaryWeight n % 2 + 1 : ℕ) : ℤ) := by
    exact_mod_cast two_pow_mod_three_eq_mod_two_add_one (binaryWeight n)
  rw [thueMorseBit, pow_succ]
  push_cast at h2 ⊢
  generalize (2 : ℤ) ^ binaryWeight n = t at h2 ⊢
  refine ⟨(t - 1 - (binaryWeight n : ℤ) % 2) / 3, ?_⟩
  omega

/-- `sin²(2π/3) = 3/4`. -/
theorem sin_sq_two_pi_div_three : Real.sin (2 * π / 3) ^ 2 = 3 / 4 := by
  have h : 2 * π / 3 = π - π / 3 := by ring
  rw [h, Real.sin_pi_sub, Real.sin_sq, Real.cos_pi_div_three]
  norm_num

/-- **`p1:eq:pascal-sine`**: `τ(n) = (4/3) sin²(π (n - S(n)) / 3)`. -/
theorem thueMorseBit_eq_sin_sq_pi_sub_signedRowSum_div_three (n : ℕ) :
    (thueMorseBit n : ℝ) = 4 / 3 * Real.sin (π * ((n : ℝ) - signedRowSum n) / 3) ^ 2 := by
  obtain ⟨k, hk⟩ := two_pow_succ_sub_two_eq n
  have hS : ((n : ℝ) - signedRowSum n) = 6 * k + 2 * (thueMorseBit n : ℝ) := by
    have h := signedRowSum_eq n
    have hk' : ((2 : ℤ) ^ (binaryWeight n + 1) - 2 : ℤ) = 6 * k + 2 * (thueMorseBit n : ℤ) := hk
    have : (signedRowSum n : ℝ) = (n : ℝ) + 2 - 2 ^ (binaryWeight n + 1) := by
      exact_mod_cast h
    have hkR : ((2 : ℝ) ^ (binaryWeight n + 1) - 2) = 6 * k + 2 * (thueMorseBit n : ℝ) := by
      exact_mod_cast hk'
    linarith
  rw [hS]
  have harg : π * (6 * (k : ℝ) + 2 * (thueMorseBit n : ℝ)) / 3
      = (thueMorseBit n : ℝ) * (2 * π / 3) + k * (2 * π) := by ring
  rw [harg, Real.sin_add_int_mul_two_pi]
  have hb : thueMorseBit n = 0 ∨ thueMorseBit n = 1 := by
    have := thueMorseBit_le_one n
    omega
  rcases hb with h | h <;> rw [h] <;> push_cast
  · simp
  · rw [one_mul, sin_sq_two_pi_div_three]
    norm_num

end Fabius
