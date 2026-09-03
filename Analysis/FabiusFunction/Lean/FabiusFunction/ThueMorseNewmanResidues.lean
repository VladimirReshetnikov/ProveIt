import FabiusFunction.ThueMorseNewmanQuantitative

/-!
# Newman's phenomenon in the other residue classes modulo three

Newman's theorem concerns the class `n ≡ 0 (mod 3)`, where even binary
weights dominate: `T₀(N) ≥ 1` and `T₀(N) ≍ N^(log₄3)`.  The base-four
bracket `|T_r(4M+s) - 3·T_r(M)| ≤ 2` of `ThueMorseNewman` holds for
**every** residue class, and in the class `n ≡ 1 (mod 3)` the same
amplification runs in the opposite direction: odd weights dominate,

`T₁(N) ≤ -1`  for all `N ≥ 2`,   and   `N^(log₄3)/27 ≤ -T₁(N) ≤ 2·N^(log₄3)`.

(Numerically `-T₁(N)/N^α ∈ [0.262, 0.578]` for `2 ≤ N ≤ 2^16`.)  The
class `n ≡ 2 (mod 3)` has no such one-sided law: `T₂(2^m) = 0` for
every odd `m`, since `T₂(2) = 0` and `T₂(4M) = 3·T₂(M)` at `M = 2^k`
with `k ≥ 1`; it does obey the two-sided bound `|T₂(N)| ≤ 2·N^(log₄3)`.

* `thueMorseResidueSum_three_one_le_neg_one` — **negativity**
  `T₁(N) ≤ -1` for `N ≥ 2`.
* `two_le_neg_thueMorseResidueSum_three_one` — the seed `-T₁(N) ≥ 2`
  for `N ≥ 5`.
* `three_pow_add_one_le_neg_thueMorseResidueSum_three_one` — the
  integer lower bound `-T₁(N) ≥ 3^k + 1` for `N ≥ 16·4^k`.
* `newman_residue_one_lower_bound`, `newman_residue_one_upper_bound` —
  **the quantitative form** `N^(log₄3)/27 ≤ -T₁(N) ≤ 2·N^(log₄3)`.
* `neg_thueMorseResidueSum_three_two_le`,
  `abs_thueMorseResidueSum_three_le` — the two-sided bound
  `|T_r(N)| ≤ 2·N^(log₄3)` for every residue class.
* `thueMorseResidueSum_three_two_two_pow_odd` — the vanishing
  `T₂(2^(2j+1)) = 0`, which rules out a one-sided law for `r = 2`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- **Negativity in the class one**: `T₁(N) ≤ -1` for every `N ≥ 2`,
the mirror image of Newman's positivity theorem: from the bracket,
`T₁(N) ≤ 3·T₁(N/4) + 2 ≤ -3 + 2 = -1` by strong induction, seeded by
`T₁(2..7) = -1, -1, -1, -2, -2, -2`. -/
theorem thueMorseResidueSum_three_one_le_neg_one : ∀ N : ℕ, 2 ≤ N →
    thueMorseResidueSum 3 1 N ≤ -1 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    by_cases h8 : N < 8
    · interval_cases N <;> decide
    · have hIH := ih (N / 4) (by omega) (by omega)
      have hb := (thueMorseResidueSum_three_bracket 1 (by norm_num) N).2
      linarith

/-- The seed for the class one: `-T₁(N) ≥ 2` for every `N ≥ 5`. -/
theorem two_le_neg_thueMorseResidueSum_three_one : ∀ N : ℕ, 5 ≤ N →
    2 ≤ -thueMorseResidueSum 3 1 N :=
  two_le_of_step (U := fun N => -thueMorseResidueSum 3 1 N) (N₀ := 5)
    (by norm_num)
    (fun N => by
      have h := (thueMorseResidueSum_three_bracket 1 (by norm_num) N).2
      linarith)
    (fun N h1 h2 => by interval_cases N <;> decide)

/-- **Integer lower bound** in the class one: `-T₁(N) ≥ 3^k + 1`
whenever `N ≥ 16·4^k`. -/
theorem three_pow_add_one_le_neg_thueMorseResidueSum_three_one (k : ℕ) :
    ∀ N : ℕ, 16 * 4 ^ k ≤ N →
      (3 : ℤ) ^ k + 1 ≤ -thueMorseResidueSum 3 1 N :=
  three_pow_add_one_le_of_step (U := fun N => -thueMorseResidueSum 3 1 N)
    (N₀ := 16) (by norm_num)
    (fun N => by
      have h := (thueMorseResidueSum_three_bracket 1 (by norm_num) N).2
      linarith)
    (fun N h1 _ => two_le_neg_thueMorseResidueSum_three_one N (by omega)) k

/-- **Integer upper bound** in the class one: `-T₁(N) + 1 ≤ 2·3^k`
whenever `N < 4^(k+1)`. -/
theorem neg_thueMorseResidueSum_three_one_add_one_le (k : ℕ) :
    ∀ N : ℕ, N < 4 ^ (k + 1) →
      -thueMorseResidueSum 3 1 N + 1 ≤ 2 * (3 : ℤ) ^ k :=
  add_one_le_two_mul_three_pow_of_step
    (U := fun N => -thueMorseResidueSum 3 1 N)
    (fun N => by
      have h := (thueMorseResidueSum_three_bracket 1 (by norm_num) N).1
      linarith)
    (fun N hN => by interval_cases N <;> decide) k

/-- **Integer upper bound** in the class two: `-T₂(N) + 1 ≤ 2·3^k`
whenever `N < 4^(k+1)`. -/
theorem neg_thueMorseResidueSum_three_two_add_one_le (k : ℕ) :
    ∀ N : ℕ, N < 4 ^ (k + 1) →
      -thueMorseResidueSum 3 2 N + 1 ≤ 2 * (3 : ℤ) ^ k :=
  add_one_le_two_mul_three_pow_of_step
    (U := fun N => -thueMorseResidueSum 3 2 N)
    (fun N => by
      have h := (thueMorseResidueSum_three_bracket 2 (by norm_num) N).1
      linarith)
    (fun N hN => by interval_cases N <;> decide) k

/-- **The quantitative law in the class one, lower bound**: for every
`N ≥ 2`, `-T₁(N) ≥ N^(log₄3) / 27`.  For `N ≥ 16` this is the
amplification with `16^(log₄3) = 9`; for `2 ≤ N < 16` it is
`-T₁(N) ≥ 1 ≥ N^(log₄3)/27` since `N^(log₄3) < 16^(log₄3) = 9`. -/
theorem newman_residue_one_lower_bound (N : ℕ) (hN : 2 ≤ N) :
    (N : ℝ) ^ (Real.logb 4 3) / 27 ≤ -(thueMorseResidueSum 3 1 N : ℝ) := by
  have hα : 0 ≤ Real.logb 4 3 := Real.logb_nonneg (by norm_num) (by norm_num)
  have h16 : ((16 : ℕ) : ℝ) ^ (Real.logb 4 3) = 9 := by
    rw [show ((16 : ℕ) : ℝ) = (4 : ℝ) ^ 2 by norm_num,
      four_pow_rpow_logb_four_three]
    norm_num
  by_cases h : N < 16
  · have hle : (N : ℝ) ^ (Real.logb 4 3) ≤ ((16 : ℕ) : ℝ) ^ (Real.logb 4 3) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast h.le) hα
    rw [h16] at hle
    have h1 : (thueMorseResidueSum 3 1 N : ℝ) ≤ -1 := by
      exact_mod_cast thueMorseResidueSum_three_one_le_neg_one N hN
    linarith
  · have hmain := rpow_div_le_of_three_pow_le
      (U := fun N => -thueMorseResidueSum 3 1 N) (N₀ := 16) (by norm_num)
      (fun k N hk => three_pow_add_one_le_neg_thueMorseResidueSum_three_one k N hk)
      N (by omega)
    rw [h16] at hmain
    have h27 : (3 : ℝ) * 9 = 27 := by norm_num
    rw [h27] at hmain
    simpa using hmain

/-- **The quantitative law in the class one, upper bound**:
`-T₁(N) ≤ 2·N^(log₄3)` for every `N`. -/
theorem newman_residue_one_upper_bound (N : ℕ) :
    -(thueMorseResidueSum 3 1 N : ℝ) ≤ 2 * (N : ℝ) ^ (Real.logb 4 3) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h0 : (thueMorseResidueSum 3 1 0 : ℝ) = 0 := by
      simp [thueMorseResidueSum]
    have hnn : (0 : ℝ) ≤ ((0 : ℕ) : ℝ) ^ (Real.logb 4 3) :=
      Real.rpow_nonneg (by simp) _
    rw [h0]
    linarith
  · have h := le_two_mul_rpow_of_add_one_le
      (U := fun N => -thueMorseResidueSum 3 1 N)
      (fun k N hk => neg_thueMorseResidueSum_three_one_add_one_le k N hk) N hN
    simpa using h

/-- **The quantitative law in the class two, one side**:
`-T₂(N) ≤ 2·N^(log₄3)` for every `N`. -/
theorem neg_thueMorseResidueSum_three_two_le (N : ℕ) :
    -(thueMorseResidueSum 3 2 N : ℝ) ≤ 2 * (N : ℝ) ^ (Real.logb 4 3) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h0 : (thueMorseResidueSum 3 2 0 : ℝ) = 0 := by
      simp [thueMorseResidueSum]
    have hnn : (0 : ℝ) ≤ ((0 : ℕ) : ℝ) ^ (Real.logb 4 3) :=
      Real.rpow_nonneg (by simp) _
    rw [h0]
    linarith
  · have h := le_two_mul_rpow_of_add_one_le
      (U := fun N => -thueMorseResidueSum 3 2 N)
      (fun k N hk => neg_thueMorseResidueSum_three_two_add_one_le k N hk) N hN
    simpa using h

/-- **All three residue sums are `O(N^(log₄3))`** with the same
constant: `|T_r(N)| ≤ 2·N^(log₄3)` for every `r < 3` and `N ≥ 1`.
The class `0` is bounded above by Newman's theorem and below by `1`,
the class `1` above by `-1` and below by the amplification, and the
class `2` by `T₀ + T₁ + T₂ = E` with `|E| ≤ 1`. -/
theorem abs_thueMorseResidueSum_three_le (r : ℕ) (hr : r < 3) (N : ℕ)
    (hN : 1 ≤ N) :
    |(thueMorseResidueSum 3 r N : ℝ)| ≤ 2 * (N : ℝ) ^ (Real.logb 4 3) := by
  have hα : 0 ≤ Real.logb 4 3 := Real.logb_nonneg (by norm_num) (by norm_num)
  have hone : (1 : ℝ) ≤ (N : ℝ) ^ (Real.logb 4 3) := by
    have h := Real.one_rpow (Real.logb 4 3)
    rw [← h]
    exact Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hN) hα
  have h0 : (1 : ℝ) ≤ (thueMorseResidueSum 3 0 N : ℝ) := by
    exact_mod_cast newman_positivity N hN
  have h0u := newman_upper_bound N
  have h1u := newman_residue_one_upper_bound N
  have h1 : (thueMorseResidueSum 3 1 N : ℝ) ≤ 0 := by
    rcases (by omega : N = 1 ∨ 2 ≤ N) with rfl | h2
    · simp [thueMorseResidueSum]
    · have := thueMorseResidueSum_three_one_le_neg_one N h2
      exact_mod_cast this.trans (by norm_num)
  have h2u := neg_thueMorseResidueSum_three_two_le N
  have hsum : (thueMorseResidueSum 3 0 N : ℝ) + thueMorseResidueSum 3 1 N +
      thueMorseResidueSum 3 2 N = ((∑ n ∈ range N, thueMorseSign n : ℤ) : ℝ) := by
    exact_mod_cast thueMorseResidueSum_three_add N
  have hE := abs_le.mp (abs_sum_thueMorseSign_le_one N)
  have hE1 : (-1 : ℝ) ≤ ((∑ n ∈ range N, thueMorseSign n : ℤ) : ℝ) := by
    exact_mod_cast hE.1
  have hE2 : ((∑ n ∈ range N, thueMorseSign n : ℤ) : ℝ) ≤ 1 := by
    exact_mod_cast hE.2
  rw [abs_le]
  interval_cases r
  · constructor <;> linarith
  · constructor <;> linarith
  · constructor <;> linarith

/-- The class two vanishes at the odd powers of two: `T₂(2^(2j+1)) = 0`.
Indeed `T₂(2) = 0`, and `T₂(4M) = 3·T₂(M) - E(M)` with `E(2^k) = 0`
for `k ≥ 1`.  So, unlike the classes `0` and `1`, the class `2` obeys
no one-sided power law. -/
theorem thueMorseResidueSum_three_two_two_pow_odd (j : ℕ) :
    thueMorseResidueSum 3 2 (2 ^ (2 * j + 1)) = 0 := by
  induction j with
  | zero => decide
  | succ j ih =>
      have h := thueMorseResidueSum_three_four_mul 2 (by norm_num)
        (2 ^ (2 * j + 1))
      rw [show 4 * 2 ^ (2 * j + 1) = 2 ^ (2 * (j + 1) + 1) by ring] at h
      rw [h, ih, show (2 : ℕ) ^ (2 * j + 1) = 2 * 2 ^ (2 * j) by ring,
        sum_thueMorseSign_two_mul]
      ring

end Fabius
