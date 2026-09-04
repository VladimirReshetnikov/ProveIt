import FabiusFunction.ThueMorseNewmanQuantitative

/-!
# Exact self-similarity of the Newman sums, and non-convergence

The base-four collapse `T_r(4M) = 3·T_r(M) - E(M)` of `ThueMorseNewman`
carries an error term only through the plain prefix sum `E(M)`, and `E`
**vanishes at every even endpoint**.  So along even mantissas the
amplification is *exact*:

`T_r(4·2M) = 3·T_r(2M)`   (every residue class `r < 3`),

whence `T_r(4^k·2M) = 3^k·T_r(2M)`.  Since `4^(log₄3) = 3`, the
normalized quantity `T_r(N)/N^(log₄3)` is therefore **exactly constant**
along each geometric ray `N = 4^k·2M`: the Newman ratio depends only on
the base-four mantissa.  This is the elementary core of Coquet's
theorem, and it settles what the quantitative bounds leave open:

`N₃(N)/N^(log₄3)` **does not converge** — it is `2/3` at every `4^(k+1)`
and `1/√3` at every `4^k·8`.

* `thueMorseResidueSum_three_four_mul_two_mul` — the exact recursion
  `T_r(4·2M) = 3·T_r(2M)`.
* `thueMorseResidueSum_three_four_pow_mul_two_mul` — its iterate
  `T_r(4^k·2M) = 3^k·T_r(2M)`.
* `thueMorseResidueSum_three_zero_four_pow` — the exact value
  `T₀(4^(k+1)) = 2·3^k`; `thueMorseResidueSum_three_zero_eight_mul_four_pow`
  gives `T₀(4^k·8) = 3^(k+1)`.
* `newmanRatio`, `newman_ratio_four_pow_mul` — the ratio and its exact
  constancy along a geometric ray with even mantissa.
* `newman_ratio_four_pow` (`= 2/3`), `newman_ratio_eight_mul_four_pow`
  (`= ratio at 8`), and `sq_eight_rpow_logb` (`(8^(log₄3))² = 27`, so
  the second value is `1/√3`).
* `not_tendsto_newmanRatio` — **non-convergence**.
-/

set_option autoImplicit false

open Filter Topology Finset

namespace Fabius

/-- **Exact base-four amplification at an even endpoint**: the error
term of the collapse is the prefix sum `E(M)`, which vanishes when the
endpoint is even, so `T_r(4·2M) = 3·T_r(2M)` with no correction. -/
theorem thueMorseResidueSum_three_four_mul_two_mul (r : ℕ) (hr : r < 3)
    (M : ℕ) :
    thueMorseResidueSum 3 r (4 * (2 * M)) =
      3 * thueMorseResidueSum 3 r (2 * M) := by
  rw [thueMorseResidueSum_three_four_mul r hr (2 * M),
    sum_thueMorseSign_two_mul M, sub_zero]

/-- The iterated form `T_r(4^k·2M) = 3^k·T_r(2M)`: each base-four digit
appended to an even mantissa multiplies the residue sum by exactly
three. -/
theorem thueMorseResidueSum_three_four_pow_mul_two_mul (r : ℕ) (hr : r < 3)
    (k M : ℕ) :
    thueMorseResidueSum 3 r (4 ^ k * (2 * M)) =
      3 ^ k * thueMorseResidueSum 3 r (2 * M) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hrw : 4 ^ (k + 1) * (2 * M) = 4 * (2 * (4 ^ k * M)) := by ring
      have heven : 2 * (4 ^ k * M) = 4 ^ k * (2 * M) := by ring
      rw [hrw, thueMorseResidueSum_three_four_mul_two_mul r hr, heven, ih,
        pow_succ]
      ring

/-- `T₀(4) = 2`: below four the multiples of three are `0` and `3`,
both of even binary weight. -/
theorem thueMorseResidueSum_three_zero_four :
    thueMorseResidueSum 3 0 4 = 2 := by
  decide

/-- `T₀(8) = 3`. -/
theorem thueMorseResidueSum_three_zero_eight :
    thueMorseResidueSum 3 0 8 = 3 := by
  decide

/-- **The exact value at the powers of four**: `T₀(4^(k+1)) = 2·3^k`. -/
theorem thueMorseResidueSum_three_zero_four_pow (k : ℕ) :
    thueMorseResidueSum 3 0 (4 ^ (k + 1)) = 2 * 3 ^ k := by
  have h : (4 : ℕ) ^ (k + 1) = 4 ^ k * (2 * 2) := by ring
  rw [h, thueMorseResidueSum_three_four_pow_mul_two_mul 0 (by norm_num),
    show (2 : ℕ) * 2 = 4 from rfl, thueMorseResidueSum_three_zero_four]
  ring

/-- **The exact value at `4^k·8`**: `T₀(4^k·8) = 3^(k+1)`. -/
theorem thueMorseResidueSum_three_zero_eight_mul_four_pow (k : ℕ) :
    thueMorseResidueSum 3 0 (4 ^ k * 8) = 3 ^ k * 3 := by
  have h : (4 : ℕ) ^ k * 8 = 4 ^ k * (2 * 4) := by ring
  rw [h, thueMorseResidueSum_three_four_pow_mul_two_mul 0 (by norm_num),
    show (2 : ℕ) * 4 = 8 from rfl, thueMorseResidueSum_three_zero_eight]

/-! ## The normalized ratio -/

/-- The Newman ratio `N₃(N)/N^(log₄3)`. -/
noncomputable def newmanRatio (N : ℕ) : ℝ :=
  (thueMorseResidueSum 3 0 N : ℝ) / (N : ℝ) ^ (Real.logb 4 3)

/-- **Exact constancy along a geometric ray with even mantissa**: the
ratio at `4^k·2M` equals the ratio at `2M` for every `k` and every
`M ≥ 1`.  Numerator and denominator are both multiplied by exactly
`3^k` — the numerator by
`thueMorseResidueSum_three_four_pow_mul_two_mul`, the denominator
because `4^(log₄3) = 3`. -/
theorem newman_ratio_four_pow_mul (k M : ℕ) (hM : 1 ≤ M) :
    newmanRatio (4 ^ k * (2 * M)) = newmanRatio (2 * M) := by
  have hMpos : (0 : ℝ) < ((2 * M : ℕ) : ℝ) := by
    have h : 0 < 2 * M := by omega
    exact_mod_cast h
  have hnum := thueMorseResidueSum_three_four_pow_mul_two_mul 0 (by norm_num) k M
  have hcast : ((4 ^ k * (2 * M) : ℕ) : ℝ) = (4 : ℝ) ^ k * ((2 * M : ℕ) : ℝ) := by
    push_cast
    ring
  have hden : ((4 ^ k * (2 * M) : ℕ) : ℝ) ^ (Real.logb 4 3) =
      (3 : ℝ) ^ k * ((2 * M : ℕ) : ℝ) ^ (Real.logb 4 3) := by
    rw [hcast, Real.mul_rpow (by positivity) hMpos.le,
      four_pow_rpow_logb_four_three]
  have hnumR : ((thueMorseResidueSum 3 0 (4 ^ k * (2 * M)) : ℤ) : ℝ) =
      (3 : ℝ) ^ k * ((thueMorseResidueSum 3 0 (2 * M) : ℤ) : ℝ) := by
    rw [hnum]
    push_cast
    ring
  have h3 : ((3 : ℝ) ^ k) ≠ 0 := by positivity
  have hd : ((2 * M : ℕ) : ℝ) ^ (Real.logb 4 3) ≠ 0 :=
    (Real.rpow_pos_of_pos hMpos _).ne'
  rw [newmanRatio, newmanRatio, hden, hnumR, mul_div_mul_left _ _ h3]

/-- The ratio is `2/3` at every positive power of four. -/
theorem newman_ratio_four_pow (k : ℕ) :
    newmanRatio (4 ^ (k + 1)) = 2 / 3 := by
  have hrw : (4 : ℕ) ^ (k + 1) = 4 ^ k * (2 * 2) := by ring
  rw [hrw, newman_ratio_four_pow_mul k 2 (by norm_num),
    show (2 : ℕ) * 2 = 4 from rfl, newmanRatio,
    thueMorseResidueSum_three_zero_four]
  have h4 : ((4 : ℕ) : ℝ) = (4 : ℝ) ^ (1 : ℕ) := by norm_num
  rw [h4, four_pow_rpow_logb_four_three]
  norm_num

/-- The ratio is constant along `4^k·8`, equal to its value at `8`. -/
theorem newman_ratio_eight_mul_four_pow (k : ℕ) :
    newmanRatio (4 ^ k * 8) = newmanRatio 8 := by
  have hrw : (4 : ℕ) ^ k * 8 = 4 ^ k * (2 * 4) := by ring
  rw [hrw, newman_ratio_four_pow_mul k 4 (by norm_num)]

/-- `(8^(log₄3))² = 27`, i.e. `8^(log₄3) = 3√3`: squaring turns the
exponent identity into `64^(log₄3) = (4^(log₄3))³ = 27`. -/
theorem sq_eight_rpow_logb :
    ((8 : ℝ) ^ (Real.logb 4 3)) ^ 2 = 27 := by
  have h64 := four_pow_rpow_logb_four_three 3
  norm_num at h64
  rw [← Real.rpow_natCast ((8 : ℝ) ^ (Real.logb 4 3)) 2,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8), mul_comm,
    Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8)]
  norm_num
  exact h64

/-- The value at `8` is `3/(3√3) = 1/√3`, in particular **not** `2/3`:
if it were, squaring would give `81/4 = 27`. -/
theorem newman_ratio_eight_ne_two_div_three : newmanRatio 8 ≠ 2 / 3 := by
  have hpos : (0 : ℝ) < (8 : ℝ) ^ (Real.logb 4 3) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hval : newmanRatio 8 = 3 / (8 : ℝ) ^ (Real.logb 4 3) := by
    rw [newmanRatio, thueMorseResidueSum_three_zero_eight]
    norm_num
  intro h
  rw [hval, div_eq_div_iff hpos.ne' (by norm_num : (3 : ℝ) ≠ 0)] at h
  -- `h : 3 * 3 = 2 * 8 ^ (log₄ 3)`, so `8 ^ (log₄ 3) = 9/2` and squaring fails
  have hsq := sq_eight_rpow_logb
  nlinarith [hsq, hpos]

/-- **The Newman ratio does not converge.**  It is constantly `2/3`
along `N = 4^(k+1)` and constantly `1/√3` along `N = 4^k·8`, and those
values differ.  So the quantitative bracket
`N^(log₄3)/9 ≤ N₃(N) ≤ 2·N^(log₄3)` cannot be sharpened to an
asymptotic equality: this is the qualitative content of Coquet's
theorem. -/
theorem not_tendsto_newmanRatio (L : ℝ) :
    ¬ Tendsto (fun N : ℕ => newmanRatio N) atTop (𝓝 L) := by
  intro hL
  have hpow : ∀ k : ℕ, k ≤ 4 ^ k := fun k =>
    le_trans (Nat.lt_two_pow_self (n := k)).le
      (Nat.pow_le_pow_left (by norm_num) k)
  have h4 : Tendsto (fun k : ℕ => (4 : ℕ) ^ (k + 1)) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_) tendsto_id
    exact le_trans (hpow k) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h8 : Tendsto (fun k : ℕ => (4 : ℕ) ^ k * 8) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_) tendsto_id
    exact le_trans (hpow k) (Nat.le_mul_of_pos_right _ (by norm_num))
  have hA : Tendsto (fun _ : ℕ => (2 : ℝ) / 3) atTop (𝓝 L) :=
    (hL.comp h4).congr fun k => newman_ratio_four_pow k
  have hB : Tendsto (fun _ : ℕ => newmanRatio 8) atTop (𝓝 L) :=
    (hL.comp h8).congr fun k => newman_ratio_eight_mul_four_pow k
  have hLA : L = 2 / 3 := tendsto_nhds_unique hA tendsto_const_nhds
  have hLB : L = newmanRatio 8 := tendsto_nhds_unique hB tendsto_const_nhds
  exact newman_ratio_eight_ne_two_div_three (hLB ▸ hLA)

end Fabius
