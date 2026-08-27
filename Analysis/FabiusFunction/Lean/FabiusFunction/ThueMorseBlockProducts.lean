import FabiusFunction.ThueMorseMasterProduct
import FabiusFunction.ThueMorseEulerTransform
import FabiusFunction.RealZPowProduct

/-!
# Block-product limits along every even block length

The atlas's three "fingerprint" limits of dyadic block products, with the
`2^m` scaffolding removed: each of them is a *subsequence* of a limit taken
along every even block length, and the log-collapse behind them holds for an
arbitrary positive shift.

*The dyadic sign split* (`sum_thueMorseSign_mul_two_mul` and its alternating
companion, in `ThueMorseEulerTransform`) collapses a sign-weighted sum over a
block of even length into a sign-weighted sum of consecutive differences —
respectively sums, for the alternating sign.  For a shift `c > 0` the
unbounded logarithms cancel in pairs, because `2j + c = 2·(j + c/2)` and
`2j + 1 + c = 2·(j + (c+1)/2)`: the two `log 2`s cancel and what survives is
the convergent master log-series at `(c/2, (c+1)/2)`,

`∑_{k<2M} ε(k)·log(k+c) = mpLog (c/2) ((c+1)/2) M`.

At `c = 1` the master series at `(1/2, 1)` is termwise the Woods–Robbins
series, so this recovers `∑_{k<2M} ε(k)·log(k+1) = wrA M`; at `c = 1/2` it is
the master series at `(1/4, 3/4)`.

*The exponential transfer* (`tendsto_prod_zpow_of_tendsto_sum`, in
`RealZPowProduct`) then turns each log-limit into a product limit along all
of `atTop`.  The three dyadic statements are the subsequences `M = 2^(m-1)`,
`M = 2^(m-2)`, `M = 2^(m-1)` of these.

* `block_log_shift` — **the shift-general block collapse**.
* `mpLog_one_half_eq_wrA`, `mpLimit_one_half_one` — the master series at
  `(1/2, 1)` *is* the Woods–Robbins series, termwise.
* `block_log_one`, `block_log_half` — its `c = 1` and `c = 1/2` instances.
* `tendsto_block_product_even` — **the even-block product limit**, for every
  shift `c > 0`.
* `tendsto_block_product_one_even`, `tendsto_block_product_half_even'`,
  `tendsto_block_product_mixed_four` — the three evaluated even-block limits.
* `block_log_one` / `tendsto_block_product_one` — `eq:block-product-one`.
* `block_log_mixed` / `tendsto_block_product_mixed` —
  `eq:block-product-mixed`.
* `block_log_half` / `tendsto_block_product_half'` — `eq:block-product-half`.
-/

set_option autoImplicit false

open Finset Filter Topology

namespace Fabius

/-- Every dyadic ladder `m ↦ 2^(m-c)` exhausts `ℕ`. -/
private theorem tendsto_two_pow_sub (c : ℕ) :
    Tendsto (fun m : ℕ => 2 ^ (m - c)) atTop atTop := by
  have h2 : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
    tendsto_atTop_mono (fun k => (Nat.lt_two_pow_self (n := k)).le) tendsto_id
  exact h2.comp (tendsto_sub_atTop_nat c)

/-! ### The shift-general block collapse -/

/-- **The shift-general block collapse.**  Over a block of *any* even
length, and for *any* positive shift `c`, the signed logarithm sum is the
master log-partial at `(c/2, (c+1)/2)`: the pairing `2j ↦ 2j+1` turns
`log(2j+c) - log(2j+1+c)` into `log((j+c/2)/(j+(c+1)/2))`, since
`2j + c = 2·(j + c/2)` and `2j + 1 + c = 2·(j + (c+1)/2)` and the two
`log 2`s cancel. -/
theorem block_log_shift (c : ℝ) (hc : 0 < c) (M : ℕ) :
    ∑ k ∈ range (2 * M), (thueMorseSign k : ℝ) *
        Real.log ((k : ℝ) + c) =
      mpLog (c / 2) ((c + 1) / 2) M := by
  rw [sum_thueMorseSign_mul_two_mul M fun k : ℕ => Real.log ((k : ℝ) + c),
    mpLog]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : (0 : ℝ) ≤ (j : ℝ) := by exact_mod_cast Nat.zero_le j
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hlo : (0 : ℝ) < (j : ℝ) + c / 2 := by linarith
  have hhi : (0 : ℝ) < (j : ℝ) + (c + 1) / 2 := by linarith
  rw [show ((2 * j : ℕ) : ℝ) + c = 2 * ((j : ℝ) + c / 2) by push_cast; ring,
    show ((2 * j + 1 : ℕ) : ℝ) + c = 2 * ((j : ℝ) + (c + 1) / 2) by
      push_cast; ring,
    Real.log_mul h2 hlo.ne', Real.log_mul h2 hhi.ne',
    Real.log_div hlo.ne' hhi.ne']
  ring

/-! ### The master series at `(1/2, 1)` is the Woods–Robbins series -/

/-- The master log-partials at `(1/2, 1)` are the Woods–Robbins partials:
termwise `log((n+1/2)/(n+1)) = log((2n+1)/(2n+2))`. -/
theorem mpLog_one_half_eq_wrA (N : ℕ) :
    mpLog (1 / 2 : ℝ) 1 N = wrA N := by
  rw [mpLog, wrA]
  refine Finset.sum_congr rfl fun n _ => ?_
  have harg : ((n : ℝ) + 1 / 2) / ((n : ℝ) + 1) =
      (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [harg]

/-- Consequently `L(1/2, 1) = -(log 2)/2`, the Woods–Robbins limit. -/
theorem mpLimit_one_half_one :
    mpLimit (1 / 2 : ℝ) 1 = -Real.log 2 / 2 :=
  tendsto_nhds_unique
    (tendsto_mpLimit (1 / 2 : ℝ) 1 (by norm_num) (by norm_num))
    (tendsto_wrA.congr fun N => (mpLog_one_half_eq_wrA N).symm)

/-! ### The two shifts used by the atlas -/

/-- Over a dyadic block, the signed logarithm sum collapses to the
Woods–Robbins partial sum.  The `c = 1` instance of `block_log_shift`. -/
theorem block_log_one (M : ℕ) :
    ∑ k ∈ range (2 * M), (thueMorseSign k : ℝ) *
        Real.log ((k : ℝ) + 1) =
      wrA M := by
  rw [block_log_shift 1 (by norm_num) M,
    show ((1 : ℝ) + 1) / 2 = 1 by norm_num]
  exact mpLog_one_half_eq_wrA M

/-- Over a dyadic block, the half-shifted signed logarithm sum is
exactly the master log-series at `(1/4, 3/4)`.  The `c = 1/2` instance of
`block_log_shift`. -/
theorem block_log_half (M : ℕ) :
    ∑ k ∈ range (2 * M), (thueMorseSign k : ℝ) *
        Real.log ((k : ℝ) + 1 / 2) =
      mpLog (1 / 4) (3 / 4) M := by
  rw [block_log_shift (1 / 2) (by norm_num) M,
    show (1 : ℝ) / 2 / 2 = 1 / 4 by norm_num,
    show ((1 : ℝ) / 2 + 1) / 2 = 3 / 4 by norm_num]

/-! ### The even-block product limits -/

/-- **The even-block product limit.**  For every shift `c > 0`,
`∏_{k<2M}(k+c)^(ε(k)) → exp L(c/2,(c+1)/2)` along all of `atTop` — no
dyadic subsequence is needed.  This is strictly stronger than each of
`tendsto_block_product_one`, `tendsto_block_product_half'` and (through
`tendsto_block_product_one_even`) their dyadic companions. -/
theorem tendsto_block_product_even (c : ℝ) (hc : 0 < c) :
    Tendsto (fun M : ℕ => ∏ k ∈ range (2 * M),
      ((k : ℝ) + c) ^ (thueMorseSign k)) atTop
      (𝓝 (Real.exp (mpLimit (c / 2) ((c + 1) / 2)))) := by
  refine tendsto_prod_zpow_of_tendsto_sum (fun M : ℕ => range (2 * M))
    (fun k : ℕ => (k : ℝ) + c) thueMorseSign
    (fun k => by
      show (0 : ℝ) < (k : ℝ) + c
      have hk : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
      linarith) ?_
  exact (tendsto_mpLimit (c / 2) ((c + 1) / 2) (by linarith)
    (by linarith)).congr fun M => (block_log_shift c hc M).symm

/-- `∏_{k<2M} (k+1)^(ε(k)) → 1/√2` along every even block length: the
evaluated `c = 1` case of `tendsto_block_product_even`, using
`L(1/2,1) = -(log 2)/2`. -/
theorem tendsto_block_product_one_even :
    Tendsto (fun M : ℕ => ∏ k ∈ range (2 * M),
      ((k : ℝ) + 1) ^ (thueMorseSign k)) atTop
      (𝓝 (1 / Real.sqrt 2)) := by
  rw [← exp_neg_log_div_two (by norm_num : (0 : ℝ) < 2)]
  refine tendsto_prod_zpow_of_tendsto_sum (fun M : ℕ => range (2 * M))
    (fun k : ℕ => (k : ℝ) + 1) thueMorseSign (fun k => by positivity) ?_
  exact tendsto_wrA.congr fun M => (block_log_one M).symm

/-- `∏_{k<2^m} (k+1)^(ε(k)) → 1/√2` (`eq:block-product-one`): the dyadic
subsequence `M = 2^(m-1)` of `tendsto_block_product_one_even`. -/
theorem tendsto_block_product_one :
    Tendsto (fun m : ℕ => ∏ k ∈ range (2 ^ m),
      ((k : ℝ) + 1) ^ (thueMorseSign k)) atTop (𝓝 (1 / Real.sqrt 2)) := by
  refine (tendsto_block_product_one_even.comp
    (tendsto_two_pow_sub 1)).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hsplit : (2 : ℕ) ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  show ∏ k ∈ range (2 * 2 ^ (m - 1)), ((k : ℝ) + 1) ^ (thueMorseSign k) =
    ∏ k ∈ range (2 ^ m), ((k : ℝ) + 1) ^ (thueMorseSign k)
  rw [hsplit]

/-! ### The alternating (mixed) block -/

/-- Over a doubly dyadic block, the alternating signed logarithm sum
telescopes into two Woods–Robbins partial sums. -/
theorem block_log_mixed (M : ℕ) :
    ∑ k ∈ range (2 * (2 * M)),
        (((-1 : ℤ) ^ k * thueMorseSign k : ℤ) : ℝ) *
          Real.log ((k : ℝ) + 1) =
      wrA (2 * M) + 2 * wrA M := by
  rw [sum_alternating_thueMorseSign_mul_two_mul (2 * M)
    fun k : ℕ => Real.log ((k : ℝ) + 1)]
  have hterm : ∀ j ∈ range (2 * M),
      (thueMorseSign j : ℝ) *
          (Real.log (((2 * j : ℕ) : ℝ) + 1) +
            Real.log (((2 * j + 1 : ℕ) : ℝ) + 1)) =
      (thueMorseSign j : ℝ) *
          Real.log ((2 * (j : ℝ) + 1) / (2 * (j : ℝ) + 2)) +
        ((thueMorseSign j : ℝ) * (2 * Real.log 2) +
          2 * ((thueMorseSign j : ℝ) * Real.log ((j : ℝ) + 1))) := by
    intro j _
    rw [show ((2 * j : ℕ) : ℝ) + 1 = 2 * (j : ℝ) + 1 by push_cast; ring,
      show ((2 * j + 1 : ℕ) : ℝ) + 1 = 2 * ((j : ℝ) + 1) by push_cast; ring,
      Real.log_div (by positivity) (by positivity),
      show (2 * (j : ℝ) + 2) = 2 * ((j : ℝ) + 1) from by ring,
      Real.log_mul (by norm_num) (by positivity)]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  have hzero : ∑ j ∈ range (2 * M),
      (thueMorseSign j : ℝ) * (2 * Real.log 2) = 0 := by
    rw [← Finset.sum_mul]
    have hcast : ∑ j ∈ range (2 * M), (thueMorseSign j : ℝ) =
        ((∑ j ∈ range (2 * M), thueMorseSign j : ℤ) : ℝ) := by
      push_cast
      rfl
    rw [hcast, sum_thueMorseSign_range_two_mul]
    norm_num
  have htwo : ∑ j ∈ range (2 * M),
      2 * ((thueMorseSign j : ℝ) * Real.log ((j : ℝ) + 1)) =
      2 * wrA M := by
    rw [← Finset.mul_sum, block_log_one M]
  rw [hzero, htwo, zero_add]
  rfl

/-- `block_log_mixed` with the block length written as a multiple of four:
`∑_{k<4M} (-1)^k·ε(k)·log(k+1) = wrA(2M) + 2·wrA(M)`. -/
theorem block_log_mixed_four (M : ℕ) :
    ∑ k ∈ range (4 * M),
        (((-1 : ℤ) ^ k * thueMorseSign k : ℤ) : ℝ) *
          Real.log ((k : ℝ) + 1) =
      wrA (2 * M) + 2 * wrA M := by
  rw [show 4 * M = 2 * (2 * M) by ring]
  exact block_log_mixed M

/-- **The mixed block product along every multiple of four**:
`∏_{k<4M} (k+1)^((-1)^k·ε(k)) → 1/(2√2)` along all of `atTop`.  Strictly
stronger than `tendsto_block_product_mixed`, which is its subsequence
`M = 2^(m-2)`. -/
theorem tendsto_block_product_mixed_four :
    Tendsto (fun M : ℕ => ∏ k ∈ range (4 * M),
      ((k : ℝ) + 1) ^ ((-1 : ℤ) ^ k * thueMorseSign k)) atTop
      (𝓝 (1 / (2 * Real.sqrt 2))) := by
  rw [← exp_neg_three_halves_log (by norm_num : (0 : ℝ) < 2)]
  refine tendsto_prod_zpow_of_tendsto_sum (fun M : ℕ => range (4 * M))
    (fun k : ℕ => (k : ℝ) + 1) (fun k => (-1 : ℤ) ^ k * thueMorseSign k)
    (fun k => by positivity) ?_
  rw [show -(3 / 2 * Real.log 2) =
    -Real.log 2 / 2 + 2 * (-Real.log 2 / 2) from by ring]
  have hdouble : Tendsto (fun M : ℕ => 2 * M) atTop atTop :=
    tendsto_atTop_mono (fun n => (by omega : n ≤ 2 * n)) tendsto_id
  refine ((tendsto_wrA.comp hdouble).add
    (tendsto_wrA.const_mul (2 : ℝ))).congr fun M => ?_
  exact (block_log_mixed_four M).symm

/-- `∏_{k<2^m} (k+1)^((-1)^k·ε(k)) → 1/(2√2)`
(`eq:block-product-mixed`): the subsequence `M = 2^(m-2)` of
`tendsto_block_product_mixed_four`. -/
theorem tendsto_block_product_mixed :
    Tendsto (fun m : ℕ => ∏ k ∈ range (2 ^ m),
      ((k : ℝ) + 1) ^ ((-1 : ℤ) ^ k * thueMorseSign k)) atTop
      (𝓝 (1 / (2 * Real.sqrt 2))) := by
  refine (tendsto_block_product_mixed_four.comp
    (tendsto_two_pow_sub 2)).congr' ?_
  filter_upwards [eventually_ge_atTop 2] with m hm
  have hsplit : (2 : ℕ) ^ m = 4 * 2 ^ (m - 2) := by
    rw [show 4 * 2 ^ (m - 2) = 2 ^ (m - 2 + 1 + 1) by
      rw [pow_succ, pow_succ]
      ring]
    congr 1
    omega
  show ∏ k ∈ range (4 * 2 ^ (m - 2)),
      ((k : ℝ) + 1) ^ ((-1 : ℤ) ^ k * thueMorseSign k) =
    ∏ k ∈ range (2 ^ m),
      ((k : ℝ) + 1) ^ ((-1 : ℤ) ^ k * thueMorseSign k)
  rw [hsplit]

/-! ### The half-shifted block -/

/-- `∏_{k<2M} (k+1/2)^(ε(k)) → exp L(1/4,3/4)` along every even block
length: the `c = 1/2` case of `tendsto_block_product_even`, with the
parameters normalised.  (The value `exp L(1/4,3/4) = 1/2` is the
Allouche–Riasat–Shallit quarter product, proved in
`ThueMorseQuarterProduct`.) -/
theorem tendsto_block_product_half_even' :
    Tendsto (fun M : ℕ => ∏ k ∈ range (2 * M),
      ((k : ℝ) + 1 / 2) ^ (thueMorseSign k)) atTop
      (𝓝 (Real.exp (mpLimit (1 / 4) (3 / 4)))) := by
  refine tendsto_prod_zpow_of_tendsto_sum (fun M : ℕ => range (2 * M))
    (fun k : ℕ => (k : ℝ) + 1 / 2) thueMorseSign (fun k => by positivity) ?_
  exact (tendsto_mpLimit (1 / 4 : ℝ) (3 / 4) (by norm_num)
    (by norm_num)).congr fun M => (block_log_half M).symm

/-- `∏_{k<2^m} (k+1/2)^(ε(k)) → exp L(1/4,3/4)`
(`eq:block-product-half`): the subsequence `M = 2^(m-1)` of
`tendsto_block_product_half_even'`.  The value `exp L(1/4,3/4) = 1/2` is
the Allouche–Riasat–Shallit quarter product, proved in
`ThueMorseQuarterProduct`. -/
theorem tendsto_block_product_half' :
    Tendsto (fun m : ℕ => ∏ k ∈ range (2 ^ m),
      ((k : ℝ) + 1 / 2) ^ (thueMorseSign k)) atTop
      (𝓝 (Real.exp (mpLimit (1 / 4) (3 / 4)))) := by
  refine (tendsto_block_product_half_even'.comp
    (tendsto_two_pow_sub 1)).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hsplit : (2 : ℕ) ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  show ∏ k ∈ range (2 * 2 ^ (m - 1)),
      ((k : ℝ) + 1 / 2) ^ (thueMorseSign k) =
    ∏ k ∈ range (2 ^ m), ((k : ℝ) + 1 / 2) ^ (thueMorseSign k)
  rw [hsplit]

end Fabius
