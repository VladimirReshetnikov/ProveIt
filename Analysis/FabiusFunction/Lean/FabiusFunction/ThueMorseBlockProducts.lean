import FabiusFunction.ThueMorseMasterProduct
import FabiusFunction.ThueMorseEulerTransform
import FabiusFunction.RealZPowProduct

/-!
# The dyadic block-product limits

The atlas's three "fingerprint" limits of dyadic block products.  Two reusable
facts make them corollaries of the Woods–Robbins and master-product machinery.

*The dyadic sign split* (`sum_thueMorseSign_mul_two_mul` and its alternating
companion, in `ThueMorseEulerTransform`) collapses a sign-weighted sum over a
block of even length into a sign-weighted sum of consecutive differences —
respectively sums, for the alternating sign.  The unbounded logarithms cancel
and what survives is the convergent sign-weighted ratio series

`∑_{k<2N} ε(k)·log(k+1) = wrA(N)`.

*The exponential transfer* (`tendsto_prod_zpow_of_tendsto_sum`, in
`RealZPowProduct`) then turns each log-limit into the product limit.

So `∏_{k<2^m}(k+1)^(ε(k)) → 1/√2`; the alternating version telescopes twice,
giving `1/(2√2)`; and the half-shifted version is exactly the master log-series
at `(1/4, 3/4)`, identifying its limit as `exp L(1/4,3/4)`.

* `block_log_one` / `tendsto_block_product_one` — `eq:block-product-one`.
* `block_log_mixed` / `tendsto_block_product_mixed` — `eq:block-product-mixed`.
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

/-- Over a dyadic block, the signed logarithm sum collapses to the
Woods–Robbins partial sum. -/
theorem block_log_one (M : ℕ) :
    ∑ k ∈ range (2 * M), (thueMorseSign k : ℝ) *
        Real.log ((k : ℝ) + 1) =
      wrA M := by
  rw [sum_thueMorseSign_mul_two_mul M fun k : ℕ => Real.log ((k : ℝ) + 1), wrA]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show ((2 * j : ℕ) : ℝ) + 1 = 2 * (j : ℝ) + 1 by push_cast; ring,
    show ((2 * j + 1 : ℕ) : ℝ) + 1 = 2 * (j : ℝ) + 2 by push_cast; ring,
    ← Real.log_div (by positivity) (by positivity)]

/-- `∏_{k<2^m} (k+1)^(ε(k)) → 1/√2` (`eq:block-product-one`). -/
theorem tendsto_block_product_one :
    Tendsto (fun m : ℕ => ∏ k ∈ range (2 ^ m),
      ((k : ℝ) + 1) ^ (thueMorseSign k)) atTop (𝓝 (1 / Real.sqrt 2)) := by
  rw [← exp_neg_log_div_two (by norm_num : (0 : ℝ) < 2)]
  refine tendsto_prod_zpow_of_tendsto_sum (fun m : ℕ => range (2 ^ m))
    (fun k : ℕ => (k : ℝ) + 1) thueMorseSign (fun k => by positivity) ?_
  refine (tendsto_wrA.comp (tendsto_two_pow_sub 1)).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  rw [show (2 : ℕ) ^ m = 2 * 2 ^ (m - 1) by
    rw [← pow_succ']
    congr 1
    omega]
  exact (block_log_one (2 ^ (m - 1))).symm

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

/-- `∏_{k<2^m} (k+1)^((-1)^k·ε(k)) → 1/(2√2)`
(`eq:block-product-mixed`). -/
theorem tendsto_block_product_mixed :
    Tendsto (fun m : ℕ => ∏ k ∈ range (2 ^ m),
      ((k : ℝ) + 1) ^ ((-1 : ℤ) ^ k * thueMorseSign k)) atTop
      (𝓝 (1 / (2 * Real.sqrt 2))) := by
  rw [← exp_neg_three_halves_log (by norm_num : (0 : ℝ) < 2)]
  refine tendsto_prod_zpow_of_tendsto_sum (fun m : ℕ => range (2 ^ m))
    (fun k : ℕ => (k : ℝ) + 1) (fun k => (-1 : ℤ) ^ k * thueMorseSign k)
    (fun k => by positivity) ?_
  rw [show -(3 / 2 * Real.log 2) =
    -Real.log 2 / 2 + 2 * (-Real.log 2 / 2) from by ring]
  refine (((tendsto_wrA.comp (tendsto_two_pow_sub 1)).add
    ((tendsto_wrA.comp (tendsto_two_pow_sub 2)).const_mul (2 : ℝ)))).congr' ?_
  filter_upwards [eventually_ge_atTop 2] with m hm
  have hsplit : (2 : ℕ) ^ m = 2 * (2 * 2 ^ (m - 2)) := by
    rw [show 2 * (2 * 2 ^ (m - 2)) = 2 ^ (m - 2 + 1 + 1) by
      rw [pow_succ, pow_succ]
      ring]
    congr 1
    omega
  have hstep : (2 : ℕ) * 2 ^ (m - 2) = 2 ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hsplit, block_log_mixed (2 ^ (m - 2)), hstep]
  rfl

/-- Over a dyadic block, the half-shifted signed logarithm sum is
exactly the master log-series at `(1/4, 3/4)`. -/
theorem block_log_half (M : ℕ) :
    ∑ k ∈ range (2 * M), (thueMorseSign k : ℝ) *
        Real.log ((k : ℝ) + 1 / 2) =
      mpLog (1 / 4) (3 / 4) M := by
  rw [sum_thueMorseSign_mul_two_mul M fun k : ℕ => Real.log ((k : ℝ) + 1 / 2),
    mpLog]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show ((2 * j : ℕ) : ℝ) + 1 / 2 = 2 * ((j : ℝ) + 1 / 4) by push_cast; ring,
    show ((2 * j + 1 : ℕ) : ℝ) + 1 / 2 = 2 * ((j : ℝ) + 3 / 4) by
      push_cast; ring,
    Real.log_mul (by norm_num) (by positivity),
    Real.log_mul (by norm_num) (by positivity),
    Real.log_div (by positivity) (by positivity)]
  ring

/-- `∏_{k<2^m} (k+1/2)^(ε(k)) → exp L(1/4,3/4)`
(`eq:block-product-half`; the value `exp L(1/4,3/4) = 1/2` is the
Allouche–Riasat–Shallit quarter product, proved in
`ThueMorseQuarterProduct`). -/
theorem tendsto_block_product_half' :
    Tendsto (fun m : ℕ => ∏ k ∈ range (2 ^ m),
      ((k : ℝ) + 1 / 2) ^ (thueMorseSign k)) atTop
      (𝓝 (Real.exp (mpLimit (1 / 4) (3 / 4)))) := by
  refine tendsto_prod_zpow_of_tendsto_sum (fun m : ℕ => range (2 ^ m))
    (fun k : ℕ => (k : ℝ) + 1 / 2) thueMorseSign (fun k => by positivity) ?_
  refine ((tendsto_mpLimit (1 / 4) (3 / 4) (by norm_num)
    (by norm_num)).comp (tendsto_two_pow_sub 1)).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  rw [show (2 : ℕ) ^ m = 2 * 2 ^ (m - 1) by
    rw [← pow_succ']
    congr 1
    omega]
  exact (block_log_half (2 ^ (m - 1))).symm

end Fabius
