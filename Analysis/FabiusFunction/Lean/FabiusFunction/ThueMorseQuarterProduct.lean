import FabiusFunction.ThueMorseMasterProduct
import FabiusFunction.ThueMorseBlockProducts

/-!
# The quarter product `G(1/4, 3/4) = 1/2`

The Allouche–Riasat–Shallit evaluation

`∏ ((4n+1)/(4n+3))^(ε(n)) = 1/2`,

proved here *from* the Woods–Robbins product by a two-line parity
split — no new analytic input.  Splitting the Woods–Robbins partial
sum of even length `2N` by the parity of the index and using
`ε(2j) = ε(j)`, `ε(2j+1) = -ε(j)` regroups the four linear factors
`(4j+1), (4j+2), (4j+3), (4j+4)` into the quarter ratio
`(4j+1)/(4j+3)` times the *inverse* Woods–Robbins ratio:

`wrA (2N) = mpLog (1/4) (3/4) N - wrA N`.

Letting `N → ∞` gives `L(1/4, 3/4) = 2·L_A = -log 2`, i.e. the
quarter product is the *square* of the Woods–Robbins product.  This
also pins down the numerical value of the half-shifted dyadic block
product of `ThueMorseBlockProducts`.

* `wrA_two_mul` — the parity-split partial-sum identity.
* `mpLimit_quarter` — `L(1/4, 3/4) = -log 2`.
* `quarter_product` / `quarter_product'` — **the ARS evaluation**
  (`eq:quarter-product`).
* `tendsto_block_product_half` — the half-shifted block product
  converges to `1/2`.
* `tendsto_block_product_half_even` — the same, along *every* even block
  length, not only the dyadic ones.
-/

set_option autoImplicit false

open Finset Filter Topology

namespace Fabius

/-- **Parity split of the Woods–Robbins partials**: an even-length
Woods–Robbins partial sum is the quarter-ratio partial sum minus the
Woods–Robbins partial sum, by `ε(2j) = ε(j)`, `ε(2j+1) = -ε(j)` and
a regrouping of the four linear factors. -/
theorem wrA_two_mul (N : ℕ) :
    wrA (2 * N) = mpLog (1 / 4 : ℝ) (3 / 4) N - wrA N := by
  rw [wrA, sum_range_two_mul, mpLog, wrA, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hs1 : (thueMorseSign (2 * j) : ℝ) = (thueMorseSign j : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ))
      (thueMorseSign_two_mul j)
  have hs2 : (thueMorseSign (2 * j + 1) : ℝ) =
      -(thueMorseSign j : ℝ) := by
    have h := thueMorseSign_two_mul_add_one j
    push_cast [h]
    ring
  have hr1 : (2 * ((2 * j : ℕ) : ℝ) + 1) / (2 * ((2 * j : ℕ) : ℝ) + 2) =
      (4 * (j : ℝ) + 1) / (4 * (j : ℝ) + 2) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    push_cast
    ring
  have hr2 : (2 * ((2 * j + 1 : ℕ) : ℝ) + 1) /
      (2 * ((2 * j + 1 : ℕ) : ℝ) + 2) =
      (4 * (j : ℝ) + 3) / (4 * (j : ℝ) + 4) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    push_cast
    ring
  -- the regrouping identity for the four linear factors
  have l1 : Real.log (4 * (j : ℝ) + 1) =
      Real.log 4 + Real.log ((j : ℝ) + 1 / 4) := by
    rw [show 4 * (j : ℝ) + 1 = 4 * ((j : ℝ) + 1 / 4) by ring,
      Real.log_mul (by norm_num) (by positivity)]
  have l2 : Real.log (4 * (j : ℝ) + 2) =
      Real.log 2 + Real.log (2 * (j : ℝ) + 1) := by
    rw [show 4 * (j : ℝ) + 2 = 2 * (2 * (j : ℝ) + 1) by ring,
      Real.log_mul (by norm_num) (by positivity)]
  have l3 : Real.log (4 * (j : ℝ) + 3) =
      Real.log 4 + Real.log ((j : ℝ) + 3 / 4) := by
    rw [show 4 * (j : ℝ) + 3 = 4 * ((j : ℝ) + 3 / 4) by ring,
      Real.log_mul (by norm_num) (by positivity)]
  have l4 : Real.log (4 * (j : ℝ) + 4) =
      Real.log 2 + Real.log (2 * (j : ℝ) + 2) := by
    rw [show 4 * (j : ℝ) + 4 = 2 * (2 * (j : ℝ) + 2) by ring,
      Real.log_mul (by norm_num) (by positivity)]
  have key : Real.log ((4 * (j : ℝ) + 1) / (4 * (j : ℝ) + 2)) -
      Real.log ((4 * (j : ℝ) + 3) / (4 * (j : ℝ) + 4)) =
      Real.log (((j : ℝ) + 1 / 4) / ((j : ℝ) + 3 / 4)) -
        Real.log ((2 * (j : ℝ) + 1) / (2 * (j : ℝ) + 2)) := by
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_div (by positivity) (by positivity),
      Real.log_div (by positivity) (by positivity),
      Real.log_div (by positivity) (by positivity),
      l1, l2, l3, l4]
    ring
  rw [hs1, hs2, hr1, hr2]
  linear_combination (thueMorseSign j : ℝ) * key

/-- The quarter-ratio log-series converges to `-log 2`: two copies of
the Woods–Robbins limit. -/
theorem tendsto_mpLog_quarter :
    Tendsto (mpLog (1 / 4 : ℝ) (3 / 4)) atTop (𝓝 (-Real.log 2)) := by
  have hdouble : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_mono (fun n => (by omega : n ≤ 2 * n)) tendsto_id
  have h1 : Tendsto (fun N => wrA (2 * N) + wrA N) atTop
      (𝓝 (-Real.log 2 / 2 + -Real.log 2 / 2)) :=
    (tendsto_wrA.comp hdouble).add tendsto_wrA
  have heq : ∀ N, wrA (2 * N) + wrA N = mpLog (1 / 4 : ℝ) (3 / 4) N :=
    fun N => by have := wrA_two_mul N; linarith
  rw [show -Real.log 2 = -Real.log 2 / 2 + -Real.log 2 / 2 by ring]
  exact Tendsto.congr heq h1

/-- **The quarter-ratio master limit**: `L(1/4, 3/4) = -log 2`. -/
theorem mpLimit_quarter : mpLimit (1 / 4 : ℝ) (3 / 4) = -Real.log 2 :=
  tendsto_nhds_unique
    (tendsto_mpLimit _ _ (by norm_num) (by norm_num))
    tendsto_mpLog_quarter

/-- **The quarter product** (`eq:quarter-product`, Allouche–Riasat–
Shallit): `∏ ((n+1/4)/(n+3/4))^(ε(n)) = 1/2`. -/
theorem quarter_product :
    Tendsto (fun N => ∏ n ∈ range N,
      (((n : ℝ) + 1 / 4) / ((n : ℝ) + 3 / 4)) ^ (thueMorseSign n))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have h := tendsto_masterProduct (1 / 4 : ℝ) (3 / 4)
    (by norm_num) (by norm_num)
  rw [mpLimit_quarter,
    exp_neg_log (by norm_num : (0 : ℝ) < 2)] at h
  exact h

/-- The quarter product in the linear-factor form
`∏ ((4n+1)/(4n+3))^(ε(n)) = 1/2`. -/
theorem quarter_product' :
    Tendsto (fun N => ∏ n ∈ range N,
      ((4 * (n : ℝ) + 1) / (4 * (n : ℝ) + 3)) ^ (thueMorseSign n))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have h := tendsto_masterProduct_affine (4 : ℝ) (1 / 4) (3 / 4)
    (by norm_num) (by norm_num) (by norm_num)
  rw [mpLimit_quarter,
    exp_neg_log (by norm_num : (0 : ℝ) < 2)] at h
  simpa only [
    show (4 : ℝ) * (1 / 4) = 1 by norm_num,
    show (4 : ℝ) * (3 / 4) = 3 by norm_num] using h

/-- **The half-shifted dyadic block product has value `1/2`**: the
numerical evaluation of `tendsto_block_product_half'`. -/
theorem tendsto_block_product_half :
    Tendsto (fun m : ℕ => ∏ k ∈ range (2 ^ m),
      ((k : ℝ) + 1 / 2) ^ (thueMorseSign k)) atTop (𝓝 (1 / 2 : ℝ)) := by
  have h := tendsto_block_product_half'
  rw [mpLimit_quarter,
    exp_neg_log (by norm_num : (0 : ℝ) < 2)] at h
  exact h

/-- **The half-shifted block product has value `1/2` along every even
block length**: the numerical evaluation of
`tendsto_block_product_half_even'`, strictly stronger than
`tendsto_block_product_half`, which is its dyadic subsequence
`M = 2^(m-1)`. -/
theorem tendsto_block_product_half_even :
    Tendsto (fun M : ℕ => ∏ k ∈ range (2 * M),
      ((k : ℝ) + 1 / 2) ^ (thueMorseSign k)) atTop (𝓝 (1 / 2 : ℝ)) := by
  have h := tendsto_block_product_half_even'
  rw [mpLimit_quarter,
    exp_neg_log (by norm_num : (0 : ℝ) < 2)] at h
  exact h

end Fabius
