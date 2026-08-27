import FabiusFunction.ThueMorseMasterProduct
import FabiusFunction.ThueMorseEulerTransform

/-!
# The dyadic block-product limits

The atlas's three "fingerprint" limits of dyadic block products.  The
key observation makes them corollaries of the Woods–Robbins and
master-product machinery: over a dyadic block the even/odd split
collapses the unbounded logarithms into the convergent sign-weighted
ratio series —

`∑_{k<2N} ε(k)·log(k+1) = wrA(N)`,

so `∏_{k<2^m}(k+1)^(ε(k)) → 1/√2`; the alternating version telescopes
twice, giving `1/(2√2)`; and the half-shifted version is exactly the
master log-series at `(1/4, 3/4)`, identifying its limit as
`exp L(1/4,3/4)` (whose numerical value `1/2` is the
Allouche–Riasat–Shallit quarter product, cited in the atlas).

* `block_log_one` / `tendsto_block_product_one` —
  `eq:block-product-one`.
* `block_log_mixed` / `tendsto_block_product_mixed` —
  `eq:block-product-mixed`.
* `block_log_half` / `tendsto_block_product_half'` —
  `eq:block-product-half` up to the cited quarter-product value.
-/

set_option autoImplicit false

open Finset Filter Topology

namespace Fabius

/-- Over a dyadic block, the signed logarithm sum collapses to the
Woods–Robbins partial sum. -/
theorem block_log_one (M : ℕ) :
    ∑ k ∈ range (2 * M), (thueMorseSign k : ℝ) *
        Real.log ((k : ℝ) + 1) =
      wrA M := by
  rw [sum_range_two_mul, wrA]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsign1 : (thueMorseSign (2 * j) : ℝ) = (thueMorseSign j : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (thueMorseSign_two_mul j)
  have hsign2 : (thueMorseSign (2 * j + 1) : ℝ) =
      -(thueMorseSign j : ℝ) := by
    have h := thueMorseSign_two_mul_add_one j
    push_cast [h]
    ring
  rw [hsign1, hsign2]
  have h1 : ((2 * j : ℕ) : ℝ) + 1 = 2 * (j : ℝ) + 1 := by push_cast; ring
  have h2 : ((2 * j + 1 : ℕ) : ℝ) + 1 = 2 * (j : ℝ) + 2 := by
    push_cast; ring
  rw [h1, h2, Real.log_div (by positivity) (by positivity)]
  ring

private theorem hpow_tendsto :
    Tendsto (fun m : ℕ => 2 ^ (m - 1)) atTop atTop := by
  refine tendsto_atTop_mono
    (fun m => (?_ : m ≤ 2 ^ (m - 1))) tendsto_id
  have := Nat.lt_two_pow_self (n := m - 1)
  omega

private theorem exp_neg_half_log :
    Real.exp (-Real.log 2 / 2) = 1 / Real.sqrt 2 := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos
    (by norm_num : (0 : ℝ) < 2), one_div, ← Real.exp_neg]
  congr 1
  ring

/-- `∏_{k<2^m} (k+1)^(ε(k)) → 1/√2` (`eq:block-product-one`). -/
theorem tendsto_block_product_one :
    Tendsto (fun m : ℕ => ∏ k ∈ range (2 ^ m),
      ((k : ℝ) + 1) ^ (thueMorseSign k)) atTop (𝓝 (1 / Real.sqrt 2)) := by
  have hexp : ∀ m : ℕ, ∏ k ∈ range (2 ^ m),
      ((k : ℝ) + 1) ^ (thueMorseSign k) =
      Real.exp (∑ k ∈ range (2 ^ m),
        (thueMorseSign k : ℝ) * Real.log ((k : ℝ) + 1)) := by
    intro m
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun k _ => ?_
    have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [← Real.rpow_intCast ((k : ℝ) + 1) (thueMorseSign k),
      Real.rpow_def_of_pos hpos]
    congr 1
    ring
  have hkey : ∀ m : ℕ, 1 ≤ m →
      (∑ k ∈ range (2 ^ m),
        (thueMorseSign k : ℝ) * Real.log ((k : ℝ) + 1)) =
      wrA (2 ^ (m - 1)) := by
    intro m hm
    rw [show (2 : ℕ) ^ m = 2 * 2 ^ (m - 1) by
      rw [← pow_succ']
      congr 1
      omega]
    exact block_log_one (2 ^ (m - 1))
  have hlog : Tendsto (fun m : ℕ => ∑ k ∈ range (2 ^ m),
      (thueMorseSign k : ℝ) * Real.log ((k : ℝ) + 1)) atTop
      (𝓝 (-Real.log 2 / 2)) := by
    refine (tendsto_wrA.comp hpow_tendsto).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    exact (hkey m hm).symm
  have hcomp := (Real.continuous_exp.tendsto _).comp hlog
  rw [exp_neg_half_log] at hcomp
  exact Tendsto.congr (fun m => (hexp m).symm) hcomp

/-- Over a doubly dyadic block, the alternating signed logarithm sum
telescopes into two Woods–Robbins partial sums. -/
theorem block_log_mixed (M : ℕ) :
    ∑ k ∈ range (2 * (2 * M)),
        (((-1 : ℤ) ^ k * thueMorseSign k : ℤ) : ℝ) *
          Real.log ((k : ℝ) + 1) =
      wrA (2 * M) + 2 * wrA M := by
  rw [sum_range_two_mul]
  have hterm : ∀ j ∈ range (2 * M),
      ((((-1 : ℤ) ^ (2 * j) * thueMorseSign (2 * j) : ℤ) : ℝ) *
          Real.log (((2 * j : ℕ) : ℝ) + 1) +
        (((-1 : ℤ) ^ (2 * j + 1) * thueMorseSign (2 * j + 1) : ℤ) : ℝ) *
          Real.log (((2 * j + 1 : ℕ) : ℝ) + 1)) =
      (thueMorseSign j : ℝ) *
          Real.log ((2 * (j : ℝ) + 1) / (2 * (j : ℝ) + 2)) +
        ((thueMorseSign j : ℝ) * (2 * Real.log 2) +
          2 * ((thueMorseSign j : ℝ) * Real.log ((j : ℝ) + 1))) := by
    intro j _
    have he : ((-1 : ℤ) ^ (2 * j)) = 1 := by
      rw [pow_mul]
      norm_num
    have ho : ((-1 : ℤ) ^ (2 * j + 1)) = -1 := by
      rw [pow_succ, pow_mul]
      norm_num
    have hs1 := thueMorseSign_two_mul j
    have hs2 := thueMorseSign_two_mul_add_one j
    rw [he, ho, hs1, hs2]
    have h1 : ((2 * j : ℕ) : ℝ) + 1 = 2 * (j : ℝ) + 1 := by
      push_cast; ring
    have h2 : ((2 * j + 1 : ℕ) : ℝ) + 1 = 2 * ((j : ℝ) + 1) := by
      push_cast; ring
    rw [h1, h2, Real.log_div (by positivity) (by positivity),
      show (2 * (j : ℝ) + 2) = 2 * ((j : ℝ) + 1) from by ring,
      Real.log_mul (by norm_num) (by positivity)]
    push_cast
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
    rw [hcast, sum_thueMorseSign_range, if_pos ⟨M, rfl⟩]
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
  have hexp : ∀ m : ℕ, ∏ k ∈ range (2 ^ m),
      ((k : ℝ) + 1) ^ ((-1 : ℤ) ^ k * thueMorseSign k) =
      Real.exp (∑ k ∈ range (2 ^ m),
        (((-1 : ℤ) ^ k * thueMorseSign k : ℤ) : ℝ) *
          Real.log ((k : ℝ) + 1)) := by
    intro m
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun k _ => ?_
    have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [← Real.rpow_intCast ((k : ℝ) + 1)
      ((-1 : ℤ) ^ k * thueMorseSign k), Real.rpow_def_of_pos hpos]
    congr 1
    ring
  have hkey : ∀ m : ℕ, 2 ≤ m →
      (∑ k ∈ range (2 ^ m),
        (((-1 : ℤ) ^ k * thueMorseSign k : ℤ) : ℝ) *
          Real.log ((k : ℝ) + 1)) =
      wrA (2 ^ (m - 1)) + 2 * wrA (2 ^ (m - 2)) := by
    intro m hm
    rw [show (2 : ℕ) ^ m = 2 * (2 * 2 ^ (m - 2)) by
      rw [show 2 * (2 * 2 ^ (m - 2)) = 2 ^ (m - 2 + 1 + 1) by
        rw [pow_succ, pow_succ]
        ring]
      congr 1
      omega]
    rw [block_log_mixed (2 ^ (m - 2))]
    congr 2
    rw [← pow_succ']
    congr 1
    omega
  have hpow2 : Tendsto (fun m : ℕ => 2 ^ (m - 2)) atTop atTop := by
    have h1 : Tendsto (fun m : ℕ => m - 2) atTop atTop :=
      tendsto_sub_atTop_nat 2
    have h2 : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop := by
      refine tendsto_atTop_mono (fun k => (?_ : k ≤ 2 ^ k)) tendsto_id
      exact (Nat.lt_two_pow_self).le
    exact h2.comp h1
  have hlog : Tendsto (fun m : ℕ => ∑ k ∈ range (2 ^ m),
      (((-1 : ℤ) ^ k * thueMorseSign k : ℤ) : ℝ) *
        Real.log ((k : ℝ) + 1)) atTop
      (𝓝 (-Real.log 2 / 2 + 2 * (-Real.log 2 / 2))) := by
    have h1 := (tendsto_wrA.comp hpow_tendsto).add
      (((tendsto_wrA.comp hpow2).const_mul (2 : ℝ)))
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with m hm
    exact (hkey m hm).symm
  have hval : Real.exp (-Real.log 2 / 2 + 2 * (-Real.log 2 / 2)) =
      1 / (2 * Real.sqrt 2) := by
    have hs : Real.sqrt 2 = Real.exp (Real.log 2 / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos
        (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    have h2e : (2 : ℝ) = Real.exp (Real.log 2) :=
      (Real.exp_log (by norm_num)).symm
    rw [one_div,
      show (2 : ℝ) * Real.sqrt 2 =
        Real.exp (Real.log 2) * Real.exp (Real.log 2 / 2) from by
          rw [← hs, ← h2e],
      ← Real.exp_add, ← Real.exp_neg]
    congr 1
    ring
  have hcomp := (Real.continuous_exp.tendsto _).comp hlog
  rw [hval] at hcomp
  exact Tendsto.congr (fun m => (hexp m).symm) hcomp

/-- Over a dyadic block, the half-shifted signed logarithm sum is
exactly the master log-series at `(1/4, 3/4)`. -/
theorem block_log_half (M : ℕ) :
    ∑ k ∈ range (2 * M), (thueMorseSign k : ℝ) *
        Real.log ((k : ℝ) + 1 / 2) =
      mpLog (1 / 4) (3 / 4) M := by
  rw [sum_range_two_mul, mpLog]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsign1 : (thueMorseSign (2 * j) : ℝ) = (thueMorseSign j : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (thueMorseSign_two_mul j)
  have hsign2 : (thueMorseSign (2 * j + 1) : ℝ) =
      -(thueMorseSign j : ℝ) := by
    have h := thueMorseSign_two_mul_add_one j
    push_cast [h]
    ring
  rw [hsign1, hsign2]
  have h1 : ((2 * j : ℕ) : ℝ) + 1 / 2 = 2 * ((j : ℝ) + 1 / 4) := by
    push_cast; ring
  have h2 : ((2 * j + 1 : ℕ) : ℝ) + 1 / 2 = 2 * ((j : ℝ) + 3 / 4) := by
    push_cast; ring
  rw [h1, h2, Real.log_mul (by norm_num) (by positivity),
    Real.log_mul (by norm_num) (by positivity),
    Real.log_div (by positivity) (by positivity)]
  ring

/-- `∏_{k<2^m} (k+1/2)^(ε(k)) → exp L(1/4,3/4)`
(`eq:block-product-half`; the value `exp L(1/4,3/4) = 1/2` is the
Allouche–Riasat–Shallit quarter product, cited in the atlas). -/
theorem tendsto_block_product_half' :
    Tendsto (fun m : ℕ => ∏ k ∈ range (2 ^ m),
      ((k : ℝ) + 1 / 2) ^ (thueMorseSign k)) atTop
      (𝓝 (Real.exp (mpLimit (1 / 4) (3 / 4)))) := by
  have hexp : ∀ m : ℕ, ∏ k ∈ range (2 ^ m),
      ((k : ℝ) + 1 / 2) ^ (thueMorseSign k) =
      Real.exp (∑ k ∈ range (2 ^ m),
        (thueMorseSign k : ℝ) * Real.log ((k : ℝ) + 1 / 2)) := by
    intro m
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun k _ => ?_
    have hpos : (0 : ℝ) < (k : ℝ) + 1 / 2 := by positivity
    rw [← Real.rpow_intCast ((k : ℝ) + 1 / 2) (thueMorseSign k),
      Real.rpow_def_of_pos hpos]
    congr 1
    ring
  have hkey : ∀ m : ℕ, 1 ≤ m →
      (∑ k ∈ range (2 ^ m),
        (thueMorseSign k : ℝ) * Real.log ((k : ℝ) + 1 / 2)) =
      mpLog (1 / 4) (3 / 4) (2 ^ (m - 1)) := by
    intro m hm
    rw [show (2 : ℕ) ^ m = 2 * 2 ^ (m - 1) by
      rw [← pow_succ']
      congr 1
      omega]
    exact block_log_half (2 ^ (m - 1))
  have hlog : Tendsto (fun m : ℕ => ∑ k ∈ range (2 ^ m),
      (thueMorseSign k : ℝ) * Real.log ((k : ℝ) + 1 / 2)) atTop
      (𝓝 (mpLimit (1 / 4) (3 / 4))) := by
    refine ((tendsto_mpLimit (1 / 4) (3 / 4) (by norm_num)
      (by norm_num)).comp hpow_tendsto).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    exact (hkey m hm).symm
  have hcomp := (Real.continuous_exp.tendsto _).comp hlog
  exact Tendsto.congr (fun m => (hexp m).symm) hcomp

end Fabius
