import FabiusFunction.ThueMorseBoundaryFlatness
import FabiusFunction.ThueMorseBooleanCube

/-!
# The analytic infinite-product identity

The atlas's opening identity `∑ ε(n)xⁿ = ∏(1 - x^(2^j))`, until now
formal only coefficientwise, holds *analytically*: for `x = e^(-t)`
with `t > 0`, the series converges absolutely and its sum equals the
convergent infinite product `𝓔(t)`.  Both sides restrict at level
`2^m` to the same finite identity, and both partial scales converge.

* `summable_thueMorseSign_mul_exp` — absolute convergence of the
  signed series at `e^(-t)`.
* `tsum_thueMorseSign_exp_eq_lacunaryExpProduct` —
  **the analytic identity** (`thm:infinite-product`):
  `∑' n, ε(n)·e^(-nt) = 𝓔(t)` for every `t > 0`.
-/

set_option autoImplicit false

open Finset Filter Topology

namespace Fabius

/-- Absolute convergence: `∑ ε(n)·e^(-nt)` is summable for `t > 0`. -/
theorem summable_thueMorseSign_mul_exp (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℕ => (thueMorseSign n : ℝ) * Real.exp (-t) ^ n) := by
  have hr1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hr0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  refine Summable.of_norm ?_
  have hgeom : Summable (fun n : ℕ => Real.exp (-t) ^ n) :=
    summable_geometric_of_lt_one hr0 hr1
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => ?_) hgeom
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hr0]
  have hsign : |(thueMorseSign n : ℝ)| = 1 := by
    rw [thueMorseSign]
    rcases Nat.even_or_odd (binaryWeight n) with h | h
    · rw [h.neg_one_pow]
      norm_num
    · rw [h.neg_one_pow]
      norm_num
  rw [hsign, one_mul]

/-- **The analytic infinite-product identity**
(`thm:infinite-product`): for every `t > 0`,
`∑' n, ε(n)·e^(-nt) = ∏_{j≥0} (1 - e^(-2^j·t)) = 𝓔(t)`. -/
theorem tsum_thueMorseSign_exp_eq_lacunaryExpProduct (t : ℝ) (ht : 0 < t) :
    ∑' n : ℕ, (thueMorseSign n : ℝ) * Real.exp (-t) ^ n =
      lacunaryExpProduct t := by
  -- the finite identity at scale `2^m`
  have hfinite : ∀ m : ℕ,
      ∑ n ∈ range (2 ^ m), (thueMorseSign n : ℝ) * Real.exp (-t) ^ n =
      ∏ j ∈ range m, (1 - Real.exp (-(2 ^ j * t))) := by
    intro m
    have h := prod_one_sub_pow_eq_sum_thueMorseSign (Real.exp (-t)) m
    rw [← h]
    refine Finset.prod_congr rfl fun j _ => ?_
    congr 1
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  -- the sum side converges along the dyadic subsequence
  have hsum := summable_thueMorseSign_mul_exp t ht
  have hS : Tendsto (fun m : ℕ =>
      ∑ n ∈ range (2 ^ m), (thueMorseSign n : ℝ) * Real.exp (-t) ^ n)
      atTop (𝓝 (∑' n : ℕ, (thueMorseSign n : ℝ) * Real.exp (-t) ^ n)) := by
    have h1 := hsum.hasSum.tendsto_sum_nat
    have h2 : Tendsto (fun m : ℕ => 2 ^ m) atTop atTop :=
      tendsto_atTop_mono (fun m => (Nat.lt_two_pow_self (n := m)).le)
        tendsto_id
    exact h1.comp h2
  -- the product side converges along partial products
  have hmult : Multipliable (fun j : ℕ => 1 - Real.exp (-(2 ^ j * t))) := by
    have h := Real.multipliable_one_add_of_summable
      (summable_exp_neg_two_pow t ht).neg
    refine h.congr fun j => ?_
    rw [← sub_eq_add_neg]
  have hP : Tendsto (fun m : ℕ =>
      ∏ j ∈ range m, (1 - Real.exp (-(2 ^ j * t))))
      atTop (𝓝 (lacunaryExpProduct t)) :=
    hmult.hasProd.tendsto_prod_nat
  -- identify the two limits
  have hEq : (fun m : ℕ =>
      ∑ n ∈ range (2 ^ m), (thueMorseSign n : ℝ) * Real.exp (-t) ^ n) =
      fun m : ℕ => ∏ j ∈ range m, (1 - Real.exp (-(2 ^ j * t))) :=
    funext hfinite
  rw [hEq] at hS
  exact tendsto_nhds_unique hS hP

end Fabius
