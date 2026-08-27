import FabiusFunction.ThueMorseBoundaryFlatness
import FabiusFunction.ThueMorseBooleanCube

/-!
# The analytic infinite-product identity

The atlas's opening identity `∑ ε(n)xⁿ = ∏(1 - x^(2^j))`, until now
formal only coefficientwise, holds *analytically* on the whole real
interval `|x| < 1` — negative `x` and `x = 0` included.  The series
converges absolutely, the lacunary product converges, and the two
limits agree because both sides restrict at level `2^m` to the same
finite identity (`prod_one_sub_pow_eq_sum_thueMorseSign`, valid over
any commutative ring), while both partial scales converge.

* `summable_thueMorseSign_mul_pow` — absolute convergence of the
  signed series at any real `x` with `|x| < 1`.
* `summable_pow_two_pow` and `multipliable_one_sub_pow_two_pow` — the
  lacunary product `∏_j (1 - x^(2^j))` converges for `|x| < 1`.
* `tsum_thueMorseSign_mul_pow` — **the analytic identity**
  (`thm:infinite-product`) in its general form:
  `∑' n, ε(n)·xⁿ = ∏'_j (1 - x^(2^j))` whenever `|x| < 1`.
  `hasProd_one_sub_pow_two_pow` and
  `tendsto_prod_one_sub_pow_two_pow` restate it as convergence of the
  partial products to the sum of the series.
* `summable_thueMorseSign_mul_exp` — absolute convergence of the
  signed series at `e^(-t)`.
* `tsum_thueMorseSign_exp_eq_lacunaryExpProduct` —
  **the analytic identity** on the exponential ray:
  `∑' n, ε(n)·e^(-nt) = 𝓔(t)` for every `t > 0`.  Both ray statements
  are now one-line specialisations of the general ones, through
  `abs_exp_neg_lt_one`.
-/

set_option autoImplicit false

open Finset Filter Topology

namespace Fabius

/-- **Absolute convergence** of the signed Thue–Morse series on the
whole interval `|x| < 1`: since `|ε(n)| = 1`, the series is dominated
termwise by the geometric series `∑ |x|ⁿ`. -/
theorem summable_thueMorseSign_mul_pow {x : ℝ} (hx : |x| < 1) :
    Summable (fun n : ℕ => (thueMorseSign n : ℝ) * x ^ n) := by
  refine Summable.of_norm ?_
  have hgeom : Summable (fun n : ℕ => |x| ^ n) :=
    summable_geometric_of_lt_one (abs_nonneg x) hx
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => ?_) hgeom
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs]
  have hsign : |(thueMorseSign n : ℝ)| = 1 := by
    rw [thueMorseSign]
    rcases Nat.even_or_odd (binaryWeight n) with h | h
    · rw [h.neg_one_pow]
      norm_num
    · rw [h.neg_one_pow]
      norm_num
  rw [hsign, one_mul]

/-- The lacunary powers `x^(2^j)` are summable for `|x| < 1`: they are
dominated by `|x|^j`, because `j ≤ 2^j`. -/
theorem summable_pow_two_pow {x : ℝ} (hx : |x| < 1) :
    Summable (fun j : ℕ => x ^ (2 ^ j)) := by
  refine Summable.of_norm ?_
  have hgeom : Summable (fun j : ℕ => |x| ^ j) :=
    summable_geometric_of_lt_one (abs_nonneg x) hx
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _)
    (fun j => ?_) hgeom
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_of_le_one (abs_nonneg x) hx.le
    (by have := Nat.lt_two_pow_self (n := j); omega)

/-- The lacunary product `∏_j (1 - x^(2^j))` is multipliable for every
real `x` with `|x| < 1`. -/
theorem multipliable_one_sub_pow_two_pow {x : ℝ} (hx : |x| < 1) :
    Multipliable (fun j : ℕ => 1 - x ^ (2 ^ j)) := by
  have h := Real.multipliable_one_add_of_summable
    (summable_pow_two_pow hx).neg
  refine h.congr fun j => ?_
  rw [← sub_eq_add_neg]

/-- **The analytic infinite-product identity** (`thm:infinite-product`)
in its general form: for every real `x` with `|x| < 1`,
`∑' n, ε(n)·xⁿ = ∏'_{j≥0} (1 - x^(2^j))`.

Both sides are limits along the dyadic scale of the *same* finite
identity `∏_{j<m}(1 - x^(2^j)) = ∑_{n<2^m} ε(n)·xⁿ`, which holds over
any commutative ring. -/
theorem tsum_thueMorseSign_mul_pow {x : ℝ} (hx : |x| < 1) :
    ∑' n : ℕ, (thueMorseSign n : ℝ) * x ^ n =
      ∏' j : ℕ, (1 - x ^ (2 ^ j)) := by
  -- the finite identity at scale `2^m`
  have hfinite : ∀ m : ℕ,
      ∑ n ∈ range (2 ^ m), (thueMorseSign n : ℝ) * x ^ n =
      ∏ j ∈ range m, (1 - x ^ (2 ^ j)) := fun m =>
    (prod_one_sub_pow_eq_sum_thueMorseSign x m).symm
  -- the sum side converges along the dyadic subsequence
  have hsum := summable_thueMorseSign_mul_pow hx
  have hS : Tendsto (fun m : ℕ =>
      ∑ n ∈ range (2 ^ m), (thueMorseSign n : ℝ) * x ^ n)
      atTop (𝓝 (∑' n : ℕ, (thueMorseSign n : ℝ) * x ^ n)) := by
    have h1 := hsum.hasSum.tendsto_sum_nat
    have h2 : Tendsto (fun m : ℕ => 2 ^ m) atTop atTop :=
      tendsto_atTop_mono (fun m => (Nat.lt_two_pow_self (n := m)).le)
        tendsto_id
    exact h1.comp h2
  -- the product side converges along partial products
  have hP : Tendsto (fun m : ℕ => ∏ j ∈ range m, (1 - x ^ (2 ^ j)))
      atTop (𝓝 (∏' j : ℕ, (1 - x ^ (2 ^ j)))) :=
    (multipliable_one_sub_pow_two_pow hx).hasProd.tendsto_prod_nat
  -- identify the two limits
  have hEq : (fun m : ℕ =>
      ∑ n ∈ range (2 ^ m), (thueMorseSign n : ℝ) * x ^ n) =
      fun m : ℕ => ∏ j ∈ range m, (1 - x ^ (2 ^ j)) :=
    funext hfinite
  rw [hEq] at hS
  exact tendsto_nhds_unique hS hP

/-- `HasProd` form of the identity: the lacunary product converges,
in the unordered sense, to the sum of the signed series. -/
theorem hasProd_one_sub_pow_two_pow {x : ℝ} (hx : |x| < 1) :
    HasProd (fun j : ℕ => 1 - x ^ (2 ^ j))
      (∑' n : ℕ, (thueMorseSign n : ℝ) * x ^ n) :=
  (multipliable_one_sub_pow_two_pow hx).hasProd_iff.mpr
    (tsum_thueMorseSign_mul_pow hx).symm

/-- Partial-product form of the identity: the truncated products
`∏_{j<m}(1 - x^(2^j))` converge to `∑' n, ε(n)·xⁿ`. -/
theorem tendsto_prod_one_sub_pow_two_pow {x : ℝ} (hx : |x| < 1) :
    Tendsto (fun m : ℕ => ∏ j ∈ range m, (1 - x ^ (2 ^ j))) atTop
      (𝓝 (∑' n : ℕ, (thueMorseSign n : ℝ) * x ^ n)) :=
  (hasProd_one_sub_pow_two_pow hx).tendsto_prod_nat

/-- The exponential ray lands inside the unit interval: `|e^(-t)| < 1`
for `t > 0`. -/
theorem abs_exp_neg_lt_one {t : ℝ} (ht : 0 < t) :
    |Real.exp (-t)| < 1 := by
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_lt_one_iff.mpr (by linarith)

/-- Absolute convergence: `∑ ε(n)·e^(-nt)` is summable for `t > 0`. -/
theorem summable_thueMorseSign_mul_exp (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℕ => (thueMorseSign n : ℝ) * Real.exp (-t) ^ n) :=
  summable_thueMorseSign_mul_pow (abs_exp_neg_lt_one ht)

/-- **The analytic infinite-product identity**
(`thm:infinite-product`): for every `t > 0`,
`∑' n, ε(n)·e^(-nt) = ∏_{j≥0} (1 - e^(-2^j·t)) = 𝓔(t)`.  This is the
general identity `tsum_thueMorseSign_mul_pow` at `x = e^(-t)`, the
factors being rewritten by `e^(-t)^(2^j) = e^(-2^j·t)`. -/
theorem tsum_thueMorseSign_exp_eq_lacunaryExpProduct (t : ℝ) (ht : 0 < t) :
    ∑' n : ℕ, (thueMorseSign n : ℝ) * Real.exp (-t) ^ n =
      lacunaryExpProduct t := by
  have hE : lacunaryExpProduct t =
      ∏' j : ℕ, (1 - Real.exp (-(2 ^ j * t))) := rfl
  rw [tsum_thueMorseSign_mul_pow (abs_exp_neg_lt_one ht), hE]
  refine tprod_congr fun j => ?_
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

end Fabius
