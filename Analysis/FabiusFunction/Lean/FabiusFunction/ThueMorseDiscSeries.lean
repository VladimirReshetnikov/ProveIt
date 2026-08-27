import FabiusFunction.ThueMorseInfiniteProduct
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# The Thue–Morse power series on the unit disc

The complex-analytic foundation for the boundary theory of the atlas:
the power series

`F(z) = ∑ ε(n)·zⁿ`

as a genuine holomorphic function on the open unit disc.  This module
provides the reusable analytic core on which the natural-boundary
theorem (and, eventually, Mahler-method arguments) rest:

* `thueMorseDiscSeries` — the sum of the series.
* `summable_thueMorseDiscSeries` — absolute convergence on the disc.
* `thueMorseDiscSeries_eq_tprod` — the lacunary infinite-product
  representation `F(z) = ∏'_j (1-z^(2^j))` throughout the disc.
* `thueMorseDiscSeries_differentiableOn` — **holomorphy** on the disc,
  by locally uniform convergence of the polynomial partial sums.
* `thueMorseDiscSeries_mahler` — the Mahler functional equation
  `F(z) = (1-z)·F(z²)`, from the even/odd split of the series.
* `thueMorseDiscSeries_iterate` — the iterated form
  `F(z) = ∏_{j<k}(1-z^(2^j))·F(z^(2^k))`.
* `thueMorseDiscSeries_real_le` — on the real ray, `‖F(x)‖ ≤ 1 - x`:
  the sum is the lacunary product, and the first factor already
  vanishes at the boundary.
* `thueMorseDiscSeries_zero` — `F(0) = 1`.

The shared norm lemma `norm_thueMorseSign_complex` now lives upstream
in `ThueMorseInfiniteProduct`; its real-sign input
`abs_thueMorseSign_real` lives in `ThueMorseBoundaryFlatness`.
-/

set_option autoImplicit false

open Finset Filter Metric Set Topology

namespace Fabius

/-- The Thue–Morse power series `F(z) = ∑ ε(n)·zⁿ`. -/
noncomputable def thueMorseDiscSeries (z : ℂ) : ℂ :=
  ∑' n : ℕ, (thueMorseSign n : ℂ) * z ^ n

/-- Absolute convergence of the Thue–Morse series on the open disc. -/
theorem summable_thueMorseDiscSeries {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => (thueMorseSign n : ℂ) * z ^ n) := by
  exact summable_thueMorseSign_mul_pow_complex hz

/-- **Lacunary infinite-product representation on the unit disc**:
for `‖z‖ < 1`, `F(z) = ∏'_{j≥0} (1-z^(2^j))`. -/
theorem thueMorseDiscSeries_eq_tprod {z : ℂ} (hz : ‖z‖ < 1) :
    thueMorseDiscSeries z = ∏' j : ℕ, (1 - z ^ (2 ^ j)) := by
  simpa [thueMorseDiscSeries] using
    (tsum_thueMorseSign_mul_pow_complex hz)

/-- **Holomorphy of the Thue–Morse series** on the open unit disc:
the polynomial partial sums converge locally uniformly. -/
theorem thueMorseDiscSeries_differentiableOn :
    DifferentiableOn ℂ thueMorseDiscSeries (ball (0 : ℂ) 1) := by
  have hTLU : TendstoLocallyUniformlyOn
      (fun (N : ℕ) (z : ℂ) => ∑ n ∈ range N, (thueMorseSign n : ℂ) * z ^ n)
      (fun z => ∑' n : ℕ, (thueMorseSign n : ℂ) * z ^ n) atTop
      (ball (0 : ℂ) 1) := by
    intro u hu z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hs1 : (1 + ‖z‖) / 2 < 1 := by linarith
    have hzs : ‖z‖ < (1 + ‖z‖) / 2 := by linarith
    have hs0 : (0 : ℝ) ≤ (1 + ‖z‖) / 2 := by positivity
    have hTUO : TendstoUniformlyOn
        (fun (N : ℕ) (z : ℂ) =>
          ∑ n ∈ range N, (thueMorseSign n : ℂ) * z ^ n)
        (fun z => ∑' n : ℕ, (thueMorseSign n : ℂ) * z ^ n) atTop
        (ball (0 : ℂ) ((1 + ‖z‖) / 2)) :=
      tendstoUniformlyOn_tsum_nat
        (summable_geometric_of_lt_one hs0 hs1)
        fun n x hx => by
          rw [norm_mul, norm_pow, norm_thueMorseSign_complex, one_mul]
          exact pow_le_pow_left₀ (norm_nonneg x)
            (mem_ball_zero_iff.mp hx).le n
    refine ⟨ball (0 : ℂ) ((1 + ‖z‖) / 2) ∩ ball (0 : ℂ) 1,
      Filter.inter_mem (mem_nhdsWithin_of_mem_nhds
        (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hzs)))
        self_mem_nhdsWithin, ?_⟩
    filter_upwards [hTUO u hu] with N hN y hy using hN y hy.1
  show DifferentiableOn ℂ
    (fun z => ∑' n : ℕ, (thueMorseSign n : ℂ) * z ^ n) (ball (0 : ℂ) 1)
  refine hTLU.differentiableOn
    (Filter.Eventually.of_forall fun N => ?_) isOpen_ball
  exact (Differentiable.fun_sum fun i _ =>
    (differentiable_const _).mul (differentiable_pow i)).differentiableOn

/-- **The Mahler functional equation** `F(z) = (1-z)·F(z²)` on the
disc, from the even/odd split `ε(2k) = ε(k)`, `ε(2k+1) = -ε(k)`. -/
theorem thueMorseDiscSeries_mahler {z : ℂ} (hz : ‖z‖ < 1) :
    thueMorseDiscSeries z = (1 - z) * thueMorseDiscSeries (z ^ 2) := by
  have hz2 : ‖z ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg z) hz (by norm_num)
  have hsum2 := summable_thueMorseDiscSeries hz2
  have heven : ∀ k : ℕ,
      (thueMorseSign (2 * k) : ℂ) * z ^ (2 * k) =
      (thueMorseSign k : ℂ) * (z ^ 2) ^ k := by
    intro k
    rw [thueMorseSign_two_mul, ← pow_mul]
  have hodd : ∀ k : ℕ,
      (thueMorseSign (2 * k + 1) : ℂ) * z ^ (2 * k + 1) =
      -((thueMorseSign k : ℂ) * (z ^ 2) ^ k * z) := by
    intro k
    have h := thueMorseSign_two_mul_add_one k
    rw [pow_succ, ← pow_mul]
    push_cast [h]
    ring
  have hse : Summable
      (fun k : ℕ => (thueMorseSign (2 * k) : ℂ) * z ^ (2 * k)) :=
    hsum2.congr fun k => (heven k).symm
  have hso : Summable
      (fun k : ℕ => (thueMorseSign (2 * k + 1) : ℂ) * z ^ (2 * k + 1)) :=
    ((hsum2.mul_right z).neg).congr fun k => (hodd k).symm
  calc thueMorseDiscSeries z
      = (∑' k : ℕ, (thueMorseSign (2 * k) : ℂ) * z ^ (2 * k)) +
          ∑' k : ℕ, (thueMorseSign (2 * k + 1) : ℂ) * z ^ (2 * k + 1) :=
        (tsum_even_add_odd
          (f := fun n => (thueMorseSign n : ℂ) * z ^ n) hse hso).symm
    _ = (∑' k : ℕ, (thueMorseSign k : ℂ) * (z ^ 2) ^ k) +
          ∑' k : ℕ, -((thueMorseSign k : ℂ) * (z ^ 2) ^ k * z) := by
        rw [tsum_congr heven, tsum_congr hodd]
    _ = thueMorseDiscSeries (z ^ 2) -
          (∑' k : ℕ, (thueMorseSign k : ℂ) * (z ^ 2) ^ k) * z := by
        rw [tsum_neg, tsum_mul_right, sub_eq_add_neg, thueMorseDiscSeries]
    _ = (1 - z) * thueMorseDiscSeries (z ^ 2) := by
        rw [thueMorseDiscSeries]
        ring

/-- **The iterated Mahler equation**:
`F(z) = ∏_{j<k}(1-z^(2^j))·F(z^(2^k))`. -/
theorem thueMorseDiscSeries_iterate {z : ℂ} (hz : ‖z‖ < 1) (k : ℕ) :
    thueMorseDiscSeries z =
      (∏ j ∈ range k, (1 - z ^ 2 ^ j)) *
        thueMorseDiscSeries (z ^ 2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hzk : ‖z ^ 2 ^ k‖ < 1 := by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg z) hz (by positivity)
      rw [ih, prod_range_succ, thueMorseDiscSeries_mahler hzk,
        show (z ^ 2 ^ k) ^ 2 = z ^ 2 ^ (k + 1) by
          rw [← pow_mul, pow_succ]]
      ring

/-- On the real segment `[0,1)` the Thue–Morse series is dominated by
the single factor `1 - x` of the lacunary product — the quantitative
seed of the radial-zero argument. -/
theorem thueMorseDiscSeries_real_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ‖thueMorseDiscSeries (x : ℂ)‖ ≤ 1 - x := by
  have hreal : thueMorseDiscSeries (x : ℂ) =
      ((∑' n : ℕ, (thueMorseSign n : ℝ) * x ^ n : ℝ) : ℂ) := by
    rw [thueMorseDiscSeries, Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    push_cast
    ring
  rw [hreal, Complex.norm_real, Real.norm_eq_abs]
  rcases eq_or_lt_of_le hx0 with rfl | hx0'
  · rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
    norm_num [thueMorseSign, binaryWeight]
  · set t := -Real.log x with ht
    have htpos : 0 < t := by
      rw [ht]
      have := Real.log_neg hx0' hx1
      linarith
    have hxe : x = Real.exp (-t) := by
      rw [ht, neg_neg, Real.exp_log hx0']
    rw [hxe, tsum_thueMorseSign_exp_eq_lacunaryExpProduct t htpos,
      abs_of_pos (lacunaryExpProduct_pos t htpos)]
    have h2t : lacunaryExpProduct (2 ^ 1 * t) ≤ 1 :=
      lacunaryExpProduct_le_one (2 ^ 1 * t) (by positivity)
    have h1e : 0 ≤ 1 - Real.exp (-t) := by
      have h := Real.exp_le_one_iff.mpr (neg_nonpos.mpr htpos.le)
      linarith
    calc lacunaryExpProduct t
        = (∏ j ∈ range 1, (1 - Real.exp (-(2 ^ j * t)))) *
            lacunaryExpProduct (2 ^ 1 * t) :=
          lacunaryExpProduct_eq_prod_mul t htpos 1
      _ ≤ (1 - Real.exp (-t)) * 1 := by
          rw [prod_range_one,
            show ((2 : ℝ) ^ (0 : ℕ) * t) = t by norm_num]
          exact mul_le_mul_of_nonneg_left h2t h1e
      _ = 1 - Real.exp (-t) := mul_one _

/-- `F(0) = 1`. -/
theorem thueMorseDiscSeries_zero : thueMorseDiscSeries 0 = 1 := by
  rw [thueMorseDiscSeries,
    tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
  norm_num [thueMorseSign, binaryWeight]

end Fabius
