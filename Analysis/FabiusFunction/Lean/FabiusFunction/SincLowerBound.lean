import FabiusFunction.Basic
import FabiusFunction.WeierstrassProductBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The quadratic lower bound for the sinc function

Mathlib's `Real.sinc` supplies the definition, evenness, and the
upper bounds `sinc x ≤ 1` and `|sinc x| ≤ 1`.  What the corpus's
product estimates additionally need is the *lower* bound

`1 - x²/6 ≤ sinc x`,

the cubic sine estimate `x - x³/6 < sin x` divided by `x`, extended
to negative `x` by evenness and to the origin by the normalization
`sinc 0 = 1`.  Paired with the Weierstrass product inequality of
`WeierstrassProductBound` it converts a summable family of squared
arguments into a lower bound for a sinc product, which is how the
dyadic products are kept away from zero.

Also recorded here is the bridge from the corpus's entire
`complexSinc` to Mathlib's real one.

* `complexSinc_ofReal` — the bridge;
* `one_sub_sq_div_six_le_sinc` — **the quadratic lower bound**;
* `sinc_nonneg_of_sq_le_six` — nonnegativity on `|x| ≤ √6`.
-/

set_option autoImplicit false

namespace Fabius

/-- The corpus's entire sinc restricts to Mathlib's real one. -/
theorem complexSinc_ofReal (x : ℝ) :
    complexSinc ((x : ℝ) : ℂ) = ((Real.sinc x : ℝ) : ℂ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [complexSinc, Real.sinc]
  · have hxC : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
    rw [complexSinc, if_neg hxC, Real.sinc_of_ne_zero hx,
      ← Complex.ofReal_sin, ← Complex.ofReal_div]

/-- The quadratic lower bound on the positive axis. -/
private theorem one_sub_sq_div_six_le_sinc_of_pos {x : ℝ}
    (hx : 0 < x) : 1 - x ^ 2 / 6 ≤ Real.sinc x := by
  have hcube := Real.sin_gt_sub_cube hx
  rw [Real.sinc_of_ne_zero (ne_of_gt hx), le_div_iff₀ hx]
  nlinarith [hcube]

/-- **The quadratic lower bound**: `1 - x²/6 ≤ sinc x` for every real
`x`.  At `x = 0` it is the normalization; for `x > 0` it is the cubic
sine estimate divided by `x`; for `x < 0` it follows by evenness.
Mathlib has the matching upper bounds `Real.sinc_le_one` and
`Real.abs_sinc_le_one` but not this one. -/
theorem one_sub_sq_div_six_le_sinc (x : ℝ) :
    1 - x ^ 2 / 6 ≤ Real.sinc x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have h := one_sub_sq_div_six_le_sinc_of_pos (neg_pos.mpr hx)
    rwa [Real.sinc_neg, neg_sq] at h
  · simp
  · exact one_sub_sq_div_six_le_sinc_of_pos hx

/-- On `|x| ≤ √6` the sinc is nonnegative, by the quadratic lower
bound. -/
theorem sinc_nonneg_of_sq_le_six {x : ℝ} (hx : x ^ 2 ≤ 6) :
    0 ≤ Real.sinc x := by
  have h := one_sub_sq_div_six_le_sinc x
  have h6 : x ^ 2 / 6 ≤ 1 := by linarith
  linarith

/-! ## The dyadic sinc product -/

/-- The dyadic deficits sum to at most `4/3` of the base one. -/
private theorem sum_deficit_le {y : ℝ} (hy : 0 ≤ y) (N : ℕ) :
    ∑ n ∈ Finset.range N, y / (6 * 4 ^ n) ≤ 2 * y / 9 := by
  have hgeom : ∑ n ∈ Finset.range N, ((1 : ℝ) / 4) ^ n =
      (((1 : ℝ) / 4) ^ N - 1) / ((1 : ℝ) / 4 - 1) :=
    geom_sum_eq (by norm_num) N
  have hpow : (0 : ℝ) ≤ ((1 : ℝ) / 4) ^ N := by positivity
  have hval : (((1 : ℝ) / 4) ^ N - 1) / ((1 : ℝ) / 4 - 1) =
      4 / 3 - 4 / 3 * ((1 : ℝ) / 4) ^ N := by
    have hden : ((1 : ℝ) / 4 - 1) = -(3 / 4) := by norm_num
    rw [hden]
    field_simp
    ring
  have hle : ∑ n ∈ Finset.range N, ((1 : ℝ) / 4) ^ n ≤ 4 / 3 := by
    rw [hgeom, hval]
    linarith [hpow]
  have hrw : ∑ n ∈ Finset.range N, y / (6 * 4 ^ n) =
      y / 6 * ∑ n ∈ Finset.range N, ((1 : ℝ) / 4) ^ n := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [div_pow, one_pow]
    field_simp
  rw [hrw]
  nlinarith [hle, hy]

/-- **The finite dyadic sinc product bound**: whenever the base
argument satisfies `t² ≤ 6`, every dyadic partial product obeys

`1 - 2t²/9 ≤ ∏_{n<N} sinc(t/2ⁿ)`.

The Weierstrass product inequality turns the termwise quadratic
bound `1 - (t/2ⁿ)²/6 ≤ sinc(t/2ⁿ)` into a bound on the product, and
the deficits sum geometrically to at most `2t²/9`. -/
theorem one_sub_le_prod_sinc_two_pow {t : ℝ} (ht : t ^ 2 ≤ 6)
    (N : ℕ) :
    1 - 2 * t ^ 2 / 9 ≤
      ∏ n ∈ Finset.range N, Real.sinc (t / 2 ^ n) := by
  have hsq : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  set u : ℕ → ℝ := fun n => t ^ 2 / (6 * 4 ^ n) with hu
  have hu0 : ∀ n, 0 ≤ u n := fun n => by
    rw [hu]; positivity
  have hu1 : ∀ n, u n ≤ 1 := by
    intro n
    have h4 : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
    rw [hu]
    rw [div_le_one (by positivity)]
    nlinarith [h4, hsq]
  have hterm : ∀ n : ℕ, 1 - u n ≤ Real.sinc (t / 2 ^ n) := by
    intro n
    have h := one_sub_sq_div_six_le_sinc (t / 2 ^ n)
    have harg : (t / 2 ^ n) ^ 2 / 6 = u n := by
      rw [hu, div_pow, ← pow_mul, mul_comm n 2, pow_mul]
      norm_num
      ring
    rwa [harg] at h
  have hweier : 1 - ∑ n ∈ Finset.range N, u n ≤
      ∏ n ∈ Finset.range N, (1 - u n) :=
    one_sub_sum_range_le_prod_range_one_sub u N hu0 hu1
  have hmono : ∏ n ∈ Finset.range N, (1 - u n) ≤
      ∏ n ∈ Finset.range N, Real.sinc (t / 2 ^ n) := by
    refine Finset.prod_le_prod (fun n _ => ?_) (fun n _ => hterm n)
    have := hu1 n
    linarith
  have hsum : ∑ n ∈ Finset.range N, u n ≤ 2 * t ^ 2 / 9 :=
    sum_deficit_le hsq N
  have hchain : 1 - 2 * t ^ 2 / 9 ≤
      1 - ∑ n ∈ Finset.range N, u n := by linarith
  exact hchain.trans (hweier.trans hmono)

/-- **The dyadic products at the half-integer stay above `4/9`**: at
`t = π/2` the bound reads `1 - π²/18 > 4/9`, since `π² < 10`. -/
theorem four_ninths_lt_prod_sinc_pi_div_two (N : ℕ) :
    4 / 9 < ∏ n ∈ Finset.range N, Real.sinc (Real.pi / 2 / 2 ^ n) := by
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsq : (Real.pi / 2) ^ 2 ≤ 6 := by
    nlinarith [hpi, hpi0]
  have h := one_sub_le_prod_sinc_two_pow hsq N
  have hlt : (4 : ℝ) / 9 < 1 - 2 * (Real.pi / 2) ^ 2 / 9 := by
    nlinarith [hpi, hpi0]
  exact hlt.trans_le h

end Fabius
