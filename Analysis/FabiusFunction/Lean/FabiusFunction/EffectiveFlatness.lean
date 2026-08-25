import FabiusFunction.Monotonicity
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Effective flatness of the Fabius function at the origin

`FabiusFunction.FabiusFlatness` records that the signed extension is `o(x^n)`
at the origin for every `n`.  That statement carries no constant.  This file
supplies an effective form, elementary and sharp in shape:

`F(x) ≤ 2^C(n+1,2) x^n`  whenever  `0 ≤ x`  and  `2^n x ≤ 1`.

The proof is a self-improving estimate.  Lagrange's mean value theorem applied
on `[0,x]`, together with the unified differential equation
`F'(t) = 2 up(2t - 1) = 2 F(2t)` on the first half and the monotonicity of
`F`, gives

`F(x) ≤ 2x F(2x)`   for `0 ≤ x ≤ 1/2`,

and iterating `n` times produces the factor
`2 · (2 · 2) · (2 · 2^2) ⋯ = 2^(1 + 2 + ⋯ + n) = 2^C(n+1,2)`, which is exactly
the scaling constant of equation (3).  Rvachev's function inherits the bound
at both ends of its support through `up(x) = F(1 - |x|)`.  Reflected estimates
at `1` and global versions using the truncated distance `max d 0` are included,
so callers need not separately discharge a support-side hypothesis.

`FabiusFunction.SharpFlatness` proves the strictly better bound
`F(x) ≤ 2^C(n+1,2) / n! · x^n` by running the same induction through the
fundamental theorem of calculus instead.  This module is kept because its
derivation is elementary: it uses only the mean value theorem, so it does not
drag the interval-integral machinery into the import surface of anything that
only wants a crude polynomial majorant.
-/

set_option autoImplicit false

open Set

namespace Fabius

/-- Lagrange's mean value theorem plus monotonicity give the self-improving
estimate `F(x) ≤ 2x F(2x)` on the first half of the unit interval. -/
theorem fabiusReal_le_two_mul_mul (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    fabiusReal F x ≤ 2 * x * fabiusReal F (2 * x) := by
  rcases eq_or_lt_of_le hx0 with h | h
  · rw [← h, hF.zero_of_nonpos 0 le_rfl]
    simp
  · obtain ⟨c, hc, hslope⟩ :=
      exists_hasDerivAt_eq_slope (fabiusReal F)
        (fun t : ℝ => 2 * rvachevUp F (2 * t - 1)) h
        hF.contDiff.continuous.continuousOn
        (fun t _ => fabius_hasDerivAt F hF t)
    have hslope' : 2 * rvachevUp F (2 * c - 1) =
        (fabiusReal F x - fabiusReal F 0) / (x - 0) := hslope
    rw [hF.zero_of_nonpos 0 le_rfl, sub_zero, sub_zero,
      rvachevUp_of_nonpos F (show 2 * c - 1 ≤ 0 by linarith [hc.2]),
      show 2 * c - 1 + 1 = 2 * c by ring] at hslope'
    have hmono := fabius_monotone F hF (show 2 * c ≤ 2 * x by linarith [hc.2])
    have hxne : x ≠ 0 := ne_of_gt h
    have hxval : fabiusReal F x = x * (2 * fabiusReal F (2 * c)) := by
      rw [hslope']
      field_simp
    rw [hxval]
    nlinarith [fabiusReal_nonneg F (2 * c)]

/-- The self-improving estimate `F(x) ≤ 2x F(2x)` holds on the whole half line,
with no upper restriction on `x`.

The hypothesis `x ≤ 1/2` in `fabiusReal_le_two_mul_mul` is not needed: past the
midpoint the estimate is trivially true, because `1 ≤ 2x` there and `F` is
monotone and nonnegative, so `F(x) ≤ F(2x) ≤ 2x F(2x)`.  Only the range
`0 ≤ x ≤ 1/2` requires the mean value theorem.

`fabiusReal_le_two_mul_mul` is kept unchanged as the half-interval form, and
this statement is proved from it rather than the other way round, so that the
existing declaration and its consumers are untouched. -/
theorem fabiusReal_le_two_mul_mul_of_nonneg (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx0 : 0 ≤ x) :
    fabiusReal F x ≤ 2 * x * fabiusReal F (2 * x) := by
  rcases le_or_gt x (1 / 2) with hx | hx
  · exact fabiusReal_le_two_mul_mul F hF hx0 hx
  · have hmono : fabiusReal F x ≤ fabiusReal F (2 * x) :=
      fabius_monotone F hF (show x ≤ 2 * x by linarith)
    have hnn : 0 ≤ fabiusReal F (2 * x) := fabiusReal_nonneg F (2 * x)
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * x - 1) hnn]

/-- Effective super-exponential flatness at the origin: on the dyadic scale
`2^n x ≤ 1` the Fabius function is dominated by `2^C(n+1,2) x^n`. -/
theorem fabiusReal_le_two_pow_mul_pow (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx : (2 : ℝ) ^ n * x ≤ 1) :
    fabiusReal F x ≤ 2 ^ (n + 1).choose 2 * x ^ n := by
  induction n generalizing x with
  | zero => simpa using fabiusReal_le_one F x
  | succ n ih =>
      have hps : (2 : ℝ) ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
      have hone : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      have hpow2 : (2 : ℝ) ≤ 2 ^ (n + 1) := by
        rw [hps]
        nlinarith
      have hhalf : x ≤ 1 / 2 := by nlinarith
      have hIHarg : (2 : ℝ) ^ n * (2 * x) ≤ 1 := by
        have harg : (2 : ℝ) ^ n * (2 * x) = 2 ^ (n + 1) * x := by
          rw [hps]; ring
        rw [harg]
        exact hx
      have hIH := ih (by linarith : (0 : ℝ) ≤ 2 * x) hIHarg
      have hchoose : (n + 2).choose 2 = (n + 1).choose 2 + (n + 1) := by
        rw [show n + 2 = (n + 1) + 1 by omega, show 2 = 1 + 1 by omega,
          Nat.choose_succ_succ]
        simp [Nat.choose_one_right, add_comm]
      have hxn : (2 * x) ^ n = 2 ^ n * x ^ n := by rw [mul_pow]
      calc fabiusReal F x
          ≤ 2 * x * fabiusReal F (2 * x) :=
            fabiusReal_le_two_mul_mul F hF hx0 hhalf
        _ ≤ 2 * x * (2 ^ (n + 1).choose 2 * (2 * x) ^ n) :=
            mul_le_mul_of_nonneg_left hIH (by linarith)
        _ = 2 ^ ((n + 1).choose 2 + (n + 1)) * x ^ (n + 1) := by
            rw [hxn, pow_add]; ring
        _ = 2 ^ (n + 1 + 1).choose 2 * x ^ (n + 1) := by
            rw [show n + 1 + 1 = n + 2 by omega, hchoose]

/-- Global form of effective flatness at the origin.  Truncating the distance
to `max x 0` is necessary outside the support when the power is odd. -/
theorem fabiusReal_le_two_pow_mul_max_pow (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) {x : ℝ} (hx : (2 : ℝ) ^ n * max x 0 ≤ 1) :
    fabiusReal F x ≤ 2 ^ (n + 1).choose 2 * (max x 0) ^ n := by
  by_cases hx0 : 0 ≤ x
  · rw [max_eq_left hx0] at hx ⊢
    exact fabiusReal_le_two_pow_mul_pow F hF n hx0 hx
  · have hxle : x ≤ 0 := (lt_of_not_ge hx0).le
    rw [hF.zero_of_nonpos x hxle]
    exact mul_nonneg (by positivity) (pow_nonneg (le_max_right x 0) n)

/-- Effective flatness reflected at the right endpoint of the unit interval. -/
theorem one_sub_fabiusReal_le_two_pow_mul_pow (F : BoundedFabius)
    (hF : IsFabius F) (n : ℕ) {x : ℝ} (hx1 : x ≤ 1)
    (hx : (2 : ℝ) ^ n * (1 - x) ≤ 1) :
    1 - fabiusReal F x ≤ 2 ^ (n + 1).choose 2 * (1 - x) ^ n := by
  have h := fabiusReal_le_two_pow_mul_pow F hF n (x := 1 - x) (by linarith) hx
  rwa [hF.symmetry_all x] at h

/-- Global reflected flatness estimate at the right endpoint. -/
theorem one_sub_fabiusReal_le_two_pow_mul_max_pow (F : BoundedFabius)
    (hF : IsFabius F) (n : ℕ) {x : ℝ}
    (hx : (2 : ℝ) ^ n * max (1 - x) 0 ≤ 1) :
    1 - fabiusReal F x ≤
      2 ^ (n + 1).choose 2 * (max (1 - x) 0) ^ n := by
  by_cases hx1 : x ≤ 1
  · rw [max_eq_left (sub_nonneg.mpr hx1)] at hx ⊢
    exact one_sub_fabiusReal_le_two_pow_mul_pow F hF n hx1 hx
  · have hxge : 1 ≤ x := (lt_of_not_ge hx1).le
    rw [hF.one_of_one_le x hxge, sub_self]
    exact mul_nonneg (by positivity)
      (pow_nonneg (le_max_right (1 - x) 0) n)

/-- Rvachev's function is the reflection of the Fabius function about the two
ends of its support. -/
theorem rvachevUp_eq_fabiusReal_one_sub_abs (F : BoundedFabius) (x : ℝ) :
    rvachevUp F x = fabiusReal F (1 - |x|) := by
  by_cases hx0 : 0 ≤ x
  · rw [abs_of_nonneg hx0, rvachevUp_eq_fabiusReal_one_sub F hx0]
  · have hneg : x < 0 := lt_of_not_ge hx0
    rw [abs_of_neg hneg, ← rvachevUp_even F x,
      rvachevUp_eq_fabiusReal_one_sub F (by linarith : (0 : ℝ) ≤ -x)]

/-- Effective flatness of Rvachev's function at both ends of its support. -/
theorem rvachevUp_le_two_pow_mul_pow (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) (hn : (2 : ℝ) ^ n * (1 - |x|) ≤ 1) :
    rvachevUp F x ≤ 2 ^ (n + 1).choose 2 * (1 - |x|) ^ n := by
  rw [rvachevUp_eq_fabiusReal_one_sub_abs F x]
  exact fabiusReal_le_two_pow_mul_pow F hF n (by linarith) hn

/-- Global effective flatness at both ends of the support.  The truncated
distance is zero outside `[-1,1]`, where Rvachev's function vanishes. -/
theorem rvachevUp_le_two_pow_mul_max_pow (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) {x : ℝ}
    (hn : (2 : ℝ) ^ n * max (1 - |x|) 0 ≤ 1) :
    rvachevUp F x ≤ 2 ^ (n + 1).choose 2 * (max (1 - |x|) 0) ^ n := by
  by_cases hx : |x| ≤ 1
  · rw [max_eq_left (sub_nonneg.mpr hx)] at hn ⊢
    exact rvachevUp_le_two_pow_mul_pow F hF n hx hn
  · have houtside : x ∉ Ioo (-1 : ℝ) 1 := by
      intro hmem
      have habs : |x| < 1 := abs_lt.mpr ⟨hmem.1, hmem.2⟩
      exact hx habs.le
    rw [rvachevUp_eq_zero_of_not_mem_Ioo F hF houtside]
    exact mul_nonneg (by positivity)
      (pow_nonneg (le_max_right (1 - |x|) 0) n)

end Fabius
