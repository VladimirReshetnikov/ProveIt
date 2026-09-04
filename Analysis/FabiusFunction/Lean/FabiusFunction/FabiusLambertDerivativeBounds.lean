import FabiusFunction.LaplacePeriodicSecondOrder
import FabiusFunction.FabiusLambertSaddle

/-!
# Second and third logarithmic derivatives on the real dyadic orbit

Write `q` for the negative-Laplace logarithm of the Fabius function and `Ψ`
for the zero-mean one-periodic correction appearing in its
quadratic-plus-periodic decomposition.  `FabiusFunction.LaplacePeriodicSecondOrder`
establishes the exact first-derivative identity

`q'(s) = (-log s / log 2 + 1/2 + Ψ'(logb 2 s) / log 2) / s - T₁(s)`,

valid for every `s > 0`, where `T₁ = negativeLaplaceForwardTailFirst` is the
exponentially small forward tail.  This module differentiates that identity
twice more, producing exact all-real formulas of the same shape for `q''` and
`q'''`, and then restricts them to the real dyadic orbit `s = 2 ^ b`.  On that
orbit `logb 2 s = b`, so the periodic terms become `Ψ'(b)`, `Ψ''(b)`,
`Ψ'''(b)` -- bounded because `Ψ` is `C⁴` and one-periodic -- and the only
unbounded contribution is an explicit term linear in `b`.  Removing it leaves
the three scaled residuals

```
R₁ b = 2 ^ b * q' (2 ^ b) + b
R₂ b = (2 ^ b) ^ 2 * q'' (2 ^ b) - b
R₃ b = (2 ^ b) ^ 3 * q''' (2 ^ b) + 2 * b
```

each bounded uniformly over `b ≥ 0`.

The orbit `s = 2 ^ b` is not an arbitrary choice: it is exactly where the
explicit lower-Lambert saddle of `FabiusFunction.FabiusLambertSaddle` lives,
since there the radius is `r = 2 ^ lambda` and the saddle equation `r * x =
lambda` identifies the phase `b` with `lambda`.  This module is the
derivative-estimate layer under that saddle.  Its sole consumer,
`FabiusFunction.FabiusSaddleCentralLambert`, rewrites the odd linear and cubic
saddle coefficients as `(R₁ b - 1) / sqrt b` and `(2 + 2 * b - R₃ b) /
(6 * b * sqrt b)`, so the uniform bounds below are precisely what make both
coefficients `O(b ^ (-1/2))`; `R₂` supplies the curvature defect between the
exact quadratic term and the standard Gaussian exponent.

## Main results

* `negativeLaplaceLogSecond_eq_periodic` and `negativeLaplaceLogThird_eq_periodic`
  -- exact quadratic-plus-periodic formulas for `q''` and `q'''` on `(0, ∞)`,
  each equal to a periodic-plus-logarithmic numerator over `s ^ 2`, `s ^ 3`
  minus the corresponding forward tail.
* `negativeLaplaceRpowFirstResidual`, `negativeLaplaceRpowSecondResidual`,
  `negativeLaplaceRpowThirdResidual` -- the residuals `R₁`, `R₂`, `R₃`, with
  `_eq` lemmas giving their closed forms in terms of `Ψ'`, `Ψ''`, `Ψ'''` and
  the forward tails.
* `exists_bound_abs_negativeLaplaceRpowFirstResidual` and its second- and
  third-order companions -- the uniform residual bounds on `b ≥ 0` that the
  saddle analysis consumes.
* `norm_negativeLaplaceForwardTailSecond_le_inv_cube` and
  `norm_negativeLaplaceForwardTailThird_le_inv_fourth` -- explicit tail decay
  `48 / s ^ 3` and `768 / s ^ 4` for `s ≥ 1`, together with sharper scaled
  bounds `abs_mul_negativeLaplaceForwardTailFirst_le_div`,
  `abs_sq_mul_negativeLaplaceForwardTailSecond_le_div` and
  `abs_cube_mul_negativeLaplaceForwardTailThird_le_div` of order `1 / s`;
  the pre-existing constant bounds are retained as convenient corollaries.
  Both families are instances of two generic estimates stated here:
  `norm_tsum_le_two_mul_of_norm_le_half_pow` sums a geometric majorant,
  and `abs_pow_mul_le_div_of_norm_le` rescales a `C / s ^ (k + 1)` bound
  by `s ^ k`.
* `negativeLaplacePsiThird` -- the third derivative of `Ψ`, one order past
  where `FabiusFunction.PeriodicRegularity` stops, with the expected
  periodicity, continuity, boundedness and `HasDerivAt` support lemmas, plus
  `exists_bound_abs_deriv_negativeLaplacePsi` supplying the first-derivative
  analogue of the existing second-derivative bound.

## Conventions and caveats

The derivative identities are unconditional on `(0, ∞)`; every *bound* here is
restricted to `s ≥ 1`, equivalently `b ≥ 0`, and the residual bounds take `b`
as an implicit argument.  The numeric constants `8`, `48`, `768` are explicit
but merely sufficient, not sharp: they come from the crude estimates
`x ^ k * exp (-x) ≤ k!` and `(1 - exp (-x)) ^ (-m) ≤ 2 ^ m` for `x ≥ 1`, summed
against a geometric series in the dyadic index.  The residual bounds, by
contrast, are pure existence statements -- the constants are extracted from
boundedness of the range of a continuous one-periodic function and are never
named.  `Ψ` here is the *normalized* correction, with its mean over a period
subtracted; all logarithms are natural, with the base-2 scale carried by the
explicit `log 2` denominators.
-/

set_option autoImplicit false

open Filter Set Asymptotics
open scoped Topology

namespace Fabius

/-- The third derivative of the periodic correction. -/
noncomputable def negativeLaplacePsiThird (t : ℝ) : ℝ :=
  deriv (deriv (deriv negativeLaplacePsi)) t

/-- The second derivative of the normalized periodic correction `Ψ` is `C²`.
Used in this file by `negativeLaplacePsi_secondDeriv_hasDerivAt` and by
`continuous_negativeLaplacePsiThird`. -/
theorem contDiff_secondDeriv_negativeLaplacePsi :
    ContDiff ℝ 2 (deriv (deriv negativeLaplacePsi)) := by
  apply ContDiff.deriv'
  simpa only [show (2 : WithTop ℕ∞) + 1 = 3 by norm_num] using
    contDiff_deriv_negativeLaplacePsi

/-- At every real `t` the second derivative of `Ψ` is differentiable, with
derivative `negativeLaplacePsiThird t`. -/
theorem negativeLaplacePsi_secondDeriv_hasDerivAt (t : ℝ) :
    HasDerivAt (deriv (deriv negativeLaplacePsi))
      (negativeLaplacePsiThird t) t := by
  exact (contDiff_secondDeriv_negativeLaplacePsi.differentiable
    (by norm_num) t).hasDerivAt

/-- The third derivative of `Ψ` is unchanged by a unit shift of its
argument. -/
theorem negativeLaplacePsiThird_add_one (t : ℝ) :
    negativeLaplacePsiThird (t + 1) = negativeLaplacePsiThird t := by
  have hshift := (negativeLaplacePsi_secondDeriv_hasDerivAt (t + 1)).comp t
    ((hasDerivAt_id t).add_const 1)
  have heq : deriv (deriv negativeLaplacePsi) =ᶠ[𝓝 t]
      deriv (deriv negativeLaplacePsi) ∘ (fun u : ℝ => id u + 1) :=
    Eventually.of_forall fun u =>
      (negativeLaplacePsi_secondDeriv_add_one u).symm
  simpa [negativeLaplacePsiThird] using
    (hshift.congr_of_eventuallyEq heq).unique
      (negativeLaplacePsi_secondDeriv_hasDerivAt t)

/-- The third derivative of `Ψ` is one-periodic. -/
theorem negativeLaplacePsiThird_periodic :
    Function.Periodic negativeLaplacePsiThird 1 :=
  negativeLaplacePsiThird_add_one

/-- The third derivative of `Ψ` is continuous on all of `ℝ`. -/
theorem continuous_negativeLaplacePsiThird :
    Continuous negativeLaplacePsiThird := by
  unfold negativeLaplacePsiThird
  exact contDiff_secondDeriv_negativeLaplacePsi.continuous_deriv (by norm_num)

/-- The range of the third derivative of `Ψ` is bounded, since a continuous
one-periodic function has bounded range. -/
theorem isBounded_range_negativeLaplacePsiThird :
    Bornology.IsBounded (range negativeLaplacePsiThird) :=
  negativeLaplacePsiThird_periodic.isBounded_of_continuous one_ne_zero
    continuous_negativeLaplacePsiThird

/-- Some nonnegative constant bounds `|Ψ'|` at every real point.  The constant
is only asserted to exist and is never named.  This is the first-derivative
analogue of `exists_bound_abs_secondDeriv_negativeLaplacePsi`; all three
residual bounds in this file consume it. -/
theorem exists_bound_abs_deriv_negativeLaplacePsi :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |deriv negativeLaplacePsi t| ≤ C := by
  exact exists_nonneg_bound_abs_of_isBounded_range
    (deriv negativeLaplacePsi) isBounded_range_deriv_negativeLaplacePsi

/-- Some nonnegative constant bounds `|Ψ'''|` at every real point, extracted
from boundedness of its range.  Used in this file by
`exists_bound_abs_negativeLaplaceRpowThirdResidual`. -/
theorem exists_bound_abs_negativeLaplacePsiThird :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |negativeLaplacePsiThird t| ≤ C := by
  exact exists_nonneg_bound_abs_of_isBounded_range negativeLaplacePsiThird
    isBounded_range_negativeLaplacePsiThird

/-- Summing a geometric majorant.  If every term of a real series is
bounded in norm by `C * (1 / 2) ^ n`, then the series is summable and
its sum is bounded in norm by `2 * C`.  This is the common step behind
the explicit forward-tail decay bounds in this file; the constant `C` is
allowed to depend on anything but the summation index. -/
theorem norm_tsum_le_two_mul_of_norm_le_half_pow {f : ℕ → ℝ} {C : ℝ}
    (h : ∀ n, ‖f n‖ ≤ C * (1 / 2 : ℝ) ^ n) :
    ‖∑' n, f n‖ ≤ 2 * C := by
  have hgeom : Summable (fun n : ℕ => C * (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left _
  have hf : Summable f := hgeom.of_norm_bounded h
  calc
    ‖∑' n, f n‖ ≤ ∑' n, ‖f n‖ := norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' n, C * (1 / 2 : ℝ) ^ n := hf.norm.tsum_le_tsum h hgeom
    _ = 2 * C := by
      rw [tsum_mul_left,
        tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
      ring

private lemma norm_negativeLaplaceForwardTermSecond_le_invCube_geometric
    {s : ℝ} (hs : 1 ≤ s) (n : ℕ) :
    ‖negativeLaplaceForwardTermSecond s n‖ ≤
      (24 / s ^ 3) * (1 / 2 : ℝ) ^ n := by
  let a : ℝ := (2 : ℝ) ^ n
  let y : ℝ := s * a
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have ha : 0 < a := by dsimp [a]; positivity
  have hy : 1 ≤ y := by
    dsimp [y]
    have ha1 : 1 ≤ a := one_le_pow₀ (by norm_num)
    nlinarith
  have hfrac := exp_neg_div_one_sub_pow_le 2 hy
  norm_num at hfrac
  have hpow := pow_mul_exp_neg_le_factorial 3 (by positivity : 0 ≤ y)
  norm_num at hpow
  unfold negativeLaplaceForwardTermSecond
  change ‖-(a ^ 2 * Real.exp (-y) / (1 - Real.exp (-y)) ^ 2)‖ ≤ _
  rw [norm_neg, Real.norm_eq_abs, abs_of_pos (div_pos
    (mul_pos (sq_pos_of_pos ha) (Real.exp_pos _)) (by
      have : Real.exp (-y) < 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.mpr (by linarith)
      positivity))]
  calc
    a ^ 2 * Real.exp (-y) / (1 - Real.exp (-y)) ^ 2 ≤
        a ^ 2 * (4 * Real.exp (-y)) := by
      calc
        a ^ 2 * Real.exp (-y) / (1 - Real.exp (-y)) ^ 2 =
            a ^ 2 * (Real.exp (-y) / (1 - Real.exp (-y)) ^ 2) := by ring
        _ ≤ a ^ 2 * (4 * Real.exp (-y)) := by gcongr
    _ ≤ (24 / s ^ 3) * (1 / 2 : ℝ) ^ n := by
      have hgeom : (1 / 2 : ℝ) ^ n = 1 / a := by
        dsimp [a]
        rw [one_div_pow]
      rw [hgeom]
      rw [show 24 / s ^ 3 * (1 / a) = 24 / (s ^ 3 * a) by field_simp]
      rw [le_div_iff₀ (mul_pos (pow_pos hs0 3) ha)]
      dsimp [y] at hpow
      nlinarith

/-- For `s ≥ 1` the second forward tail obeys
`‖negativeLaplaceForwardTailSecond s‖ ≤ 48 / s ^ 3`.  The constant is
explicit but merely sufficient: it is the sum of a geometric majorant of the
individual terms. -/
theorem norm_negativeLaplaceForwardTailSecond_le_inv_cube
    {s : ℝ} (hs : 1 ≤ s) :
    ‖negativeLaplaceForwardTailSecond s‖ ≤ 48 / s ^ 3 := by
  have h := norm_tsum_le_two_mul_of_norm_le_half_pow
    (norm_negativeLaplaceForwardTermSecond_le_invCube_geometric hs)
  calc
    ‖negativeLaplaceForwardTailSecond s‖ =
        ‖∑' n : ℕ, negativeLaplaceForwardTermSecond s n‖ := rfl
    _ ≤ 2 * (24 / s ^ 3) := h
    _ = 48 / s ^ 3 := by ring

private lemma norm_negativeLaplaceForwardTermThird_le_invFourth_geometric
    {s : ℝ} (hs : 1 ≤ s) (n : ℕ) :
    ‖negativeLaplaceForwardTermThird s n‖ ≤
      (384 / s ^ 4) * (1 / 2 : ℝ) ^ n := by
  let a : ℝ := (2 : ℝ) ^ n
  let y : ℝ := s * a
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have ha : 0 < a := by dsimp [a]; positivity
  have hy : 1 ≤ y := by
    dsimp [y]
    have ha1 : 1 ≤ a := one_le_pow₀ (by norm_num)
    nlinarith
  have he : Real.exp (-y) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hfrac := exp_neg_div_one_sub_pow_le 3 hy
  norm_num at hfrac
  have hpow := pow_mul_exp_neg_le_factorial 4 (by positivity : 0 ≤ y)
  norm_num at hpow
  unfold negativeLaplaceForwardTermThird
  change ‖a ^ 3 * Real.exp (-y) * (1 + Real.exp (-y)) /
      (1 - Real.exp (-y)) ^ 3‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_pos (div_pos
    (mul_pos (mul_pos (pow_pos ha 3) (Real.exp_pos _)) (by positivity)) (by
      have : Real.exp (-y) < 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.mpr (by linarith)
      positivity))]
  calc
    a ^ 3 * Real.exp (-y) * (1 + Real.exp (-y)) /
          (1 - Real.exp (-y)) ^ 3 ≤
        a ^ 3 * (16 * Real.exp (-y)) := by
      calc
        a ^ 3 * Real.exp (-y) * (1 + Real.exp (-y)) /
              (1 - Real.exp (-y)) ^ 3 =
            a ^ 3 * (Real.exp (-y) / (1 - Real.exp (-y)) ^ 3) *
              (1 + Real.exp (-y)) := by ring
        _ ≤ a ^ 3 * (8 * Real.exp (-y)) * 2 := by gcongr; linarith
        _ = a ^ 3 * (16 * Real.exp (-y)) := by ring
    _ ≤ (384 / s ^ 4) * (1 / 2 : ℝ) ^ n := by
      have hgeom : (1 / 2 : ℝ) ^ n = 1 / a := by
        dsimp [a]
        rw [one_div_pow]
      rw [hgeom]
      rw [show 384 / s ^ 4 * (1 / a) = 384 / (s ^ 4 * a) by field_simp]
      rw [le_div_iff₀ (mul_pos (pow_pos hs0 4) ha)]
      dsimp [y] at hpow
      nlinarith

/-- For `s ≥ 1` the third forward tail obeys
`‖negativeLaplaceForwardTailThird s‖ ≤ 768 / s ^ 4`, again by summing a
geometric majorant; the constant is sufficient, not sharp. -/
theorem norm_negativeLaplaceForwardTailThird_le_inv_fourth
    {s : ℝ} (hs : 1 ≤ s) :
    ‖negativeLaplaceForwardTailThird s‖ ≤ 768 / s ^ 4 := by
  have h := norm_tsum_le_two_mul_of_norm_le_half_pow
    (norm_negativeLaplaceForwardTermThird_le_invFourth_geometric hs)
  calc
    ‖negativeLaplaceForwardTailThird s‖ =
        ‖∑' n : ℕ, negativeLaplaceForwardTermThird s n‖ := rfl
    _ ≤ 2 * (384 / s ^ 4) := h
    _ = 768 / s ^ 4 := by ring

private lemma hasDerivAt_logb_two {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.logb 2 x)
      ((1 / s) / Real.log 2) s := by
  unfold Real.logb
  simpa [one_div] using (Real.hasDerivAt_log hs).div_const (Real.log 2)

/-- Exact all-real second derivative of the quadratic-plus-periodic Laplace decomposition. -/
theorem negativeLaplaceLogSecond_eq_periodic
    (F : BoundedFabius) (hF : IsFabius F) {s : ℝ} (hs : 0 < s) :
    negativeLaplaceLogSecond F s =
      (Real.log s / Real.log 2 - 1 / 2 - 1 / Real.log 2 -
          deriv negativeLaplacePsi (Real.logb 2 s) / Real.log 2 +
          deriv (deriv negativeLaplacePsi) (Real.logb 2 s) /
            (Real.log 2) ^ 2) / s ^ 2 -
        negativeLaplaceForwardTailSecond s := by
  let A : ℝ → ℝ := fun x =>
    -Real.log x / Real.log 2 + 1 / 2 +
      deriv negativeLaplacePsi (Real.logb 2 x) / Real.log 2
  have hlog := Real.hasDerivAt_log hs.ne'
  have hlogb : HasDerivAt (fun x : ℝ => Real.logb 2 x)
      ((1 / s) / Real.log 2) s := hasDerivAt_logb_two hs.ne'
  have hpsi := (negativeLaplacePsi_deriv_hasDerivAt
    (Real.logb 2 s)).comp s hlogb
  have hAraw := (hlog.neg.div_const (Real.log 2)).add_const (1 / 2) |>.add
    (hpsi.div_const (Real.log 2))
  have hA : HasDerivAt A
      (-1 / (s * Real.log 2) +
        deriv (deriv negativeLaplacePsi) (Real.logb 2 s) /
          (s * (Real.log 2) ^ 2)) s := by
    refine (hAraw.congr_deriv ?_).congr_of_eventuallyEq ?_
    · field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne', hs.ne']
    · filter_upwards with x
      rfl
  have hmain := hA.div (hasDerivAt_id s) hs.ne'
  have htail := negativeLaplaceForwardTailFirst_hasDerivAt s hs
  let rhs : ℝ → ℝ := fun x => A x / x - negativeLaplaceForwardTailFirst x
  have hrhs : HasDerivAt rhs
      ((Real.log s / Real.log 2 - 1 / 2 - 1 / Real.log 2 -
          deriv negativeLaplacePsi (Real.logb 2 s) / Real.log 2 +
          deriv (deriv negativeLaplacePsi) (Real.logb 2 s) /
            (Real.log 2) ^ 2) / s ^ 2 -
        negativeLaplaceForwardTailSecond s) s := by
    have h := hmain.sub htail
    refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
    · dsimp [A]
      field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne', hs.ne']
      ring
    · filter_upwards with x
      rfl
  have heq : negativeLaplaceLogFirst F =ᶠ[nhds s] rhs := by
    filter_upwards [Ioi_mem_nhds hs] with x hx
    rw [negativeLaplaceLogFirst_eq_periodic F hF hx]
  exact (negativeLaplaceLogFirst_hasDerivAt F hF hs).unique
    (hrhs.congr_of_eventuallyEq heq)

/-- Exact all-real third derivative of the quadratic-plus-periodic Laplace decomposition. -/
theorem negativeLaplaceLogThird_eq_periodic
    (F : BoundedFabius) (hF : IsFabius F) {s : ℝ} (hs : 0 < s) :
    negativeLaplaceLogThird F s =
      (-2 * Real.log s / Real.log 2 + 1 + 3 / Real.log 2 +
          2 * deriv negativeLaplacePsi (Real.logb 2 s) / Real.log 2 -
          3 * deriv (deriv negativeLaplacePsi) (Real.logb 2 s) /
            (Real.log 2) ^ 2 +
          negativeLaplacePsiThird (Real.logb 2 s) / (Real.log 2) ^ 3) /
        s ^ 3 - negativeLaplaceForwardTailThird s := by
  let B : ℝ → ℝ := fun x =>
    Real.log x / Real.log 2 - 1 / 2 - 1 / Real.log 2 -
      deriv negativeLaplacePsi (Real.logb 2 x) / Real.log 2 +
      deriv (deriv negativeLaplacePsi) (Real.logb 2 x) / (Real.log 2) ^ 2
  have hlog := Real.hasDerivAt_log hs.ne'
  have hlogb : HasDerivAt (fun x : ℝ => Real.logb 2 x)
      ((1 / s) / Real.log 2) s := hasDerivAt_logb_two hs.ne'
  have hpsi1 := (negativeLaplacePsi_deriv_hasDerivAt
    (Real.logb 2 s)).comp s hlogb
  have hpsi2 := (negativeLaplacePsi_secondDeriv_hasDerivAt
    (Real.logb 2 s)).comp s hlogb
  have hBraw := (((hlog.div_const (Real.log 2)).sub_const (1 / 2) |>.sub_const
    (1 / Real.log 2)).sub (hpsi1.div_const (Real.log 2))).add
      (hpsi2.div_const ((Real.log 2) ^ 2))
  have hB : HasDerivAt B
      (1 / (s * Real.log 2) -
        deriv (deriv negativeLaplacePsi) (Real.logb 2 s) /
          (s * (Real.log 2) ^ 2) +
        negativeLaplacePsiThird (Real.logb 2 s) /
          (s * (Real.log 2) ^ 3)) s := by
    refine (hBraw.congr_deriv ?_).congr_of_eventuallyEq ?_
    · unfold negativeLaplacePsiThird
      field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne', hs.ne']
    · filter_upwards with x
      rfl
  have hden := (hasDerivAt_id s).pow 2
  have hmain := hB.div hden (pow_ne_zero 2 hs.ne')
  have htail := negativeLaplaceForwardTailSecond_hasDerivAt s hs
  let rhs : ℝ → ℝ := fun x => B x / x ^ 2 - negativeLaplaceForwardTailSecond x
  have hrhs : HasDerivAt rhs
      ((-2 * Real.log s / Real.log 2 + 1 + 3 / Real.log 2 +
          2 * deriv negativeLaplacePsi (Real.logb 2 s) / Real.log 2 -
          3 * deriv (deriv negativeLaplacePsi) (Real.logb 2 s) /
            (Real.log 2) ^ 2 +
          negativeLaplacePsiThird (Real.logb 2 s) / (Real.log 2) ^ 3) /
        s ^ 3 - negativeLaplaceForwardTailThird s) s := by
    have h := hmain.sub htail
    refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
    · dsimp [B]
      field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne', hs.ne']
      ring
    · filter_upwards with x
      rfl
  have heq : negativeLaplaceLogSecond F =ᶠ[nhds s] rhs := by
    filter_upwards [Ioi_mem_nhds hs] with x hx
    rw [negativeLaplaceLogSecond_eq_periodic F hF hx]
  exact (negativeLaplaceLogSecond_hasDerivAt F hF hs).unique
    (hrhs.congr_of_eventuallyEq heq)

/-- Scaled first-log-derivative residual on the real dyadic orbit. -/
noncomputable def negativeLaplaceRpowFirstResidual
    (F : BoundedFabius) (b : ℝ) : ℝ :=
  (2 : ℝ) ^ b * negativeLaplaceLogFirst F ((2 : ℝ) ^ b) + b

/-- Scaled curvature residual on the real dyadic orbit. -/
noncomputable def negativeLaplaceRpowSecondResidual
    (F : BoundedFabius) (b : ℝ) : ℝ :=
  ((2 : ℝ) ^ b) ^ 2 * negativeLaplaceLogSecond F ((2 : ℝ) ^ b) - b

/-- Scaled cubic residual after removing its linear-in-phase main term. -/
noncomputable def negativeLaplaceRpowThirdResidual
    (F : BoundedFabius) (b : ℝ) : ℝ :=
  ((2 : ℝ) ^ b) ^ 3 * negativeLaplaceLogThird F ((2 : ℝ) ^ b) + 2 * b

/-- Closed form of the first residual on the real dyadic orbit, for a Fabius
function `F` and every real `b`: it equals `1 / 2 + Ψ'(b) / log 2` minus the
scaled tail `2 ^ b * negativeLaplaceForwardTailFirst (2 ^ b)`. -/
theorem negativeLaplaceRpowFirstResidual_eq
    (F : BoundedFabius) (hF : IsFabius F) (b : ℝ) :
    negativeLaplaceRpowFirstResidual F b =
      1 / 2 + deriv negativeLaplacePsi b / Real.log 2 -
        (2 : ℝ) ^ b * negativeLaplaceForwardTailFirst ((2 : ℝ) ^ b) := by
  have hr : 0 < (2 : ℝ) ^ b := Real.rpow_pos_of_pos (by norm_num) _
  unfold negativeLaplaceRpowFirstResidual
  rw [negativeLaplaceLogFirst_eq_periodic F hF hr,
    Real.log_rpow (by norm_num : (0 : ℝ) < 2),
    Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num)]
  field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne', hr.ne']
  ring

/-- Closed form of the curvature residual, for a Fabius function `F` and every
real `b`: it equals
`-1 / 2 - 1 / log 2 - Ψ'(b) / log 2 + Ψ''(b) / (log 2) ^ 2` minus the scaled
tail `(2 ^ b) ^ 2 * negativeLaplaceForwardTailSecond (2 ^ b)`. -/
theorem negativeLaplaceRpowSecondResidual_eq
    (F : BoundedFabius) (hF : IsFabius F) (b : ℝ) :
    negativeLaplaceRpowSecondResidual F b =
      -1 / 2 - 1 / Real.log 2 - deriv negativeLaplacePsi b / Real.log 2 +
        deriv (deriv negativeLaplacePsi) b / (Real.log 2) ^ 2 -
        ((2 : ℝ) ^ b) ^ 2 *
          negativeLaplaceForwardTailSecond ((2 : ℝ) ^ b) := by
  have hr : 0 < (2 : ℝ) ^ b := Real.rpow_pos_of_pos (by norm_num) _
  unfold negativeLaplaceRpowSecondResidual
  rw [negativeLaplaceLogSecond_eq_periodic F hF hr,
    Real.log_rpow (by norm_num : (0 : ℝ) < 2),
    Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num)]
  field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne', hr.ne']
  ring

/-- Closed form of the cubic residual, for a Fabius function `F` and every
real `b`: it equals `1 + 3 / log 2 + 2 * Ψ'(b) / log 2 -
3 * Ψ''(b) / (log 2) ^ 2 + Ψ'''(b) / (log 2) ^ 3` minus the scaled tail
`(2 ^ b) ^ 3 * negativeLaplaceForwardTailThird (2 ^ b)`. -/
theorem negativeLaplaceRpowThirdResidual_eq
    (F : BoundedFabius) (hF : IsFabius F) (b : ℝ) :
    negativeLaplaceRpowThirdResidual F b =
      1 + 3 / Real.log 2 + 2 * deriv negativeLaplacePsi b / Real.log 2 -
        3 * deriv (deriv negativeLaplacePsi) b / (Real.log 2) ^ 2 +
        negativeLaplacePsiThird b / (Real.log 2) ^ 3 -
        ((2 : ℝ) ^ b) ^ 3 *
          negativeLaplaceForwardTailThird ((2 : ℝ) ^ b) := by
  have hr : 0 < (2 : ℝ) ^ b := Real.rpow_pos_of_pos (by norm_num) _
  unfold negativeLaplaceRpowThirdResidual
  rw [negativeLaplaceLogThird_eq_periodic F hF hr,
    Real.log_rpow (by norm_num : (0 : ℝ) < 2),
    Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num)]
  field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne', hr.ne']
  ring

/-- Rescaling a tail bound.  If `‖g s‖ ≤ C / s ^ (k + 1)` at some
`s ≥ 1`, then `|s ^ k * g s| ≤ C / s`.  The six scaled forward-tail
bounds below are the instances `k = 1, 2, 3`; the constant bound `≤ C`
follows from this one by `div_le_self`. -/
theorem abs_pow_mul_le_div_of_norm_le {g : ℝ → ℝ} {k : ℕ} {C s : ℝ}
    (hs : 1 ≤ s) (h : ‖g s‖ ≤ C / s ^ (k + 1)) :
    |s ^ k * g s| ≤ C / s := by
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have hk : s ^ k ≠ 0 := pow_ne_zero k hs0.ne'
  rw [Real.norm_eq_abs] at h
  rw [abs_mul, abs_of_pos (pow_pos hs0 k)]
  calc
    s ^ k * |g s| ≤ s ^ k * (C / s ^ (k + 1)) := by gcongr
    _ = C / s := by
      rw [pow_succ, mul_div_assoc',
        div_eq_div_iff (mul_ne_zero hk hs0.ne') hs0.ne']
      ring

/-- Sharper scaled first-tail bound:
`|s * negativeLaplaceForwardTailFirst s| ≤ 8 / s` whenever `s ≥ 1`. -/
lemma abs_mul_negativeLaplaceForwardTailFirst_le_div
    {s : ℝ} (hs : 1 ≤ s) :
    |s * negativeLaplaceForwardTailFirst s| ≤ 8 / s := by
  simpa only [pow_one] using
    abs_pow_mul_le_div_of_norm_le (g := negativeLaplaceForwardTailFirst)
      (k := 1) hs (norm_negativeLaplaceForwardTailFirst_le_inv_sq hs)

/-- Scaled first-tail bound: `|s * negativeLaplaceForwardTailFirst s| ≤ 8`
whenever `s ≥ 1`. -/
lemma abs_mul_negativeLaplaceForwardTailFirst_le_eight
    {s : ℝ} (hs : 1 ≤ s) :
    |s * negativeLaplaceForwardTailFirst s| ≤ 8 :=
  (abs_mul_negativeLaplaceForwardTailFirst_le_div hs).trans
    (div_le_self (by norm_num) hs)

/-- Sharper scaled second-tail bound:
`|s ^ 2 * negativeLaplaceForwardTailSecond s| ≤ 48 / s` whenever `s ≥ 1`. -/
lemma abs_sq_mul_negativeLaplaceForwardTailSecond_le_div
    {s : ℝ} (hs : 1 ≤ s) :
    |s ^ 2 * negativeLaplaceForwardTailSecond s| ≤ 48 / s :=
  abs_pow_mul_le_div_of_norm_le (g := negativeLaplaceForwardTailSecond)
    (k := 2) hs (norm_negativeLaplaceForwardTailSecond_le_inv_cube hs)

/-- Scaled second-tail bound:
`|s ^ 2 * negativeLaplaceForwardTailSecond s| ≤ 48` whenever `s ≥ 1`. -/
lemma abs_sq_mul_negativeLaplaceForwardTailSecond_le
    {s : ℝ} (hs : 1 ≤ s) :
    |s ^ 2 * negativeLaplaceForwardTailSecond s| ≤ 48 :=
  (abs_sq_mul_negativeLaplaceForwardTailSecond_le_div hs).trans
    (div_le_self (by norm_num) hs)

/-- Sharper scaled third-tail bound:
`|s ^ 3 * negativeLaplaceForwardTailThird s| ≤ 768 / s` whenever `s ≥ 1`. -/
lemma abs_cube_mul_negativeLaplaceForwardTailThird_le_div
    {s : ℝ} (hs : 1 ≤ s) :
    |s ^ 3 * negativeLaplaceForwardTailThird s| ≤ 768 / s :=
  abs_pow_mul_le_div_of_norm_le (g := negativeLaplaceForwardTailThird)
    (k := 3) hs (norm_negativeLaplaceForwardTailThird_le_inv_fourth hs)

/-- Scaled third-tail bound:
`|s ^ 3 * negativeLaplaceForwardTailThird s| ≤ 768` whenever `s ≥ 1`. -/
lemma abs_cube_mul_negativeLaplaceForwardTailThird_le
    {s : ℝ} (hs : 1 ≤ s) :
    |s ^ 3 * negativeLaplaceForwardTailThird s| ≤ 768 :=
  (abs_cube_mul_negativeLaplaceForwardTailThird_le_div hs).trans
    (div_le_self (by norm_num) hs)

/-- Uniform bound on the first residual over the half-line `b ≥ 0`: for a
Fabius function `F` some nonnegative constant dominates
`|negativeLaplaceRpowFirstResidual F b|` at every nonnegative `b`.  The
constant is an existence claim only.  Consumed by
`FabiusFunction.FabiusSaddleCentralLambert`. -/
theorem exists_bound_abs_negativeLaplaceRpowFirstResidual
    (F : BoundedFabius) (hF : IsFabius F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {b : ℝ}, 0 ≤ b →
      |negativeLaplaceRpowFirstResidual F b| ≤ C := by
  obtain ⟨Cψ, hCψ0, hCψ⟩ := exists_bound_abs_deriv_negativeLaplacePsi
  let C := 1 / 2 + Cψ / Real.log 2 + 8
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC0, ?_⟩
  intro b hb
  rw [negativeLaplaceRpowFirstResidual_eq F hF]
  have hr1 : 1 ≤ (2 : ℝ) ^ b := by
    exact Real.one_le_rpow (by norm_num) hb
  have htail := abs_mul_negativeLaplaceForwardTailFirst_le_eight hr1
  have htri1 :
      |1 / 2 + deriv negativeLaplacePsi b / Real.log 2 -
          (2 : ℝ) ^ b * negativeLaplaceForwardTailFirst ((2 : ℝ) ^ b)| ≤
        |1 / 2 + deriv negativeLaplacePsi b / Real.log 2| +
          |(2 : ℝ) ^ b * negativeLaplaceForwardTailFirst ((2 : ℝ) ^ b)| :=
    abs_sub _ _
  have htri2 := abs_add_le (1 / 2)
    (deriv negativeLaplacePsi b / Real.log 2)
  simp only [abs_div, abs_of_pos hlog] at htri2
  have hpsi := hCψ b
  have hpsiDiv : |deriv negativeLaplacePsi b| / Real.log 2 ≤
      Cψ / Real.log 2 :=
    div_le_div_of_nonneg_right hpsi hlog.le
  dsimp [C]
  norm_num at htri2 ⊢
  calc
    |1 / 2 + deriv negativeLaplacePsi b / Real.log 2 -
        2 ^ b * negativeLaplaceForwardTailFirst (2 ^ b)| ≤
        |1 / 2 + deriv negativeLaplacePsi b / Real.log 2| +
          |2 ^ b * negativeLaplaceForwardTailFirst (2 ^ b)| := htri1
    _ ≤ (1 / 2 + |deriv negativeLaplacePsi b| / Real.log 2) + 8 :=
      add_le_add htri2 htail
    _ ≤ (1 / 2 + Cψ / Real.log 2) + 8 := by
      gcongr
    _ = 1 / 2 + Cψ / Real.log 2 + 8 := by ring

/-- Uniform bound on the curvature residual over the half-line `b ≥ 0`, for a
Fabius function `F`, again through an unnamed nonnegative constant.  Consumed
by `FabiusFunction.FabiusSaddleCentralLambert`. -/
theorem exists_bound_abs_negativeLaplaceRpowSecondResidual
    (F : BoundedFabius) (hF : IsFabius F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {b : ℝ}, 0 ≤ b →
      |negativeLaplaceRpowSecondResidual F b| ≤ C := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_bound_abs_deriv_negativeLaplacePsi
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_bound_abs_secondDeriv_negativeLaplacePsi
  let L := Real.log 2
  let C := 1 / 2 + 1 / L + C₁ / L + C₂ / L ^ 2 + 48
  have hL : 0 < L := by dsimp [L]; positivity
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC0, ?_⟩
  intro b hb
  rw [negativeLaplaceRpowSecondResidual_eq F hF]
  have hr1 : 1 ≤ (2 : ℝ) ^ b := Real.one_le_rpow (by norm_num) hb
  have ht := abs_sq_mul_negativeLaplaceForwardTailSecond_le hr1
  have h1 := hC₁ b
  have h2 := hC₂ b
  have htri :
      |-1 / 2 - 1 / L - deriv negativeLaplacePsi b / L +
          deriv (deriv negativeLaplacePsi) b / L ^ 2 -
          ((2 : ℝ) ^ b) ^ 2 * negativeLaplaceForwardTailSecond ((2 : ℝ) ^ b)| ≤
        |-1 / 2 - 1 / L - deriv negativeLaplacePsi b / L +
          deriv (deriv negativeLaplacePsi) b / L ^ 2| +
        |((2 : ℝ) ^ b) ^ 2 * negativeLaplaceForwardTailSecond ((2 : ℝ) ^ b)| :=
    abs_sub _ _
  have ha := abs_add_le
    (-1 / 2 - 1 / L - deriv negativeLaplacePsi b / L)
    (deriv (deriv negativeLaplacePsi) b / L ^ 2)
  have hb' : |-1 / 2 - 1 / L - deriv negativeLaplacePsi b / L| ≤
      |-1 / 2 - 1 / L| + |deriv negativeLaplacePsi b / L| :=
    abs_sub _ _
  have hbase : |-1 / 2 - 1 / L| = 1 / 2 + 1 / L := by
    have hnonpos : -1 / 2 - 1 / L ≤ 0 := by
      have : 0 < 1 / L := by positivity
      linarith
    rw [abs_of_nonpos hnonpos]
    ring
  have hcore :
      |-1 / 2 - 1 / L - deriv negativeLaplacePsi b / L +
          deriv (deriv negativeLaplacePsi) b / L ^ 2| ≤
        1 / 2 + 1 / L + C₁ / L + C₂ / L ^ 2 := by
    calc
      |-1 / 2 - 1 / L - deriv negativeLaplacePsi b / L +
          deriv (deriv negativeLaplacePsi) b / L ^ 2| ≤
          |-1 / 2 - 1 / L - deriv negativeLaplacePsi b / L| +
            |deriv (deriv negativeLaplacePsi) b / L ^ 2| := ha
      _ ≤ (|-1 / 2 - 1 / L| + |deriv negativeLaplacePsi b / L|) +
          |deriv (deriv negativeLaplacePsi) b / L ^ 2| := by gcongr
      _ = (1 / 2 + 1 / L + |deriv negativeLaplacePsi b| / L) +
          |deriv (deriv negativeLaplacePsi) b| / L ^ 2 := by
        rw [hbase, abs_div, abs_div, abs_pow, abs_of_pos hL]
      _ ≤ 1 / 2 + 1 / L + C₁ / L + C₂ / L ^ 2 := by
        gcongr
  dsimp [C]
  calc
    |-1 / 2 - 1 / L - deriv negativeLaplacePsi b / L +
          deriv (deriv negativeLaplacePsi) b / L ^ 2 -
        (2 ^ b) ^ 2 * negativeLaplaceForwardTailSecond (2 ^ b)| ≤
        |-1 / 2 - 1 / L - deriv negativeLaplacePsi b / L +
          deriv (deriv negativeLaplacePsi) b / L ^ 2| +
        |(2 ^ b) ^ 2 * negativeLaplaceForwardTailSecond (2 ^ b)| := htri
    _ ≤ (1 / 2 + 1 / L + C₁ / L + C₂ / L ^ 2) + 48 :=
      add_le_add hcore ht
    _ = 1 / 2 + 1 / L + C₁ / L + C₂ / L ^ 2 + 48 := by ring

/-- Uniform bound on the cubic residual over the half-line `b ≥ 0`, for a
Fabius function `F`, through an unnamed nonnegative constant.  Consumed by
`FabiusFunction.FabiusSaddleCentralLambert`. -/
theorem exists_bound_abs_negativeLaplaceRpowThirdResidual
    (F : BoundedFabius) (hF : IsFabius F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {b : ℝ}, 0 ≤ b →
      |negativeLaplaceRpowThirdResidual F b| ≤ C := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_bound_abs_deriv_negativeLaplacePsi
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_bound_abs_secondDeriv_negativeLaplacePsi
  obtain ⟨C₃, hC₃0, hC₃⟩ := exists_bound_abs_negativeLaplacePsiThird
  let L := Real.log 2
  let C := 1 + 3 / L + 2 * C₁ / L + 3 * C₂ / L ^ 2 +
    C₃ / L ^ 3 + 768
  have hL : 0 < L := by dsimp [L]; positivity
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC0, ?_⟩
  intro b hb
  rw [negativeLaplaceRpowThirdResidual_eq F hF]
  have hr1 : 1 ≤ (2 : ℝ) ^ b := Real.one_le_rpow (by norm_num) hb
  have ht := abs_cube_mul_negativeLaplaceForwardTailThird_le hr1
  have h1 := hC₁ b
  have h2 := hC₂ b
  have h3 := hC₃ b
  have htri :
      |1 + 3 / L + 2 * deriv negativeLaplacePsi b / L -
          3 * deriv (deriv negativeLaplacePsi) b / L ^ 2 +
          negativeLaplacePsiThird b / L ^ 3 -
          ((2 : ℝ) ^ b) ^ 3 * negativeLaplaceForwardTailThird ((2 : ℝ) ^ b)| ≤
        |1 + 3 / L + 2 * deriv negativeLaplacePsi b / L -
          3 * deriv (deriv negativeLaplacePsi) b / L ^ 2 +
          negativeLaplacePsiThird b / L ^ 3| +
        |((2 : ℝ) ^ b) ^ 3 * negativeLaplaceForwardTailThird ((2 : ℝ) ^ b)| :=
    abs_sub _ _
  have ha := abs_add_le
    (1 + 3 / L + 2 * deriv negativeLaplacePsi b / L -
      3 * deriv (deriv negativeLaplacePsi) b / L ^ 2)
    (negativeLaplacePsiThird b / L ^ 3)
  have hb' :
      |1 + 3 / L + 2 * deriv negativeLaplacePsi b / L -
          3 * deriv (deriv negativeLaplacePsi) b / L ^ 2| ≤
        |1 + 3 / L + 2 * deriv negativeLaplacePsi b / L| +
          |3 * deriv (deriv negativeLaplacePsi) b / L ^ 2| :=
    abs_sub _ _
  have hc := abs_add_le (1 + 3 / L) (2 * deriv negativeLaplacePsi b / L)
  have hbase : |1 + 3 / L| = 1 + 3 / L := by
    rw [abs_of_pos]
    positivity
  have hcore :
      |1 + 3 / L + 2 * deriv negativeLaplacePsi b / L -
          3 * deriv (deriv negativeLaplacePsi) b / L ^ 2 +
          negativeLaplacePsiThird b / L ^ 3| ≤
        1 + 3 / L + 2 * C₁ / L + 3 * C₂ / L ^ 2 + C₃ / L ^ 3 := by
    calc
      |1 + 3 / L + 2 * deriv negativeLaplacePsi b / L -
          3 * deriv (deriv negativeLaplacePsi) b / L ^ 2 +
          negativeLaplacePsiThird b / L ^ 3| ≤
          |1 + 3 / L + 2 * deriv negativeLaplacePsi b / L -
            3 * deriv (deriv negativeLaplacePsi) b / L ^ 2| +
            |negativeLaplacePsiThird b / L ^ 3| := ha
      _ ≤ (|1 + 3 / L + 2 * deriv negativeLaplacePsi b / L| +
          |3 * deriv (deriv negativeLaplacePsi) b / L ^ 2|) +
          |negativeLaplacePsiThird b / L ^ 3| := by gcongr
      _ ≤ ((|1 + 3 / L| + |2 * deriv negativeLaplacePsi b / L|) +
          |3 * deriv (deriv negativeLaplacePsi) b / L ^ 2|) +
          |negativeLaplacePsiThird b / L ^ 3| := by gcongr
      _ = ((1 + 3 / L + 2 * |deriv negativeLaplacePsi b| / L) +
          3 * |deriv (deriv negativeLaplacePsi) b| / L ^ 2) +
          |negativeLaplacePsiThird b| / L ^ 3 := by
        rw [hbase]
        simp only [abs_div, abs_mul, abs_pow, abs_of_pos hL]
        norm_num
      _ ≤ 1 + 3 / L + 2 * C₁ / L + 3 * C₂ / L ^ 2 + C₃ / L ^ 3 := by
        gcongr
  dsimp [C]
  calc
    |1 + 3 / L + 2 * deriv negativeLaplacePsi b / L -
          3 * deriv (deriv negativeLaplacePsi) b / L ^ 2 +
          negativeLaplacePsiThird b / L ^ 3 -
        (2 ^ b) ^ 3 * negativeLaplaceForwardTailThird (2 ^ b)| ≤
        |1 + 3 / L + 2 * deriv negativeLaplacePsi b / L -
          3 * deriv (deriv negativeLaplacePsi) b / L ^ 2 +
          negativeLaplacePsiThird b / L ^ 3| +
        |(2 ^ b) ^ 3 * negativeLaplaceForwardTailThird (2 ^ b)| := htri
    _ ≤ (1 + 3 / L + 2 * C₁ / L + 3 * C₂ / L ^ 2 + C₃ / L ^ 3) +
        768 := add_le_add hcore ht
    _ = 1 + 3 / L + 2 * C₁ / L + 3 * C₂ / L ^ 2 + C₃ / L ^ 3 +
        768 := by ring

end Fabius
