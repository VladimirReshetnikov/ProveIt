import FabiusFunction.NegativeLaplaceVerticalSmooth
import FabiusFunction.NegativeLaplaceVerticalFourthBound
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Uniform all-order vertical Laplace bounds

The one-factor dyadic dilation formula gives an additive recurrence for the
first derivative of the branch-safe vertical logarithm.  We holomorphically
continue that one-factor derivative in the vertical parameter and apply
Cauchy's estimate on disks of radius `1/2`.  This gives, for every order `m`,
the explicit scale-independent increment bound

`‖D^m K₁(s, θ)‖ ≤ m! * 5 / (1/2)^m` for `s ≥ 1`.

A second holomorphic continuation controls the compact base
`1 ≤ r ≤ 2`, `|θ| ≤ 1`.  Iterating the exact dilation recurrence then proves
that every positive-order vertical logarithmic derivative is `O(b + 1)` at
`r = 2^b` for every `b ≥ 0`, uniformly throughout the fixed strip.  A
compatibility corollary recovers the original `O(b)` form for `b ≥ 1`, and the
final theorem exports that form directly in the lower-Lambert saddle
coordinates.
-/

set_option autoImplicit false

open Filter Set Metric
open scoped Topology Interval

namespace Fabius

/-- Real and complex iterated derivatives agree along the real embedding: if
`f : ℂ → ℂ` is complex differentiable on an open set `U` and `(x : ℂ)` lies
in `U`, then the `n`-th iterated derivative over `ℝ` of `fun t : ℝ => f t`
at `x` equals the `n`-th iterated derivative over `ℂ` of `f` at `(x : ℂ)`.
Both Cauchy estimates of this file are transferred back to the real vertical
parameter with it, and it is also the transfer step used by
`FabiusFunction.NegativeLaplaceVerticalOrdinaryJets`. -/
lemma iteratedDeriv_comp_ofReal_eq_of_differentiableOn
    (f : ℂ → ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (n : ℕ) (x : ℝ) (hx : (x : ℂ) ∈ U) :
    iteratedDeriv n (fun t : ℝ ↦ f t) x = iteratedDeriv n f x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have hmem : ∀ᶠ t : ℝ in nhds x, (t : ℂ) ∈ U :=
        (Complex.continuous_ofReal.tendsto x) (hU.mem_nhds hx)
      have heq : iteratedDeriv n (fun t : ℝ ↦ f t) =ᶠ[nhds x]
          fun t : ℝ ↦ iteratedDeriv n f t := by
        filter_upwards [hmem] with t ht
        exact ih t ht
      rw [heq.deriv_eq]
      have han : AnalyticAt ℂ (iteratedDeriv n f) x := by
        rw [iteratedDeriv_eq_iterate]
        exact ((hf.analyticOnNhd hU).iterated_deriv n) x hx
      exact han.differentiableAt.hasDerivAt.comp_ofReal.deriv

/-- Continuation of `negativeLaplaceVerticalKernelLogFirst s` in the vertical
parameter: the real `θ` is replaced by a complex `z`, while the scale `s`
and the prefactor `s * I` are unchanged.  The restriction to real arguments
is definitionally the real kernel, as recorded by
`negativeLaplaceVerticalKernelLogFirstComplex_ofReal`; holomorphy on the
tilted half-plane `0 < (s * (1 + z * I)).re` is proved separately below. -/
noncomputable def negativeLaplaceVerticalKernelLogFirstComplex
    (s : ℝ) (z : ℂ) : ℂ :=
  ((s : ℂ) * Complex.I) * negativeLaplaceComplexKernelFirst
    ((s : ℂ) * (1 + z * Complex.I))

/-- Restricting the complex vertical kernel derivative to a real parameter
recovers the real vertical kernel derivative. -/
@[simp] theorem negativeLaplaceVerticalKernelLogFirstComplex_ofReal
    (s θ : ℝ) :
    negativeLaplaceVerticalKernelLogFirstComplex s θ =
      negativeLaplaceVerticalKernelLogFirst s θ := rfl

private lemma vertical_complex_arg_re (s : ℝ) (z : ℂ) :
    ((s : ℂ) * (1 + z * Complex.I)).re = s * (1 - z.im) := by
  simp [mul_add]
  ring

private lemma im_le_of_mem_closedBall_real_half
    {θ : ℝ} {z : ℂ} (hz : z ∈ closedBall (θ : ℂ) (1 / 2 : ℝ)) :
    z.im ≤ 1 / 2 := by
  have him : |z.im - (θ : ℂ).im| ≤ ‖z - (θ : ℂ)‖ :=
    Complex.abs_im_le_norm (z - (θ : ℂ))
  simp only [Complex.ofReal_im, sub_zero] at him
  have hnorm : ‖z - (θ : ℂ)‖ ≤ 1 / 2 := by
    simpa only [mem_closedBall, dist_eq_norm] using hz
  linarith [le_abs_self z.im]

private lemma abs_im_le_of_mem_closedBall_real_half
    {θ : ℝ} {z : ℂ} (hz : z ∈ closedBall (θ : ℂ) (1 / 2 : ℝ)) :
    |z.im| ≤ 1 / 2 := by
  have him : |z.im - (θ : ℂ).im| ≤ ‖z - (θ : ℂ)‖ :=
    Complex.abs_im_le_norm (z - (θ : ℂ))
  simp only [Complex.ofReal_im, sub_zero] at him
  exact him.trans (by simpa only [mem_closedBall, dist_eq_norm] using hz)

private lemma vertical_complex_arg_re_ge_half
    {s θ : ℝ} (hs : 1 ≤ s) {z : ℂ}
    (hz : z ∈ closedBall (θ : ℂ) (1 / 2 : ℝ)) :
    s / 2 ≤ ((s : ℂ) * (1 + z * Complex.I)).re := by
  rw [vertical_complex_arg_re]
  have him := im_le_of_mem_closedBall_real_half hz
  nlinarith

private lemma norm_exp_neg_vertical_complex_arg_le_two_thirds
    {s θ : ℝ} (hs : 1 ≤ s) {z : ℂ}
    (hz : z ∈ closedBall (θ : ℂ) (1 / 2 : ℝ)) :
    ‖Complex.exp (-((s : ℂ) * (1 + z * Complex.I)))‖ ≤ 2 / 3 := by
  rw [Complex.norm_exp]
  have hre := vertical_complex_arg_re_ge_half hs hz
  simp only [Complex.neg_re]
  have hmono : Real.exp
      (-((s : ℂ) * (1 + z * Complex.I)).re) ≤ Real.exp (-(s / 2)) :=
    Real.exp_le_exp.mpr (by linarith)
  calc
    Real.exp (-((s : ℂ) * (1 + z * Complex.I)).re) ≤
        Real.exp (-(s / 2)) := hmono
    _ ≤ 2 / 3 := by
      rw [Real.exp_neg]
      have hexp : (3 / 2 : ℝ) ≤ Real.exp (s / 2) := by
        calc
          (3 / 2 : ℝ) ≤ s / 2 + 1 := by linarith
          _ ≤ Real.exp (s / 2) := Real.add_one_le_exp _
      rw [← one_mul (Real.exp (s / 2))⁻¹,
        mul_inv_le_iff₀ (Real.exp_pos (s / 2))]
      nlinarith

private lemma s_mul_norm_exp_neg_vertical_complex_arg_le_one
    {s θ : ℝ} (hs : 1 ≤ s) {z : ℂ}
    (hz : z ∈ closedBall (θ : ℂ) (1 / 2 : ℝ)) :
    s * ‖Complex.exp (-((s : ℂ) * (1 + z * Complex.I)))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have hre := vertical_complex_arg_re_ge_half hs hz
  simp only [Complex.neg_re]
  have hmono : Real.exp
      (-((s : ℂ) * (1 + z * Complex.I)).re) ≤ Real.exp (-(s / 2)) :=
    Real.exp_le_exp.mpr (by linarith)
  calc
    s * Real.exp (-((s : ℂ) * (1 + z * Complex.I)).re) ≤
        s * Real.exp (-(s / 2)) :=
      mul_le_mul_of_nonneg_left hmono (by linarith)
    _ = 2 * ((s / 2) * Real.exp (-(s / 2))) := by ring
    _ ≤ 1 := by
      have h := Real.mul_exp_neg_le_exp_neg_one (s / 2)
      nlinarith [Real.exp_neg_one_lt_half]

private theorem norm_negativeLaplaceVerticalKernelLogFirstComplex_le
    {s θ : ℝ} (hs : 1 ≤ s) {z : ℂ}
    (hz : z ∈ closedBall (θ : ℂ) (1 / 2 : ℝ)) :
    ‖negativeLaplaceVerticalKernelLogFirstComplex s z‖ ≤ 5 := by
  let w : ℂ := (s : ℂ) * (1 + z * Complex.I)
  let t : ℂ := Complex.exp (-w)
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have hwre : s / 2 ≤ w.re := vertical_complex_arg_re_ge_half hs hz
  have hwNorm : s / 2 ≤ ‖w‖ := by
    exact hwre.trans (Complex.re_le_norm w)
  have hwNorm0 : 0 < ‖w‖ := (by positivity : (0 : ℝ) < s / 2).trans_le hwNorm
  have ht : ‖t‖ ≤ 2 / 3 := by
    dsimp [t, w]
    exact norm_exp_neg_vertical_complex_arg_le_two_thirds hs hz
  have hden : 1 / 3 ≤ ‖1 - t‖ := by
    calc
      1 / 3 ≤ ‖(1 : ℂ)‖ - ‖t‖ := by norm_num; linarith
      _ ≤ ‖(1 : ℂ) - t‖ := norm_sub_norm_le _ _
  have hden0 : 0 < ‖1 - t‖ := (by norm_num : (0 : ℝ) < 1 / 3).trans_le hden
  have hfrac : s * ‖t / (1 - t)‖ ≤ 3 := by
    rw [norm_div, ← mul_div_assoc, div_le_iff₀ hden0]
    calc
      s * ‖t‖ ≤ 1 := by
        dsimp [t, w]
        exact s_mul_norm_exp_neg_vertical_complex_arg_le_one hs hz
      _ ≤ 3 * ‖1 - t‖ := by nlinarith
  have hinv : s * ‖(1 : ℂ) / w‖ ≤ 2 := by
    rw [norm_div, norm_one, one_div, ← div_eq_mul_inv,
      div_le_iff₀ hwNorm0]
    nlinarith
  unfold negativeLaplaceVerticalKernelLogFirstComplex
    negativeLaplaceComplexKernelFirst
  change ‖((s : ℂ) * Complex.I) * (t / (1 - t) - 1 / w)‖ ≤ 5
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hs0, Complex.norm_I, mul_one]
  calc
    s * ‖t / (1 - t) - 1 / w‖ ≤
        s * (‖t / (1 - t)‖ + ‖(1 : ℂ) / w‖) := by
      gcongr
      exact norm_sub_le _ _
    _ = s * ‖t / (1 - t)‖ + s * ‖(1 : ℂ) / w‖ := by ring
    _ ≤ 3 + 2 := add_le_add hfrac hinv
    _ = 5 := by norm_num

private theorem differentiableOn_negativeLaplaceVerticalKernelLogFirstComplex
    {s : ℝ} :
    DifferentiableOn ℂ (negativeLaplaceVerticalKernelLogFirstComplex s)
      {z : ℂ | 0 < ((s : ℂ) * (1 + z * Complex.I)).re} := by
  intro z hz
  have harg : HasDerivAt
      (fun w : ℂ => (s : ℂ) * (1 + w * Complex.I))
      ((s : ℂ) * Complex.I) z := by
    simpa only [id_eq, one_mul] using
      (((hasDerivAt_id z).mul_const Complex.I).const_add 1).const_mul (s : ℂ)
  have hkernel := (negativeLaplaceComplexKernelFirst_hasDerivAt hz).comp z harg
  change DifferentiableWithinAt ℂ
    (fun y : ℂ => ((s : ℂ) * Complex.I) * negativeLaplaceComplexKernelFirst
      ((s : ℂ) * (1 + y * Complex.I))) _ z
  have hd : DifferentiableAt ℂ
      (fun y : ℂ => ((s : ℂ) * Complex.I) * negativeLaplaceComplexKernelFirst
        ((s : ℂ) * (1 + y * Complex.I))) z := by
    simpa only [Function.comp_apply] using
      (hkernel.const_mul ((s : ℂ) * Complex.I)).differentiableAt
  exact hd.differentiableWithinAt

/-- The `m`-th derivative of the one-factor logarithmic increment is bounded
uniformly in the vertical parameter `theta`, at all scales `s >= 1`.  The
bound holds for *every* real `theta`, not only on a bounded strip: the
constant does not depend on `theta` at all, because the disk of radius `1/2`
around `theta` stays inside the half plane `Re > 0` uniformly.  Cauchy's
estimate on that disk gives the explicit constant `5 * m! * 2^m`, written
below as `m! * 5 / (1/2)^m`. -/
theorem norm_iteratedDeriv_negativeLaplaceVerticalKernelLogFirst_le
    (m : ℕ) {s θ : ℝ} (hs : 1 ≤ s) :
    ‖iteratedDeriv m (negativeLaplaceVerticalKernelLogFirst s) θ‖ ≤
      m.factorial * 5 / (1 / 2 : ℝ) ^ m := by
  let U : Set ℂ :=
    {z : ℂ | 0 < ((s : ℂ) * (1 + z * Complex.I)).re}
  have hU : IsOpen U := by
    dsimp [U]
    exact isOpen_lt continuous_const (by fun_prop)
  have hdiff : DifferentiableOn ℂ
      (negativeLaplaceVerticalKernelLogFirstComplex s) U :=
    differentiableOn_negativeLaplaceVerticalKernelLogFirstComplex
  have hclosed : closedBall (θ : ℂ) (1 / 2 : ℝ) ⊆ U := by
    intro z hz
    exact (by
      have := vertical_complex_arg_re_ge_half hs hz
      linarith : 0 < ((s : ℂ) * (1 + z * Complex.I)).re)
  have hf : DiffContOnCl ℂ
      (negativeLaplaceVerticalKernelLogFirstComplex s)
      (ball (θ : ℂ) (1 / 2 : ℝ)) :=
    hdiff.diffContOnCl_ball hclosed
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    m (by norm_num : (0 : ℝ) < 1 / 2) hf (fun z hz =>
      norm_negativeLaplaceVerticalKernelLogFirstComplex_le hs
        (sphere_subset_closedBall hz))
  have hθU : (θ : ℂ) ∈ U := hclosed (mem_closedBall_self (by norm_num))
  have heq : negativeLaplaceVerticalKernelLogFirst s =
      fun t : ℝ => negativeLaplaceVerticalKernelLogFirstComplex s t := rfl
  rw [heq]
  rw [iteratedDeriv_comp_ofReal_eq_of_differentiableOn
    (negativeLaplaceVerticalKernelLogFirstComplex s) hU hdiff m θ hθU]
  exact hcauchy

/-- For `r > 0` the first vertical logarithmic derivative
`negativeLaplaceVerticalLogFirst F r` is `C^∞` in the vertical parameter.
The exponent `↑(⊤ : ℕ∞)` is the `C^∞` exponent of `WithTop ℕ∞`, not the
analytic exponent.  Assumes `IsFabius F`. -/
theorem contDiff_negativeLaplaceVerticalLogFirst_infty
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (negativeLaplaceVerticalLogFirst F r) := by
  have hderiv : deriv (negativeLaplaceVerticalLog F r) =
      negativeLaplaceVerticalLogFirst F r := by
    funext θ
    exact (negativeLaplaceVerticalLog_hasDerivAt_cumulant F hF hr θ).deriv
  have h := contDiff_iteratedDeriv_negativeLaplaceVerticalLog_infty F hF hr 1
  simpa only [iteratedDeriv_succ', iteratedDeriv_zero, hderiv] using h

/-- For `s > 0` the first vertical kernel is `C^∞` in the vertical parameter.
The exponent `↑(⊤ : ℕ∞)` is the `C^∞` exponent of `WithTop ℕ∞`, not the
analytic exponent.  The conclusion does not mention `F`, yet the statement
still takes a `BoundedFabius` together with `IsFabius F`: the proof rewrites
the kernel as the difference of the first vertical logarithmic derivatives
at `2 * s` and at `s`. -/
theorem contDiff_negativeLaplaceVerticalKernelLogFirst_infty
    (F : BoundedFabius) (hF : IsFabius F) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (negativeLaplaceVerticalKernelLogFirst s) := by
  have heq : negativeLaplaceVerticalKernelLogFirst s =
      negativeLaplaceVerticalLogFirst F (2 * s) -
        negativeLaplaceVerticalLogFirst F s := by
    funext θ
    rw [Pi.sub_apply, negativeLaplaceVerticalLogFirst_two_mul F hF hs θ]
    abel
  rw [heq]
  exact (contDiff_negativeLaplaceVerticalLogFirst_infty F hF (by positivity)).sub
    (contDiff_negativeLaplaceVerticalLogFirst_infty F hF hs)

/-- Every positive-order vertical logarithmic derivative satisfies the exact
one-factor dyadic recurrence.  The index is written as `m + 1` because the
uniform analytic increment is the first logarithmic derivative. -/
theorem iteratedDeriv_negativeLaplaceVerticalLog_succ_two_mul
    (F : BoundedFabius) (hF : IsFabius F) (m : ℕ)
    {s : ℝ} (hs : 0 < s) (θ : ℝ) :
    iteratedDeriv (m + 1) (negativeLaplaceVerticalLog F (2 * s)) θ =
      iteratedDeriv m (negativeLaplaceVerticalKernelLogFirst s) θ +
        iteratedDeriv (m + 1) (negativeLaplaceVerticalLog F s) θ := by
  have hderiv (r : ℝ) (hr : 0 < r) :
      deriv (negativeLaplaceVerticalLog F r) =
        negativeLaplaceVerticalLogFirst F r := by
    funext t
    exact (negativeLaplaceVerticalLog_hasDerivAt_cumulant F hF hr t).deriv
  rw [iteratedDeriv_succ', iteratedDeriv_succ', hderiv (2 * s) (by positivity),
    hderiv s hs]
  have heq : negativeLaplaceVerticalLogFirst F (2 * s) =
      negativeLaplaceVerticalKernelLogFirst s +
        negativeLaplaceVerticalLogFirst F s := by
    funext t
    exact negativeLaplaceVerticalLogFirst_two_mul F hF hs t
  rw [heq]
  exact iteratedDeriv_add
    ((contDiff_negativeLaplaceVerticalKernelLogFirst_infty F hF hs).contDiffAt.of_le
      (by exact_mod_cast (show (m : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)))
    ((contDiff_negativeLaplaceVerticalLogFirst_infty F hF hs).contDiffAt.of_le
      (by exact_mod_cast (show (m : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)))

/-- Holomorphic continuation in the vertical parameter of the first
logarithmic derivative. -/
noncomputable def negativeLaplaceVerticalLogFirstComplex
    (F : BoundedFabius) (r : ℝ) (z : ℂ) : ℂ :=
  (-((r : ℂ) * Complex.I)) *
    (iteratedDeriv 1 (complexGeneratingFunction F)
        (-((r : ℂ) * (1 + z * Complex.I))) /
      complexGeneratingFunction F (-((r : ℂ) * (1 + z * Complex.I))))

/-- Restricting the complexified first vertical logarithmic derivative to the
real axis recovers its real counterpart. -/
@[simp] theorem negativeLaplaceVerticalLogFirstComplex_ofReal
    (F : BoundedFabius) (r θ : ℝ) :
    negativeLaplaceVerticalLogFirstComplex F r θ =
      negativeLaplaceVerticalLogFirst F r θ := by
  rw [negativeLaplaceVerticalLogFirst_apply]
  unfold negativeLaplaceVerticalLogFirstComplex
    negativeLaplaceVerticalCumulantFirst
    normalizedNegativeLaplaceVerticalMoment negativeLaplaceVerticalMoment
  simp only [iteratedDeriv_zero]

private theorem differentiableOn_negativeLaplaceVerticalLogFirstComplex
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} :
    DifferentiableOn ℂ (negativeLaplaceVerticalLogFirstComplex F r)
      {z : ℂ | 0 < ((r : ℂ) * (1 + z * Complex.I)).re} := by
  intro z hz
  have harg : HasDerivAt
      (fun w : ℂ => -((r : ℂ) * (1 + w * Complex.I)))
      (-((r : ℂ) * Complex.I)) z := by
    have h : HasDerivAt
        (fun w : ℂ => -(r : ℂ) + w * (-((r : ℂ) * Complex.I)))
        (-((r : ℂ) * Complex.I)) z := by
      simpa only [id_eq, one_mul] using
        ((hasDerivAt_id z).mul_const (-((r : ℂ) * Complex.I))).const_add (-(r : ℂ))
    apply h.congr_of_eventuallyEq
    filter_upwards with y
    ring
  have hsmooth : ContDiff ℂ (↑(⊤ : ℕ∞))
      (iteratedDeriv 1 (complexGeneratingFunction F)) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv (𝕜 := ℂ) 1
      ((contDiff_complexGeneratingFunction F hF).of_le (by simp))
  have hnum := ((hsmooth.differentiable (by simp)
    (-((r : ℂ) * (1 + z * Complex.I)))).hasDerivAt).comp z harg
  have hden := ((differentiable_complexGeneratingFunction F hF).differentiableAt.hasDerivAt).comp
    z harg
  have hdenNe : complexGeneratingFunction F
      (-((r : ℂ) * (1 + z * Complex.I))) ≠ 0 :=
    complexGeneratingFunction_neg_ne_zero F hF hz
  change DifferentiableWithinAt ℂ
    (fun y : ℂ => (-((r : ℂ) * Complex.I)) *
      (iteratedDeriv 1 (complexGeneratingFunction F)
          (-((r : ℂ) * (1 + y * Complex.I))) /
        complexGeneratingFunction F (-((r : ℂ) * (1 + y * Complex.I))))) _ z
  exact ((hnum.div hden hdenNe).const_mul
    (-((r : ℂ) * Complex.I))).differentiableAt.differentiableWithinAt

private theorem continuousOn_negativeLaplaceVerticalLogFirstComplex_base
    (F : BoundedFabius) (hF : IsFabius F) :
    ContinuousOn
      (fun p : ℝ × ℂ => negativeLaplaceVerticalLogFirstComplex F p.1 p.2)
      (Icc (1 : ℝ) 2 ×ˢ
        (closedBall (0 : ℂ) 2 ∩ {z : ℂ | z.im ∈ Icc (-1 / 2 : ℝ) (1 / 2)})) := by
  let arg : ℝ × ℂ → ℂ := fun p =>
    -((p.1 : ℂ) * (1 + p.2 * Complex.I))
  have harg : Continuous arg := by
    dsimp [arg]
    fun_prop
  have hsmooth : ContDiff ℂ (↑(⊤ : ℕ∞))
      (iteratedDeriv 1 (complexGeneratingFunction F)) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv (𝕜 := ℂ) 1
      ((contDiff_complexGeneratingFunction F hF).of_le (by simp))
  have hnum : Continuous (fun p : ℝ × ℂ =>
      iteratedDeriv 1 (complexGeneratingFunction F) (arg p)) :=
    hsmooth.continuous.comp harg
  have hden : Continuous (fun p : ℝ × ℂ =>
      complexGeneratingFunction F (arg p)) :=
    (differentiable_complexGeneratingFunction F hF).continuous.comp harg
  have hscale : Continuous (fun p : ℝ × ℂ =>
      (-((p.1 : ℂ) * Complex.I))) := by fun_prop
  unfold negativeLaplaceVerticalLogFirstComplex
  exact hscale.continuousOn.mul (hnum.continuousOn.div hden.continuousOn (by
    intro p hp
    apply complexGeneratingFunction_neg_ne_zero F hF
    rw [vertical_complex_arg_re]
    have hr := hp.1.1
    have him := hp.2.2.2
    nlinarith))

/-- Compact-base control for every positive vertical derivative order. -/
theorem exists_norm_iteratedDeriv_negativeLaplaceVerticalLog_base
    (F : BoundedFabius) (hF : IsFabius F) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {r θ : ℝ}, 1 ≤ r → r ≤ 2 → |θ| ≤ 1 →
      ‖iteratedDeriv (m + 1) (negativeLaplaceVerticalLog F r) θ‖ ≤ A := by
  let Z : Set ℂ := closedBall (0 : ℂ) 2 ∩
    {z : ℂ | z.im ∈ Icc (-1 / 2 : ℝ) (1 / 2)}
  let K : Set (ℝ × ℂ) := Icc (1 : ℝ) 2 ×ˢ Z
  have hZcompact : IsCompact Z := by
    dsimp [Z]
    exact (isCompact_closedBall (0 : ℂ) 2).inter_right
      (isClosed_Icc.preimage Complex.continuous_im)
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact isCompact_Icc.prod hZcompact
  have hcont : ContinuousOn
      (fun p : ℝ × ℂ => ‖negativeLaplaceVerticalLogFirstComplex F p.1 p.2‖) K := by
    exact (continuousOn_negativeLaplaceVerticalLogFirstComplex_base F hF).norm
  obtain ⟨B₀, hB₀⟩ := bddAbove_def.mp (hKcompact.bddAbove_image hcont)
  let B : ℝ := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hbound : ∀ p ∈ K,
      ‖negativeLaplaceVerticalLogFirstComplex F p.1 p.2‖ ≤ B := by
    intro p hp
    exact (hB₀ _ ⟨p, hp, rfl⟩).trans (le_max_left _ _)
  let A : ℝ := m.factorial * B / (1 / 2 : ℝ) ^ m
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro r θ hr1 hr2 hθ
  let U : Set ℂ :=
    {z : ℂ | 0 < ((r : ℂ) * (1 + z * Complex.I)).re}
  have hU : IsOpen U := by
    dsimp [U]
    exact isOpen_lt continuous_const (by fun_prop)
  have hdiff : DifferentiableOn ℂ
      (negativeLaplaceVerticalLogFirstComplex F r) U :=
    differentiableOn_negativeLaplaceVerticalLogFirstComplex F hF
  have hclosed : closedBall (θ : ℂ) (1 / 2 : ℝ) ⊆ U := by
    intro z hz
    exact (by
      have := vertical_complex_arg_re_ge_half hr1 hz
      linarith : 0 < ((r : ℂ) * (1 + z * Complex.I)).re)
  have hf : DiffContOnCl ℂ (negativeLaplaceVerticalLogFirstComplex F r)
      (ball (θ : ℂ) (1 / 2 : ℝ)) :=
    hdiff.diffContOnCl_ball hclosed
  have hsphere : ∀ z ∈ sphere (θ : ℂ) (1 / 2 : ℝ),
      ‖negativeLaplaceVerticalLogFirstComplex F r z‖ ≤ B := by
    intro z hz
    apply hbound (r, z)
    have hzclosed : z ∈ closedBall (θ : ℂ) (1 / 2 : ℝ) :=
      sphere_subset_closedBall hz
    have hznorm : ‖z‖ ≤ 2 := by
      calc
        ‖z‖ = ‖(z - (θ : ℂ)) + (θ : ℂ)‖ := by ring_nf
        _ ≤ ‖z - (θ : ℂ)‖ + ‖(θ : ℂ)‖ := norm_add_le _ _
        _ ≤ 1 / 2 + |θ| := by
          gcongr
          · simpa only [mem_closedBall, dist_eq_norm] using hzclosed
          · simp
        _ ≤ 2 := by linarith
    have him := abs_im_le_of_mem_closedBall_real_half hzclosed
    exact ⟨⟨hr1, hr2⟩, ⟨by
      simpa only [mem_closedBall, dist_zero_right] using hznorm,
      (show z.im ∈ Icc (-1 / 2 : ℝ) (1 / 2) by
        constructor <;> linarith [((abs_le.mp him).1), ((abs_le.mp him).2)])⟩⟩
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    m (by norm_num : (0 : ℝ) < 1 / 2) hf hsphere
  have hθU : (θ : ℂ) ∈ U := hclosed (mem_closedBall_self (by norm_num))
  have heq : negativeLaplaceVerticalLogFirst F r =
      fun t : ℝ => negativeLaplaceVerticalLogFirstComplex F r t := by
    funext t
    exact (negativeLaplaceVerticalLogFirstComplex_ofReal F r t).symm
  have hreal : ‖iteratedDeriv m (negativeLaplaceVerticalLogFirst F r) θ‖ ≤ A := by
    rw [heq, iteratedDeriv_comp_ofReal_eq_of_differentiableOn
      (negativeLaplaceVerticalLogFirstComplex F r) hU hdiff m θ hθU]
    exact hcauchy
  rw [iteratedDeriv_succ']
  have hderiv : deriv (negativeLaplaceVerticalLog F r) =
      negativeLaplaceVerticalLogFirst F r := by
    funext t
    exact (negativeLaplaceVerticalLog_hasDerivAt_cumulant F hF
      (zero_lt_one.trans_le hr1) t).deriv
  rw [hderiv]
  exact hreal

/-- Dyadic iteration of the all-order one-factor recurrence. -/
theorem exists_norm_iteratedDeriv_negativeLaplaceVerticalLog_le_dyadicScales
    (F : BoundedFabius) (hF : IsFabius F) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (k : ℕ) {r θ : ℝ},
      1 ≤ r → r ≤ (2 : ℝ) ^ (k + 1) → |θ| ≤ 1 →
      ‖iteratedDeriv (m + 1) (negativeLaplaceVerticalLog F r) θ‖ ≤
        A + (k + 1 : ℕ) *
          (m.factorial * 5 / (1 / 2 : ℝ) ^ m) := by
  obtain ⟨A, hA, hbase⟩ :=
    exists_norm_iteratedDeriv_negativeLaplaceVerticalLog_base F hF m
  let D : ℝ := m.factorial * 5 / (1 / 2 : ℝ) ^ m
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨A, hA, ?_⟩
  intro k
  induction k with
  | zero =>
      intro r θ hr1 hr2 hθ
      norm_num at hr2
      exact (hbase hr1 hr2 hθ).trans
        (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hD))
  | succ k ih =>
      intro r θ hr1 hrUpper hθ
      by_cases hr2 : r ≤ 2
      · exact (hbase hr1 hr2 hθ).trans
          (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hD))
      · let s : ℝ := r / 2
        have hs1 : 1 ≤ s := by dsimp [s]; linarith
        have hsUpper : s ≤ (2 : ℝ) ^ (k + 1) := by
          dsimp [s]
          rw [show k + 1 + 1 = (k + 1) + 1 by omega, pow_succ] at hrUpper
          nlinarith
        have hi := ih hs1 hsUpper hθ
        have hk := norm_iteratedDeriv_negativeLaplaceVerticalKernelLogFirst_le
          m hs1 (θ := θ)
        have hs0 : 0 < s := zero_lt_one.trans_le hs1
        have hrs : r = 2 * s := by dsimp [s]; ring
        rw [hrs, iteratedDeriv_negativeLaplaceVerticalLog_succ_two_mul
          F hF m hs0 θ]
        calc
          ‖iteratedDeriv m (negativeLaplaceVerticalKernelLogFirst s) θ +
              iteratedDeriv (m + 1) (negativeLaplaceVerticalLog F s) θ‖ ≤
              ‖iteratedDeriv m (negativeLaplaceVerticalKernelLogFirst s) θ‖ +
                ‖iteratedDeriv (m + 1) (negativeLaplaceVerticalLog F s) θ‖ :=
            norm_add_le _ _
          _ ≤ D + (A + (k + 1 : ℕ) * D) := add_le_add hk hi
          _ = A + (k + 1 + 1 : ℕ) * D := by push_cast; ring

/-- Uniform all-order `O(b + 1)` control on the dyadic radius `r = 2^b`, valid
from the natural endpoint `b = 0`.  The additive one accounts for the compact
base radius `r = 1`; the theorem is quantified in the derivative order, so no
order-dependent regularity assumptions remain. -/
theorem exists_norm_iteratedDeriv_negativeLaplaceVerticalLog_rpow_le_add_one
    (F : BoundedFabius) (hF : IsFabius F) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {b θ : ℝ}, 0 ≤ b → |θ| ≤ 1 →
      ‖iteratedDeriv (m + 1)
        (negativeLaplaceVerticalLog F ((2 : ℝ) ^ b)) θ‖ ≤ C * (b + 1) := by
  obtain ⟨A, hA, hscale⟩ :=
    exists_norm_iteratedDeriv_negativeLaplaceVerticalLog_le_dyadicScales F hF m
  let D : ℝ := m.factorial * 5 / (1 / 2 : ℝ) ^ m
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let C : ℝ := A + 2 * D
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro b θ hb0 hθ
  let k : ℕ := ⌈b⌉₊
  have hr1 : 1 ≤ (2 : ℝ) ^ b :=
    Real.one_le_rpow (by norm_num) hb0
  have hbceil : b ≤ (k : ℝ) := by
    dsimp [k]
    exact Nat.le_ceil b
  have hbUpper : b ≤ (k + 1 : ℕ) :=
    hbceil.trans (by push_cast; linarith)
  have hrUpperRpow : (2 : ℝ) ^ b ≤ (2 : ℝ) ^ ((k + 1 : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hbUpper
  have hrUpper : (2 : ℝ) ^ b ≤ (2 : ℝ) ^ (k + 1) := by
    simpa only [Real.rpow_natCast] using hrUpperRpow
  have hmain := hscale k hr1 hrUpper hθ
  have hkCeil : (k : ℝ) < b + 1 := by
    dsimp [k]
    exact Nat.ceil_lt_add_one hb0
  calc
    ‖iteratedDeriv (m + 1)
        (negativeLaplaceVerticalLog F ((2 : ℝ) ^ b)) θ‖ ≤
        A + (k + 1 : ℕ) * D := hmain
    _ ≤ A + (b + 2) * D := by push_cast; nlinarith
    _ ≤ C * (b + 1) := by
      dsimp [C]
      nlinarith

/-- Uniform all-order `O(b)` control on the dyadic radius `r = 2^b`, for
`b ≥ 1`.  This retains the original public estimate as a direct corollary of
the boundary-compatible `O(b + 1)` theorem. -/
theorem exists_norm_iteratedDeriv_negativeLaplaceVerticalLog_rpow_le
    (F : BoundedFabius) (hF : IsFabius F) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {b θ : ℝ}, 1 ≤ b → |θ| ≤ 1 →
      ‖iteratedDeriv (m + 1)
        (negativeLaplaceVerticalLog F ((2 : ℝ) ^ b)) θ‖ ≤ C * b := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_norm_iteratedDeriv_negativeLaplaceVerticalLog_rpow_le_add_one F hF m
  let C : ℝ := 2 * D
  have hC : 0 ≤ C := mul_nonneg (by norm_num) hD
  refine ⟨C, hC, ?_⟩
  intro b θ hb hθ
  have hmain := hbound (zero_le_one.trans hb) hθ
  calc
    ‖iteratedDeriv (m + 1)
        (negativeLaplaceVerticalLog F ((2 : ℝ) ^ b)) θ‖ ≤
        D * (b + 1) := hmain
    _ ≤ C * b := by
      dsimp [C]
      nlinarith

/-- The all-order vertical bound in the explicit lower-Lambert coordinates. -/
theorem exists_norm_iteratedDeriv_negativeLaplaceVerticalLog_lambertRadius_le
    (F : BoundedFabius) (hF : IsFabius F) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {x θ : ℝ}, 1 ≤ fabiusLambertPhase x → |θ| ≤ 1 →
      ‖iteratedDeriv (m + 1)
        (negativeLaplaceVerticalLog F (fabiusLambertRadius x)) θ‖ ≤
          C * fabiusLambertPhase x := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_iteratedDeriv_negativeLaplaceVerticalLog_rpow_le F hF m
  refine ⟨C, hC, ?_⟩
  intro x θ hphase hθ
  simpa only [fabiusLambertRadius] using hbound hphase hθ

end Fabius
