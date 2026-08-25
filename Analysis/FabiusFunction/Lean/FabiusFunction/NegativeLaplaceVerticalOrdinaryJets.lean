import FabiusFunction.NegativeLaplaceVerticalAllOrderBound
import FabiusFunction.NegativeLaplaceAllOrderJets

/-!
# Vertical logarithmic jets as ordinary negative-Laplace jets

Write `Λ = negativeLaplaceLog` for the logarithm of the canonical negative
Laplace product, and `L_r = negativeLaplaceVerticalLog F r` for the
branch-safe logarithm of the negative-Laplace transform restricted to the
vertical line `s = r * (1 + θ * I)`, normalized by `L_r 0 = 0`.  That line is
the affine image `θ ↦ r + (r * I) * θ` of the real axis, so the chain rule
predicts

`L_r⁽ⁿ⁺¹⁾(0) = (r * I) ^ (n + 1) * Λ⁽ⁿ⁺¹⁾(r)`,  for `r > 0`.

Proving that identity is the whole content of this module.  It is what lets
the saddle machinery trade the vertical Taylor coefficients of `L_r` for the
exact ordinary jets of `Λ` -- linear drift plus periodic jet plus forward
tail -- supplied by `FabiusFunction.NegativeLaplaceAllOrderJets`.  It is not
a one-line chain rule in Lean: `iteratedDeriv` over `ℝ` sees only the
restriction of a function to the real line, so a real jet cannot be pushed
through a complex affine substitution directly.  The work is therefore two
holomorphic continuations of the first logarithmic derivative -- one in the
ordinary variable on the open right half-plane `{0 < re z}`, one in the
vertical parameter on the tilted half-plane `0 < (r + (r * I) * z).re` --
after which `iteratedDeriv_comp_ofReal_eq_of_differentiableOn` of
`FabiusFunction.NegativeLaplaceVerticalAllOrderBound` carries each iterated
derivative across the real embedding.

## Main results

* `negativeLaplaceComplexLogFirst` -- holomorphic `Λ'`, namely
  `-(G'(-z) / G(-z))` for the complex generating function `G`, together with
  `differentiableOn_negativeLaplaceComplexLogFirst` and
  `negativeLaplaceComplexLogFirst_ofReal`, which identifies its restriction
  to the positive real axis with `negativeLaplaceLogOrdinaryDeriv 1`.
* `negativeLaplaceComplexVerticalFirst` -- its pullback
  `(r * I) * Λ'(r + (r * I) * z)` along the vertical line, with
  `negativeLaplaceComplexVerticalFirst_ofReal` matching it against
  `negativeLaplaceVerticalLogFirst` on real arguments.
* `iteratedDeriv_negativeLaplaceVerticalLog_at_zero_eq_ordinary` -- the jet
  identity displayed above for positive orders.
* `iteratedDeriv_negativeLaplaceVerticalLog_at_zero_eq_ordinary_all` -- the
  exact all-order form, including the exceptional normalized value at order
  zero.

Every result except `negativeLaplaceComplexVerticalFirst_ofReal`, which is a
definitional rearrangement, assumes `IsFabius F`, for holomorphy of `G` and
for `G(-z) ≠ 0` on `{0 < re z}`.  The multiplicative jet identity holds only
in orders `n + 1`: at order zero, `L_r 0 = 0` while `Λ r` is not generally
zero.  The all-order theorem therefore records that normalization as a
separate `if` branch, matching the case split previously required of every
consumer.  The chain-rule factor carries a plus sign: the minus signs visible
in `negativeLaplaceComplexLogFirst` and in
`negativeLaplaceVerticalLogFirst` both come from the negative-Laplace
convention `s ↦ G(-s)` and cancel.  The
supporting differentiability and iterated-derivative lemmas for the vertical
continuation are `private` and are phrased with the unsimplified half-plane
predicate; only the final theorem assumes `0 < r`, under which that predicate
reads `im z < 1`.

The positive-order identity is consumed by
`FabiusFunction.FabiusSaddleExponentAllOrders`, inside
`verticalTaylorSum_sub_logTaylor_eq_jetSum`; the total form is available to
future consumers that do not want to split off order zero.
-/

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace Fabius

/-- Holomorphic logarithmic derivative of the negative Laplace transform on
the open right half-plane. -/
noncomputable def negativeLaplaceComplexLogFirst
    (F : BoundedFabius) (z : ℂ) : ℂ :=
  -(iteratedDeriv 1 (complexGeneratingFunction F) (-z) /
    complexGeneratingFunction F (-z))

/-- `negativeLaplaceComplexLogFirst F` is complex differentiable on the open
right half-plane `{z | 0 < z.re}`.  The hypothesis `IsFabius F` supplies
both the holomorphy of the complex generating function and its nonvanishing
at `-z` there; nothing is claimed off that half-plane. -/
theorem differentiableOn_negativeLaplaceComplexLogFirst
    (F : BoundedFabius) (hF : IsFabius F) :
    DifferentiableOn ℂ (negativeLaplaceComplexLogFirst F)
      {z : ℂ | 0 < z.re} := by
  intro z hz
  have harg : HasDerivAt (fun w : ℂ => -w) (-1) z := by
    exact (hasDerivAt_id z).neg.congr_of_eventuallyEq <| by
      filter_upwards with w
      rfl
  have hsmooth : ContDiff ℂ (↑(⊤ : ℕ∞))
      (iteratedDeriv 1 (complexGeneratingFunction F)) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv (𝕜 := ℂ) 1
      ((contDiff_complexGeneratingFunction F hF).of_le (by simp))
  have hnum :=
    (hsmooth.differentiable (by simp) (-z)).hasDerivAt.comp z harg
  have hden :=
    (differentiable_complexGeneratingFunction F hF (-z)).hasDerivAt.comp z harg
  have hdenNe : complexGeneratingFunction F (-z) ≠ 0 :=
    complexGeneratingFunction_neg_ne_zero F hF hz
  exact (hnum.div hden hdenNe).neg.differentiableAt.differentiableWithinAt

/-- On the positive real axis the holomorphic logarithmic derivative agrees
with the ordinary derivative sequence: for `s > 0` and `IsFabius F`,
`negativeLaplaceComplexLogFirst F s` is the cast into `ℂ` of
`negativeLaplaceLogOrdinaryDeriv 1 s`.  Nothing is claimed for `s ≤ 0`. -/
theorem negativeLaplaceComplexLogFirst_ofReal
    (F : BoundedFabius) (hF : IsFabius F) {s : ℝ} (hs : 0 < s) :
    negativeLaplaceComplexLogFirst F s =
      (negativeLaplaceLogOrdinaryDeriv 1 s : ℂ) := by
  have h1 := negativeLaplaceVerticalMoment_at_zero F hF 1 s
  have h0 := negativeLaplaceVerticalMoment_at_zero F hF 0 s
  simp only [negativeLaplaceVerticalMoment, Complex.ofReal_zero, zero_mul,
    add_zero, mul_one] at h1 h0
  have h0' : complexGeneratingFunction F (-s) =
      (fabiusLaplaceMoment F 0 s : ℂ) := by
    simpa only [iteratedDeriv_zero] using h0
  rw [negativeLaplaceComplexLogFirst, h1, h0']
  have hord := negativeLaplaceLogOrdinaryDeriv_hasDerivAt 0 hs
  have hfirst := negativeLaplaceLog_hasDerivAt F hF hs
  have heq : negativeLaplaceLogOrdinaryDeriv 1 s =
      negativeLaplaceLogFirst F s := hord.unique hfirst
  rw [heq]
  unfold negativeLaplaceLogFirst normalizedLaplaceMoment
  push_cast
  ring

private theorem iteratedDeriv_negativeLaplaceComplexLogFirst_ofReal
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ)
    {s : ℝ} (hs : 0 < s) :
    iteratedDeriv n (fun x : ℝ => negativeLaplaceComplexLogFirst F x) s =
      (negativeLaplaceLogOrdinaryDeriv (n + 1) s : ℂ) := by
  induction n generalizing s with
  | zero => exact negativeLaplaceComplexLogFirst_ofReal F hF hs
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv n
          (fun x : ℝ => negativeLaplaceComplexLogFirst F x) =ᶠ[nhds s]
          fun x => (negativeLaplaceLogOrdinaryDeriv (n + 1) x : ℂ) := by
        filter_upwards [Ioi_mem_nhds hs] with x hx
        exact ih hx
      rw [heq.deriv_eq]
      exact ((negativeLaplaceLogOrdinaryDeriv_hasDerivAt (n + 1) hs).ofReal_comp).deriv

/-- Complexification of the first vertical logarithmic derivative. -/
noncomputable def negativeLaplaceComplexVerticalFirst
    (F : BoundedFabius) (r : ℝ) (z : ℂ) : ℂ :=
  ((r : ℂ) * Complex.I) *
    negativeLaplaceComplexLogFirst F
      ((r : ℂ) + ((r : ℂ) * Complex.I) * z)

@[simp] theorem negativeLaplaceComplexVerticalFirst_ofReal
    (F : BoundedFabius) (r θ : ℝ) :
    negativeLaplaceComplexVerticalFirst F r θ =
      negativeLaplaceVerticalLogFirst F r θ := by
  rw [← negativeLaplaceVerticalLogFirstComplex_ofReal]
  unfold negativeLaplaceComplexVerticalFirst negativeLaplaceComplexLogFirst
    negativeLaplaceVerticalLogFirstComplex
  have harg :
      -((r : ℂ) + (r : ℂ) * Complex.I * (θ : ℂ)) =
        -((r : ℂ) * (1 + (θ : ℂ) * Complex.I)) := by ring
  rw [harg]
  ring

private theorem differentiableOn_negativeLaplaceComplexVerticalFirst
    (F : BoundedFabius) (hF : IsFabius F) (r : ℝ) :
    DifferentiableOn ℂ (negativeLaplaceComplexVerticalFirst F r)
      {z : ℂ | 0 < ((r : ℂ) + ((r : ℂ) * Complex.I) * z).re} := by
  intro z hz
  have harg : HasDerivAt
      (fun w : ℂ => (r : ℂ) + ((r : ℂ) * Complex.I) * w)
      ((r : ℂ) * Complex.I) z := by
    exact (((hasDerivAt_id z).const_mul
      ((r : ℂ) * Complex.I)).const_add (r : ℂ)).congr_deriv (by ring)
  have hV : IsOpen {w : ℂ | 0 < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hargMem : (r : ℂ) + ((r : ℂ) * Complex.I) * z ∈
      {w : ℂ | 0 < w.re} := hz
  have houterWithin := (differentiableOn_negativeLaplaceComplexLogFirst F hF)
    _ hargMem
  have houter := houterWithin.differentiableAt
    (hV.mem_nhds hargMem)
  exact ((houter.hasDerivAt.comp z harg).const_mul
    ((r : ℂ) * Complex.I)).differentiableAt.differentiableWithinAt

private theorem iteratedDeriv_negativeLaplaceComplexVerticalFirst
    (F : BoundedFabius) (hF : IsFabius F) (r : ℝ) (n : ℕ)
    {z : ℂ} (hz : 0 < ((r : ℂ) + ((r : ℂ) * Complex.I) * z).re) :
    iteratedDeriv n (negativeLaplaceComplexVerticalFirst F r) z =
      ((r : ℂ) * Complex.I) ^ (n + 1) *
        iteratedDeriv n (negativeLaplaceComplexLogFirst F)
          ((r : ℂ) + ((r : ℂ) * Complex.I) * z) := by
  let U : Set ℂ :=
    {w : ℂ | 0 < ((r : ℂ) + ((r : ℂ) * Complex.I) * w).re}
  let V : Set ℂ := {w : ℂ | 0 < w.re}
  have hU : IsOpen U := by
    dsimp [U]
    exact isOpen_lt continuous_const (by fun_prop)
  have hV : IsOpen V := by
    exact isOpen_lt continuous_const Complex.continuous_re
  have hHdiff := differentiableOn_negativeLaplaceComplexLogFirst F hF
  induction n generalizing z with
  | zero => simp [negativeLaplaceComplexVerticalFirst]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv n (negativeLaplaceComplexVerticalFirst F r) =ᶠ[nhds z]
          fun w => ((r : ℂ) * Complex.I) ^ (n + 1) *
            iteratedDeriv n (negativeLaplaceComplexLogFirst F)
              ((r : ℂ) + ((r : ℂ) * Complex.I) * w) := by
        filter_upwards [hU.mem_nhds (show z ∈ U from hz)] with w hw
        exact ih hw
      rw [heq.deriv_eq]
      let arg : ℂ := (r : ℂ) + ((r : ℂ) * Complex.I) * z
      have hargV : arg ∈ V := hz
      have harg : HasDerivAt
          (fun w : ℂ => (r : ℂ) + ((r : ℂ) * Complex.I) * w)
          ((r : ℂ) * Complex.I) z := by
        exact (((hasDerivAt_id z).const_mul
          ((r : ℂ) * Complex.I)).const_add (r : ℂ)).congr_deriv (by ring)
      have han : AnalyticAt ℂ
          (iteratedDeriv n (negativeLaplaceComplexLogFirst F)) arg := by
        rw [iteratedDeriv_eq_iterate]
        exact ((hHdiff.analyticOnNhd hV).iterated_deriv n) arg hargV
      have hout : HasDerivAt
          (iteratedDeriv n (negativeLaplaceComplexLogFirst F))
          (iteratedDeriv (n + 1) (negativeLaplaceComplexLogFirst F) arg) arg := by
        rw [iteratedDeriv_succ]
        exact han.differentiableAt.hasDerivAt
      have hcomp := (hout.comp z harg).const_mul
        (((r : ℂ) * Complex.I) ^ (n + 1))
      have hcomp' : HasDerivAt
          (fun w => ((r : ℂ) * Complex.I) ^ (n + 1) *
            iteratedDeriv n (negativeLaplaceComplexLogFirst F)
              ((r : ℂ) + ((r : ℂ) * Complex.I) * w))
          (((r : ℂ) * Complex.I) ^ (n + 1) *
            (iteratedDeriv (n + 1) (negativeLaplaceComplexLogFirst F) arg *
              ((r : ℂ) * Complex.I))) z :=
        hcomp.congr_of_eventuallyEq <| by
          filter_upwards with w
          rfl
      rw [hcomp'.deriv]
      dsimp only [arg]
      ring

/-- Every zero-axis vertical logarithmic jet is the corresponding ordinary
negative-Laplace jet multiplied by the expected complex chain-rule factor. -/
theorem iteratedDeriv_negativeLaplaceVerticalLog_at_zero_eq_ordinary
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ)
    {r : ℝ} (hr : 0 < r) :
    iteratedDeriv (n + 1) (negativeLaplaceVerticalLog F r) 0 =
      (((r : ℂ) * Complex.I) ^ (n + 1)) *
        ((iteratedDeriv (𝕜 := ℝ) (n + 1) negativeLaplaceLog r : ℝ) : ℂ) := by
  have hderiv : deriv (negativeLaplaceVerticalLog F r) =
      fun θ : ℝ => negativeLaplaceComplexVerticalFirst F r θ := by
    funext θ
    rw [(negativeLaplaceVerticalLog_hasDerivAt_cumulant F hF hr θ).deriv]
    exact (negativeLaplaceComplexVerticalFirst_ofReal F r θ).symm
  rw [iteratedDeriv_succ', hderiv]
  let U : Set ℂ :=
    {z : ℂ | 0 < ((r : ℂ) + ((r : ℂ) * Complex.I) * z).re}
  have hU : IsOpen U := by
    dsimp [U]
    exact isOpen_lt continuous_const (by fun_prop)
  have hzeroU : (0 : ℂ) ∈ U := by
    change 0 < ((r : ℂ) + ((r : ℂ) * Complex.I) * (0 : ℂ)).re
    simpa using hr
  rw [iteratedDeriv_comp_ofReal_eq_of_differentiableOn
    (negativeLaplaceComplexVerticalFirst F r) hU
    (differentiableOn_negativeLaplaceComplexVerticalFirst F hF r) n 0 hzeroU]
  change iteratedDeriv n (negativeLaplaceComplexVerticalFirst F r) (0 : ℂ) = _
  rw [iteratedDeriv_negativeLaplaceComplexVerticalFirst F hF r n hzeroU]
  simp only [mul_zero, add_zero]
  let V : Set ℂ := {z : ℂ | 0 < z.re}
  have hV : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hrV : (r : ℂ) ∈ V := by simpa only [V, Complex.ofReal_re]
  rw [← iteratedDeriv_comp_ofReal_eq_of_differentiableOn
    (negativeLaplaceComplexLogFirst F) hV
    (differentiableOn_negativeLaplaceComplexLogFirst F hF) n r hrV]
  rw [iteratedDeriv_negativeLaplaceComplexLogFirst_ofReal F hF n hr]
  rw [iteratedDeriv_negativeLaplaceLog_eq_ordinaryDeriv (n + 1) hr]

/-- Exact zero-axis vertical logarithmic jet at every order.  Positive orders
are the ordinary negative-Laplace jets multiplied by their complex
chain-rule factors; order zero is the exceptional normalization
`negativeLaplaceVerticalLog F r 0 = 0`. -/
theorem iteratedDeriv_negativeLaplaceVerticalLog_at_zero_eq_ordinary_all
    (F : BoundedFabius) (hF : IsFabius F) (order : ℕ)
    {r : ℝ} (hr : 0 < r) :
    iteratedDeriv order (negativeLaplaceVerticalLog F r) 0 =
      if order = 0 then 0 else
        (((r : ℂ) * Complex.I) ^ order) *
          ((iteratedDeriv (𝕜 := ℝ) order negativeLaplaceLog r : ℝ) : ℂ) := by
  cases order with
  | zero => simp
  | succ n =>
      simpa using
        iteratedDeriv_negativeLaplaceVerticalLog_at_zero_eq_ordinary F hF n hr

end Fabius
