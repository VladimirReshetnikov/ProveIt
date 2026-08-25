import FabiusFunction.NegativeLaplaceVerticalTaylor
import FabiusFunction.FabiusLambertSaddle

/-!
# Uniform fourth-order vertical Laplace bounds

The vertical negative-Laplace transform `P(z) = G(-z)`, with `G` the complex
generating function of a Fabius solution, obeys the exact one-factor dilation
law `P(2z) = ((1 - e^(-z)) / z) * P(z)`.  Restricting to the vertical line
`z = s * (1 + i * θ)` and taking the branch-safe logarithm of
`FabiusFunction.NegativeLaplaceVerticalLog` turns that law into an additive
recurrence for the derivatives in `θ`.  Writing

`K₁(s, θ) = (s * i) * (e^(-z) / (1 - e^(-z)) - 1 / z)`,  `z = s * (1 + i * θ)`,

for the logarithmic derivative of the dilation factor, the first derivative
satisfies `L₁(2s, θ) = K₁(s, θ) + L₁(s, θ)`; since the dilation acts on the
parameter `s` while the differentiation acts on `θ`, every higher order
inherits the same recurrence with no extra weight.  The increment `K₄` is
bounded by a single absolute constant once `s ≥ 1`, so iterating outward from
the compact base rectangle `1 ≤ r ≤ 2`, `|θ| ≤ 1` costs one constant per
dyadic scale and gives growth linear in the number of scales.

The module exists to supply the quartic Taylor-remainder constant used by the
first quantitative central saddle theorem, and it stops at order four for that
reason.  Its complex kernels are the right half-plane analogues of the real
kernels of `FabiusFunction.NegativeLaplaceDerivativeBounds`, with `Real.exp`
replaced by `Complex.exp`.  The later module
`FabiusFunction.NegativeLaplaceVerticalAllOrderBound` reuses the order-one
material from here and replaces this hand-run order-by-order chain with Cauchy
estimates valid at every order.

## Main results

* `negativeLaplaceComplexFactor_hasDerivAt`, and
  `negativeLaplaceComplexKernelFirst_hasDerivAt` with its `Second` and `Third`
  companions -- the dilation factor has logarithmic derivative `K₁`, and each
  complex kernel differentiates to the next, on the half-plane `0 < z.re`.
* `negativeLaplaceVerticalKernelLogFirst_hasDerivAt` and its `Second` and
  `Third` companions -- the same chain after `z = s * (1 + i * θ)`,
  differentiated in `θ` for `s > 0`.
* `negativeLaplaceVerticalLogFirst_two_mul` through
  `negativeLaplaceVerticalLogFourth_two_mul` -- the exact unweighted dyadic
  recurrence at orders one through four.
* `norm_negativeLaplaceVerticalKernelLogFourth_le` -- `‖K₄(s, θ)‖ ≤ 1542` for
  every `s ≥ 1` and every real `θ`.
* `exists_norm_negativeLaplaceVerticalLogFourth_le_dyadicScales` -- iterating
  the recurrence bounds `‖L₄(r, θ)‖` by a compactness constant plus `1542` per
  dyadic scale, for `1 ≤ r ≤ 2 ^ (m + 1)` and `|θ| ≤ 1`.
* `exists_norm_negativeLaplaceVerticalLogFourth_rpow_le_add_one` -- the
  resulting `O(b + 1)` bound at radius `r = 2 ^ b`, valid from the natural
  endpoint `b = 0` and uniform in the strip `|θ| ≤ 1`.
* `exists_norm_negativeLaplaceVerticalLogFourth_rpow_le` -- the compatible
  `O(b)` form for `b ≥ 1`.  This is the form
  `FabiusFunction.FabiusSaddleCentralLambert` consumes, as the quartic
  coefficient of its exponent remainder.
* `exists_norm_negativeLaplaceVerticalLogFourth_lambertRadius_le` -- the same
  bound restated in the explicit lower-Lambert saddle coordinates
  `r = fabiusLambertRadius x`, `b = fabiusLambertPhase x`.

## Conventions and caveats

* `Lⱼ` abbreviates `negativeLaplaceVerticalLogFirst` through
  `negativeLaplaceVerticalLogFourth`, the `j`th `θ`-derivative of the
  branch-safe vertical logarithm.  Its chain-rule prefactor is
  `(-(r * i)) ^ j`, because the transform is read at `-(r * (1 + i * θ))`,
  whereas `Kⱼ` carries `(s * i) ^ j`, because the dilation factor is read at
  `s * (1 + i * θ)`; both are ordinary logarithmic derivatives in `θ`.
* The uniform bounds are restricted to radius `r ≥ 1` and to the fixed strip
  `|θ| ≤ 1`, and nothing is claimed for smaller radius or larger `θ`.  The
  differentiation chain and the exact dyadic recurrences themselves hold for
  every `s > 0` and every real `θ`, and the `K₄` bound for every `s ≥ 1` and
  every real `θ`.
* `1542 = 64 * 24 + 6` is explicit but deliberately generous, sized so that the
  crude estimate `s ^ 4 * e^(-s) ≤ 4!` closes the proof; it is not sharp, and
  the base constant supplied by compactness is not explicit at all.
* Every statement is for an arbitrary `F : BoundedFabius` with `IsFabius F`.
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped Interval Topology

namespace Fabius

/-- The complex kernel `K₁(z) = exp (-z) / (1 - exp (-z)) - 1 / z`, with the
rational singular part `1 / z` kept as a separate summand.  It is the
`Complex.exp` analogue of `negativeLaplaceKernelFirst` of
`FabiusFunction.NegativeLaplaceDerivativeBounds`.  It is identified as the
logarithmic derivative of `negativeLaplaceComplexFactor` by
`negativeLaplaceComplexFactor_hasDerivAt`, which needs `0 < z.re`; the
definition itself is unrestricted, so Lean's `x / 0 = 0` convention governs
the value at `z = 0` and at the poles of the first summand. -/
noncomputable def negativeLaplaceComplexKernelFirst (z : ℂ) : ℂ :=
  Complex.exp (-z) / (1 - Complex.exp (-z)) - 1 / z

/-- The complex kernel `K₂(z) = -exp (-z) / (1 - exp (-z)) ^ 2 + 1 / z ^ 2`, the
`Complex.exp` analogue of `negativeLaplaceKernelSecond`.  It is identified
as the derivative of `negativeLaplaceComplexKernelFirst` by
`negativeLaplaceComplexKernelFirst_hasDerivAt`, for `0 < z.re`. -/
noncomputable def negativeLaplaceComplexKernelSecond (z : ℂ) : ℂ :=
  -Complex.exp (-z) / (1 - Complex.exp (-z)) ^ 2 + 1 / z ^ 2

/-- The complex kernel
`K₃(z) = exp (-z) * (1 + exp (-z)) / (1 - exp (-z)) ^ 3 - 2 / z ^ 3`, the
`Complex.exp` analogue of `negativeLaplaceKernelThird`.  It is identified as
the derivative of `negativeLaplaceComplexKernelSecond` by
`negativeLaplaceComplexKernelSecond_hasDerivAt`, for `0 < z.re`. -/
noncomputable def negativeLaplaceComplexKernelThird (z : ℂ) : ℂ :=
  Complex.exp (-z) * (1 + Complex.exp (-z)) /
      (1 - Complex.exp (-z)) ^ 3 - 2 / z ^ 3

/-- The complex kernel `K₄(z)`, equal to
`-(exp (-z) * (1 + 4 * exp (-z) + exp (-z) ^ 2)) / (1 - exp (-z)) ^ 4`
plus `6 / z ^ 4`; the `Complex.exp` analogue of
`negativeLaplaceKernelFourth`.  It is identified as the derivative of
`negativeLaplaceComplexKernelThird` by
`negativeLaplaceComplexKernelThird_hasDerivAt`, for `0 < z.re`.  This is the
highest complex kernel the module defines. -/
noncomputable def negativeLaplaceComplexKernelFourth (z : ℂ) : ℂ :=
  -(Complex.exp (-z) *
      (1 + 4 * Complex.exp (-z) + Complex.exp (-z) ^ 2)) /
      (1 - Complex.exp (-z)) ^ 4 + 6 / z ^ 4

private lemma complex_one_sub_exp_neg_ne {z : ℂ} (hz : 0 < z.re) :
    1 - Complex.exp (-z) ≠ 0 := by
  intro h
  have hexp : Complex.exp (-z) = 1 := (sub_eq_zero.mp h).symm
  have hnorm := congrArg norm hexp
  rw [Complex.norm_exp, norm_one] at hnorm
  have hre : (-z).re = 0 := (Real.exp_eq_one_iff _).mp hnorm
  norm_num at hre
  linarith

private lemma complex_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := by
  intro h
  subst z
  norm_num at hz

/-- On the open right half-plane `0 < z.re` the dilation factor
`negativeLaplaceComplexFactor` is complex differentiable at `z`, with
derivative its own value at `z` times
`negativeLaplaceComplexKernelFirst z`; that is, `K₁` is its logarithmic
derivative there. -/
theorem negativeLaplaceComplexFactor_hasDerivAt
    {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt negativeLaplaceComplexFactor
      (negativeLaplaceComplexFactor z * negativeLaplaceComplexKernelFirst z) z := by
  have hz0 := complex_ne_zero_of_re_pos hz
  have ht := (hasDerivAt_id z).neg.cexp
  have hnum := (hasDerivAt_const z 1).sub ht
  have h := hnum.div (hasDerivAt_id z) hz0
  have heq : negativeLaplaceComplexFactor =ᶠ[nhds z]
      (((fun w : ℂ => 1) - fun w => Complex.exp (-w)) / id) := by
    filter_upwards [eventually_ne_nhds hz0] with w hw
    rw [negativeLaplaceComplexFactor, complexExpm1Div_of_ne]
    · simp only [Pi.sub_apply, Pi.div_apply, id_eq]
      field_simp [hw]
      ring
    · exact neg_ne_zero.mpr hw
  have hc := h.congr_of_eventuallyEq heq
  refine hc.congr_deriv ?_
  unfold negativeLaplaceComplexFactor negativeLaplaceComplexKernelFirst
  rw [complexExpm1Div_of_ne (neg_ne_zero.mpr hz0)]
  simp only [id_eq, Pi.neg_apply, Pi.sub_apply]
  field_simp [hz0, complex_one_sub_exp_neg_ne hz]
  ring

/-- On the open right half-plane `0 < z.re` the kernel
`negativeLaplaceComplexKernelFirst` is complex differentiable at `z` with
derivative `negativeLaplaceComplexKernelSecond z`. -/
theorem negativeLaplaceComplexKernelFirst_hasDerivAt
    {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt negativeLaplaceComplexKernelFirst
      (negativeLaplaceComplexKernelSecond z) z := by
  have hz0 := complex_ne_zero_of_re_pos hz
  have ht := (hasDerivAt_id z).neg.cexp
  have hnum := (hasDerivAt_const z 1).sub ht
  have hquot := ht.div hnum (complex_one_sub_exp_neg_ne hz)
  have hinv := (hasDerivAt_const z 1).div (hasDerivAt_id z) hz0
  have h := hquot.sub hinv
  refine h.congr_deriv ?_
  unfold negativeLaplaceComplexKernelSecond
  simp only [id_eq, Pi.neg_apply, Pi.sub_apply]
  field_simp [hz0, complex_one_sub_exp_neg_ne hz]
  ring

/-- On the open right half-plane `0 < z.re` the kernel
`negativeLaplaceComplexKernelSecond` is complex differentiable at `z` with
derivative `negativeLaplaceComplexKernelThird z`. -/
theorem negativeLaplaceComplexKernelSecond_hasDerivAt
    {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt negativeLaplaceComplexKernelSecond
      (negativeLaplaceComplexKernelThird z) z := by
  have hz0 := complex_ne_zero_of_re_pos hz
  have ht := (hasDerivAt_id z).neg.cexp
  have hnum := (hasDerivAt_const z 1).sub ht
  have hfrac := ht.neg.div (hnum.pow 2)
    (pow_ne_zero 2 (complex_one_sub_exp_neg_ne hz))
  have hz2 := (hasDerivAt_id z).pow 2
  have hone := (hasDerivAt_const z 1).div hz2 (pow_ne_zero 2 hz0)
  have h := hfrac.add hone
  refine h.congr_deriv ?_
  unfold negativeLaplaceComplexKernelThird
  simp only [id_eq, Pi.neg_apply, Pi.sub_apply, Pi.pow_apply]
  field_simp [hz0, complex_one_sub_exp_neg_ne hz]
  ring

/-- On the open right half-plane `0 < z.re` the kernel
`negativeLaplaceComplexKernelThird` is complex differentiable at `z` with
derivative `negativeLaplaceComplexKernelFourth z`. -/
theorem negativeLaplaceComplexKernelThird_hasDerivAt
    {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt negativeLaplaceComplexKernelThird
      (negativeLaplaceComplexKernelFourth z) z := by
  have hz0 := complex_ne_zero_of_re_pos hz
  have ht := (hasDerivAt_id z).neg.cexp
  have hnum := (hasDerivAt_const z 1).sub ht
  have hplus := (hasDerivAt_const z 1).add ht
  have hfrac := (ht.mul hplus).div (hnum.pow 3)
    (pow_ne_zero 3 (complex_one_sub_exp_neg_ne hz))
  have hz3 := (hasDerivAt_id z).pow 3
  have htwo := (hasDerivAt_const z 2).div hz3 (pow_ne_zero 3 hz0)
  have h := hfrac.sub htwo
  refine h.congr_deriv ?_
  unfold negativeLaplaceComplexKernelFourth
  simp only [id_eq, Pi.neg_apply, Pi.sub_apply, Pi.add_apply, Pi.mul_apply,
    Pi.pow_apply]
  field_simp [hz0, complex_one_sub_exp_neg_ne hz]
  ring

/-- The first complex kernel evaluated on the vertical line
`z = s * (1 + θ * I)`, carrying the chain-rule prefactor `s * I`.  Both `s`
and `θ` are real and the definition imposes no positivity; the restrictions
enter only in the lemmas below.  This kernel is also used by
`FabiusFunction.NegativeLaplaceVerticalAllOrderBound`, which continues it
holomorphically in the vertical parameter. -/
noncomputable def negativeLaplaceVerticalKernelLogFirst (s θ : ℝ) : ℂ :=
  ((s : ℂ) * Complex.I) * negativeLaplaceComplexKernelFirst
    ((s : ℂ) * (1 + (θ : ℂ) * Complex.I))

/-- The second complex kernel on the vertical line `z = s * (1 + θ * I)`, with
the chain-rule prefactor `(s * I) ^ 2`.  For `s > 0` it is the
`θ`-derivative of `negativeLaplaceVerticalKernelLogFirst s`, by
`negativeLaplaceVerticalKernelLogFirst_hasDerivAt`. -/
noncomputable def negativeLaplaceVerticalKernelLogSecond (s θ : ℝ) : ℂ :=
  ((s : ℂ) * Complex.I) ^ 2 * negativeLaplaceComplexKernelSecond
    ((s : ℂ) * (1 + (θ : ℂ) * Complex.I))

/-- The third complex kernel on the vertical line `z = s * (1 + θ * I)`, with
the chain-rule prefactor `(s * I) ^ 3`.  For `s > 0` it is the
`θ`-derivative of `negativeLaplaceVerticalKernelLogSecond s`, by
`negativeLaplaceVerticalKernelLogSecond_hasDerivAt`. -/
noncomputable def negativeLaplaceVerticalKernelLogThird (s θ : ℝ) : ℂ :=
  ((s : ℂ) * Complex.I) ^ 3 * negativeLaplaceComplexKernelThird
    ((s : ℂ) * (1 + (θ : ℂ) * Complex.I))

/-- The fourth complex kernel on the vertical line `z = s * (1 + θ * I)`, with
the chain-rule prefactor `(s * I) ^ 4`.  For `s > 0` it is the
`θ`-derivative of `negativeLaplaceVerticalKernelLogThird s`, by
`negativeLaplaceVerticalKernelLogThird_hasDerivAt`.  This is the order at
which the uniform increment bound of this module is proved. -/
noncomputable def negativeLaplaceVerticalKernelLogFourth (s θ : ℝ) : ℂ :=
  ((s : ℂ) * Complex.I) ^ 4 * negativeLaplaceComplexKernelFourth
    ((s : ℂ) * (1 + (θ : ℂ) * Complex.I))

private lemma vertical_arg_hasDerivAt (s θ : ℝ) :
    HasDerivAt (fun t : ℝ => (s : ℂ) * (1 + (t : ℂ) * Complex.I))
      ((s : ℂ) * Complex.I) θ := by
  have hcomplex : HasDerivAt
      (fun z : ℂ => (s : ℂ) * (1 + z * Complex.I))
      ((s : ℂ) * Complex.I) (θ : ℂ) := by
    have h := ((hasDerivAt_id (θ : ℂ)).const_mul
      ((s : ℂ) * Complex.I)).add_const (s : ℂ)
    have h' : HasDerivAt (fun z : ℂ =>
        (s : ℂ) * Complex.I * z + (s : ℂ))
        ((s : ℂ) * Complex.I) (θ : ℂ) := h.congr_deriv (by ring)
    apply h'.congr_of_eventuallyEq
    filter_upwards with z
    ring
  exact hcomplex.comp_ofReal

private lemma vertical_arg_re (s θ : ℝ) :
    ((s : ℂ) * (1 + (θ : ℂ) * Complex.I)).re = s := by
  norm_num

/-- For `s > 0` and every real `θ`, `negativeLaplaceVerticalKernelLogFirst s` is
differentiable in the vertical parameter with derivative
`negativeLaplaceVerticalKernelLogSecond s θ`. -/
theorem negativeLaplaceVerticalKernelLogFirst_hasDerivAt
    {s : ℝ} (hs : 0 < s) (θ : ℝ) :
    HasDerivAt (negativeLaplaceVerticalKernelLogFirst s)
      (negativeLaplaceVerticalKernelLogSecond s θ) θ := by
  have hz : 0 < ((s : ℂ) * (1 + (θ : ℂ) * Complex.I)).re := by
    rw [vertical_arg_re]
    exact hs
  have h := (negativeLaplaceComplexKernelFirst_hasDerivAt hz).comp θ
    (vertical_arg_hasDerivAt s θ)
  exact ((h.const_mul ((s : ℂ) * Complex.I))).congr_deriv (by
    unfold negativeLaplaceVerticalKernelLogSecond
    ring)

/-- For `s > 0` and every real `θ`, `negativeLaplaceVerticalKernelLogSecond s`
is differentiable in the vertical parameter with derivative
`negativeLaplaceVerticalKernelLogThird s θ`. -/
theorem negativeLaplaceVerticalKernelLogSecond_hasDerivAt
    {s : ℝ} (hs : 0 < s) (θ : ℝ) :
    HasDerivAt (negativeLaplaceVerticalKernelLogSecond s)
      (negativeLaplaceVerticalKernelLogThird s θ) θ := by
  have hz : 0 < ((s : ℂ) * (1 + (θ : ℂ) * Complex.I)).re := by
    rw [vertical_arg_re]
    exact hs
  have h := (negativeLaplaceComplexKernelSecond_hasDerivAt hz).comp θ
    (vertical_arg_hasDerivAt s θ)
  exact ((h.const_mul (((s : ℂ) * Complex.I) ^ 2))).congr_deriv (by
    unfold negativeLaplaceVerticalKernelLogThird
    ring)

/-- For `s > 0` and every real `θ`, `negativeLaplaceVerticalKernelLogThird s` is
differentiable in the vertical parameter with derivative
`negativeLaplaceVerticalKernelLogFourth s θ`. -/
theorem negativeLaplaceVerticalKernelLogThird_hasDerivAt
    {s : ℝ} (hs : 0 < s) (θ : ℝ) :
    HasDerivAt (negativeLaplaceVerticalKernelLogThird s)
      (negativeLaplaceVerticalKernelLogFourth s θ) θ := by
  have hz : 0 < ((s : ℂ) * (1 + (θ : ℂ) * Complex.I)).re := by
    rw [vertical_arg_re]
    exact hs
  have h := (negativeLaplaceComplexKernelThird_hasDerivAt hz).comp θ
    (vertical_arg_hasDerivAt s θ)
  exact ((h.const_mul (((s : ℂ) * Complex.I) ^ 3))).congr_deriv (by
    unfold negativeLaplaceVerticalKernelLogFourth
    ring)

private theorem negativeLaplaceVerticalCurve_two_mul
    (F : BoundedFabius) (hF : IsFabius F) (s θ : ℝ) :
    negativeLaplaceVerticalCurve F (2 * s) θ =
      negativeLaplaceComplexFactor
          ((s : ℂ) * (1 + (θ : ℂ) * Complex.I)) *
        negativeLaplaceVerticalCurve F s θ := by
  have h := proposition_two_formula F hF
    (-((s : ℂ) * (1 + (θ : ℂ) * Complex.I)))
  unfold negativeLaplaceVerticalCurve negativeLaplaceComplexFactor
  convert h using 1
  push_cast
  ring_nf

private theorem negativeLaplaceVerticalFactor_hasDerivAt
    {s : ℝ} (hs : 0 < s) (θ : ℝ) :
    HasDerivAt
      (fun t : ℝ => negativeLaplaceComplexFactor
        ((s : ℂ) * (1 + (t : ℂ) * Complex.I)))
      (negativeLaplaceComplexFactor
          ((s : ℂ) * (1 + (θ : ℂ) * Complex.I)) *
        negativeLaplaceVerticalKernelLogFirst s θ) θ := by
  have hz : 0 < ((s : ℂ) * (1 + (θ : ℂ) * Complex.I)).re := by
    rw [vertical_arg_re]
    exact hs
  have h := (negativeLaplaceComplexFactor_hasDerivAt hz).comp θ
    (vertical_arg_hasDerivAt s θ)
  exact h.congr_deriv (by
    unfold negativeLaplaceVerticalKernelLogFirst
    ring)

/-- The exact one-factor dyadic recurrence at order one: for an arbitrary
`F : BoundedFabius` with `IsFabius F`, every `s > 0` and every real `θ`, the
first vertical logarithmic derivative at radius `2 * s` equals the increment
`negativeLaplaceVerticalKernelLogFirst s θ` plus its own value at radius `s`.
No weight appears, because the dilation acts on `s` while the
differentiation acts on `θ`.  The orders two through four below are obtained
from this one by differentiating in `θ`, and
`FabiusFunction.NegativeLaplaceVerticalAllOrderBound` reuses this order-one
statement for its all-order recurrence. -/
theorem negativeLaplaceVerticalLogFirst_two_mul
    (F : BoundedFabius) (hF : IsFabius F)
    {s : ℝ} (hs : 0 < s) (θ : ℝ) :
    negativeLaplaceVerticalLogFirst F (2 * s) θ =
      negativeLaplaceVerticalKernelLogFirst s θ +
        negativeLaplaceVerticalLogFirst F s θ := by
  let factorCurve : ℝ → ℂ := fun t => negativeLaplaceComplexFactor
    ((s : ℂ) * (1 + (t : ℂ) * Complex.I))
  have hfactor : HasDerivAt factorCurve
      (factorCurve θ * negativeLaplaceVerticalKernelLogFirst s θ) θ := by
    exact negativeLaplaceVerticalFactor_hasDerivAt hs θ
  have hcurve : HasDerivAt (negativeLaplaceVerticalCurve F s)
      (deriv (negativeLaplaceVerticalCurve F s) θ) θ :=
    ((contDiff_negativeLaplaceVerticalCurve F hF s).differentiable
      (by simp) θ).hasDerivAt
  have hprod := hfactor.mul hcurve
  have heq : negativeLaplaceVerticalCurve F (2 * s) =ᶠ[nhds θ]
      factorCurve * negativeLaplaceVerticalCurve F s := by
    filter_upwards with t
    exact negativeLaplaceVerticalCurve_two_mul F hF s t
  have hleft := hprod.congr_of_eventuallyEq heq
  have hderiv := hleft.deriv
  have hfactorNe : factorCurve θ ≠ 0 := by
    apply negativeLaplaceComplexFactor_ne_zero
    rw [vertical_arg_re]
    exact hs
  have hcurveNe := negativeLaplaceVerticalCurve_ne_zero F hF hs θ
  rw [negativeLaplaceVerticalLogFirst_apply,
    ← negativeLaplaceVerticalLogDerivative_eq_cumulant F hF (2 * s) θ,
    negativeLaplaceVerticalLogFirst_apply,
    ← negativeLaplaceVerticalLogDerivative_eq_cumulant F hF s θ]
  unfold negativeLaplaceVerticalLogDerivative
  rw [hderiv, negativeLaplaceVerticalCurve_two_mul F hF s θ]
  dsimp [factorCurve] at hfactorNe ⊢
  field_simp [hfactorNe, hcurveNe]

/-- The second vertical logarithmic derivative inherits the one-factor dyadic
recurrence by differentiating the first one in the vertical parameter.  No
weight appears: the dilation acts on `s`, the differentiation on `θ`. -/
theorem negativeLaplaceVerticalLogSecond_two_mul
    (F : BoundedFabius) (hF : IsFabius F)
    {s : ℝ} (hs : 0 < s) (θ : ℝ) :
    negativeLaplaceVerticalLogSecond F (2 * s) θ =
      negativeLaplaceVerticalKernelLogSecond s θ +
        negativeLaplaceVerticalLogSecond F s θ :=
  hasDerivAt_of_parameterScalingRecurrence_two_mul
    (f := negativeLaplaceVerticalLogFirst F)
    (f' := negativeLaplaceVerticalLogSecond F)
    (g := negativeLaplaceVerticalKernelLogFirst)
    (g' := negativeLaplaceVerticalKernelLogSecond)
    (fun _ ht t => negativeLaplaceVerticalLogFirst_hasDerivAt F hF ht t)
    (fun _ ht t => negativeLaplaceVerticalKernelLogFirst_hasDerivAt ht t)
    (fun _ ht t => negativeLaplaceVerticalLogFirst_two_mul F hF ht t) hs θ

/-- The third vertical logarithmic derivative satisfies the same unweighted
one-factor dyadic recurrence. -/
theorem negativeLaplaceVerticalLogThird_two_mul
    (F : BoundedFabius) (hF : IsFabius F)
    {s : ℝ} (hs : 0 < s) (θ : ℝ) :
    negativeLaplaceVerticalLogThird F (2 * s) θ =
      negativeLaplaceVerticalKernelLogThird s θ +
        negativeLaplaceVerticalLogThird F s θ :=
  hasDerivAt_of_parameterScalingRecurrence_two_mul
    (f := negativeLaplaceVerticalLogSecond F)
    (f' := negativeLaplaceVerticalLogThird F)
    (g := negativeLaplaceVerticalKernelLogSecond)
    (g' := negativeLaplaceVerticalKernelLogThird)
    (fun _ ht t => negativeLaplaceVerticalLogSecond_hasDerivAt F hF ht t)
    (fun _ ht t => negativeLaplaceVerticalKernelLogSecond_hasDerivAt ht t)
    (fun _ ht t => negativeLaplaceVerticalLogSecond_two_mul F hF ht t) hs θ

/-- The fourth vertical logarithmic derivative satisfies the same unweighted
one-factor dyadic recurrence.  This is the order used by the uniform off-axis
bound below. -/
theorem negativeLaplaceVerticalLogFourth_two_mul
    (F : BoundedFabius) (hF : IsFabius F)
    {s : ℝ} (hs : 0 < s) (θ : ℝ) :
    negativeLaplaceVerticalLogFourth F (2 * s) θ =
      negativeLaplaceVerticalKernelLogFourth s θ +
        negativeLaplaceVerticalLogFourth F s θ :=
  hasDerivAt_of_parameterScalingRecurrence_two_mul
    (f := negativeLaplaceVerticalLogThird F)
    (f' := negativeLaplaceVerticalLogFourth F)
    (g := negativeLaplaceVerticalKernelLogThird)
    (g' := negativeLaplaceVerticalKernelLogFourth)
    (fun _ ht t => negativeLaplaceVerticalLogThird_hasDerivAt F hF ht t)
    (fun _ ht t => negativeLaplaceVerticalKernelLogThird_hasDerivAt ht t)
    (fun _ ht t => negativeLaplaceVerticalLogThird_two_mul F hF ht t) hs θ

private lemma vertical_exp_neg_le_half
    {s θ : ℝ} (hs : 1 ≤ s) :
    ‖Complex.exp
      (-((s : ℂ) * (1 + (θ : ℂ) * Complex.I)))‖ ≤ 1 / 2 := by
  rw [Complex.norm_exp]
  have hre : (-((s : ℂ) * (1 + (θ : ℂ) * Complex.I))).re = -s := by
    norm_num
  rw [hre]
  calc
    Real.exp (-s) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ 1 / 2 := Real.exp_neg_one_lt_half.le

/-- Uniform bound `‖K₄(s, θ)‖ ≤ 1542` on the fourth vertical kernel, valid for
every `s ≥ 1` and every real `θ`; the vertical parameter is unrestricted.
The constant `1542 = 64 * 24 + 6` is explicit but deliberately generous, and
no attainment or converse is claimed. -/
theorem norm_negativeLaplaceVerticalKernelLogFourth_le
    {s : ℝ} (hs : 1 ≤ s) (θ : ℝ) :
    ‖negativeLaplaceVerticalKernelLogFourth s θ‖ ≤ 1542 := by
  let z : ℂ := (s : ℂ) * (1 + (θ : ℂ) * Complex.I)
  let t : ℂ := Complex.exp (-z)
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have ht0 : 0 ≤ ‖t‖ := norm_nonneg _
  have ht : ‖t‖ ≤ 1 / 2 := by
    dsimp [t, z]
    exact vertical_exp_neg_le_half hs
  have hzre : z.re = s := by
    dsimp [z]
    norm_num
  have hzNorm : s ≤ ‖z‖ := by
    rw [← abs_of_pos hs0, ← hzre]
    exact Complex.abs_re_le_norm z
  have hzNorm0 : 0 < ‖z‖ := hs0.trans_le hzNorm
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzNorm0
  have hden : 1 / 2 ≤ ‖1 - t‖ := by
    calc
      1 / 2 ≤ ‖(1 : ℂ)‖ - ‖t‖ := by norm_num; linarith
      _ ≤ ‖(1 : ℂ) - t‖ := norm_sub_norm_le _ _
  have hden0 : 0 < ‖1 - t‖ := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hden
  have hdenPow : (1 / 16 : ℝ) ≤ ‖1 - t‖ ^ 4 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hden 4
    norm_num at hp ⊢
    exact hp
  have hpoly : ‖1 + 4 * t + t ^ 2‖ ≤ 4 := by
    calc
      ‖1 + 4 * t + t ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖4 * t‖ + ‖t ^ 2‖ := by
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = 1 + 4 * ‖t‖ + ‖t‖ ^ 2 := by norm_num
      _ ≤ 4 := by nlinarith [sq_nonneg ‖t‖]
  have hfrac :
      ‖t * (1 + 4 * t + t ^ 2) / (1 - t) ^ 4‖ ≤ 64 * ‖t‖ := by
    rw [norm_div, norm_mul, norm_pow]
    rw [div_le_iff₀ (pow_pos hden0 4)]
    calc
      ‖t‖ * ‖1 + 4 * t + t ^ 2‖ ≤ ‖t‖ * 4 := by
        exact mul_le_mul_of_nonneg_left hpoly ht0
      _ ≤ (64 * ‖t‖) * ‖1 - t‖ ^ 4 := by
        have h64t : 0 ≤ 64 * ‖t‖ := mul_nonneg (by norm_num) ht0
        have hm := mul_le_mul_of_nonneg_left hdenPow h64t
        calc
          ‖t‖ * 4 = (64 * ‖t‖) * (1 / 16) := by ring
          _ ≤ (64 * ‖t‖) * ‖1 - t‖ ^ 4 := hm
  have hzPow : s ^ 4 ≤ ‖z‖ ^ 4 :=
    pow_le_pow_left₀ hs0.le hzNorm 4
  have hzTerm : ‖(6 : ℂ) / z ^ 4‖ ≤ 6 / s ^ 4 := by
    have h6 : ‖(6 : ℂ)‖ = (6 : ℝ) := by norm_num
    rw [norm_div, h6, norm_pow]
    apply div_le_div_of_nonneg_left (by norm_num) (pow_pos hs0 4) hzPow
  have htNorm : ‖t‖ = Real.exp (-s) := by
    dsimp [t]
    rw [Complex.norm_exp]
    have hneg : (-z).re = -s := by simpa using congrArg Neg.neg hzre
    rw [hneg]
  have hexpPow := pow_mul_exp_neg_le_factorial 4 hs0.le
  norm_num at hexpPow
  unfold negativeLaplaceVerticalKernelLogFourth negativeLaplaceComplexKernelFourth
  change ‖((s : ℂ) * Complex.I) ^ 4 *
    (-(t * (1 + 4 * t + t ^ 2)) / (1 - t) ^ 4 + 6 / z ^ 4)‖ ≤ 1542
  rw [norm_mul, norm_pow]
  have hsINorm : ‖(s : ℂ) * Complex.I‖ = s := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0,
      Complex.norm_I, mul_one]
  rw [hsINorm]
  calc
    s ^ 4 * ‖-(t * (1 + 4 * t + t ^ 2)) / (1 - t) ^ 4 + 6 / z ^ 4‖ ≤
        s ^ 4 *
          (‖t * (1 + 4 * t + t ^ 2) / (1 - t) ^ 4‖ +
            ‖(6 : ℂ) / z ^ 4‖) := by
      gcongr
      rw [show -(t * (1 + 4 * t + t ^ 2)) / (1 - t) ^ 4 =
        -(t * (1 + 4 * t + t ^ 2) / (1 - t) ^ 4) by ring]
      simpa only [norm_neg] using norm_add_le
        (-(t * (1 + 4 * t + t ^ 2) / (1 - t) ^ 4)) ((6 : ℂ) / z ^ 4)
    _ ≤ s ^ 4 * (64 * ‖t‖ + 6 / s ^ 4) := by gcongr
    _ = 64 * (s ^ 4 * Real.exp (-s)) + 6 := by
      rw [htNorm]
      field_simp [hs0.ne']
    _ ≤ 1542 := by linarith

private theorem continuous_negativeLaplaceVerticalMoment_pair
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) :
    Continuous (fun p : ℝ × ℝ =>
      negativeLaplaceVerticalMoment F k p.1 p.2) := by
  have hsmooth : ContDiff ℂ (↑(⊤ : ℕ∞))
      (iteratedDeriv k (complexGeneratingFunction F)) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv (𝕜 := ℂ) k
      ((contDiff_complexGeneratingFunction F hF).of_le (by simp))
  exact hsmooth.continuous.comp (by fun_prop)

private theorem continuousAt_normalizedNegativeLaplaceVerticalMoment_pair
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ)
    {p : ℝ × ℝ} (hp : 0 < p.1) :
    ContinuousAt (fun q : ℝ × ℝ =>
      normalizedNegativeLaplaceVerticalMoment F k q.1 q.2) p := by
  unfold normalizedNegativeLaplaceVerticalMoment
  exact (continuous_negativeLaplaceVerticalMoment_pair F hF k).continuousAt.div
    (continuous_negativeLaplaceVerticalMoment_pair F hF 0).continuousAt
    (negativeLaplaceVerticalMoment_ne_zero F hF hp p.2)

private theorem continuousOn_negativeLaplaceVerticalLogFourth_rectangle
    (F : BoundedFabius) (hF : IsFabius F) :
    ContinuousOn (fun p : ℝ × ℝ =>
      negativeLaplaceVerticalLogFourth F p.1 p.2)
      (Icc (1 : ℝ) 2 ×ˢ Icc (-1 : ℝ) 1) := by
  intro p hp
  have hp0 : 0 < p.1 := zero_lt_one.trans_le hp.1.1
  have h1 := continuousAt_normalizedNegativeLaplaceVerticalMoment_pair F hF 1 hp0
  have h2 := continuousAt_normalizedNegativeLaplaceVerticalMoment_pair F hF 2 hp0
  have h3 := continuousAt_normalizedNegativeLaplaceVerticalMoment_pair F hF 3 hp0
  have h4 := continuousAt_normalizedNegativeLaplaceVerticalMoment_pair F hF 4 hp0
  have hc := (((h4.sub ((h1.const_mul 4).mul h3)).sub
    ((h2.pow 2).const_mul 3)).add (((h1.pow 2).const_mul 12).mul h2)).sub
      ((h1.pow 4).const_mul 6)
  have hscale : ContinuousAt (fun q : ℝ × ℝ =>
      (-((q.1 : ℂ) * Complex.I)) ^ 4) p := by fun_prop
  apply ContinuousAt.continuousWithinAt
  unfold negativeLaplaceVerticalLogFourth negativeLaplaceVerticalCumulantFourth
  simp only [Pi.smul_apply, smul_eq_mul]
  exact hscale.mul hc

/-- Iterating the dyadic recurrence bounds the fourth vertical logarithmic
derivative by one fixed compact-base constant plus `1542` per dyadic scale. -/
theorem exists_norm_negativeLaplaceVerticalLogFourth_le_dyadicScales
    (F : BoundedFabius) (hF : IsFabius F) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (m : ℕ) {r θ : ℝ},
      1 ≤ r → r ≤ (2 : ℝ) ^ (m + 1) → |θ| ≤ 1 →
      ‖negativeLaplaceVerticalLogFourth F r θ‖ ≤ A + (m + 1 : ℕ) * 1542 := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      ‖negativeLaplaceVerticalLogFourth F p.1 p.2‖)
      (Icc (1 : ℝ) 2 ×ˢ Icc (-1 : ℝ) 1) :=
    (continuousOn_negativeLaplaceVerticalLogFourth_rectangle F hF).norm
  have hcompact : IsCompact (Icc (1 : ℝ) 2 ×ˢ Icc (-1 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨A₀, hA₀⟩ := bddAbove_def.mp (hcompact.bddAbove_image hcont)
  let A : ℝ := max A₀ 0
  have hA : 0 ≤ A := le_max_right _ _
  have hbase : ∀ {r θ : ℝ}, 1 ≤ r → r ≤ 2 → |θ| ≤ 1 →
      ‖negativeLaplaceVerticalLogFourth F r θ‖ ≤ A := by
    intro r θ hr1 hr2 hθ
    have hθmem : θ ∈ Icc (-1 : ℝ) 1 := (abs_le.mp hθ)
    exact (hA₀ _ ⟨(r, θ), ⟨⟨hr1, hr2⟩, hθmem⟩, rfl⟩).trans
      (le_max_left _ _)
  refine ⟨A, hA, ?_⟩
  intro m
  induction m with
  | zero =>
      intro r θ hr1 hr2 hθ
      norm_num at hr2
      exact (hbase hr1 hr2 hθ).trans (by push_cast; nlinarith [hA])
  | succ m ih =>
      intro r θ hr1 hrUpper hθ
      by_cases hr2 : r ≤ 2
      · exact (hbase hr1 hr2 hθ).trans
          (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (by norm_num)))
      · let s : ℝ := r / 2
        have hs1 : 1 ≤ s := by dsimp [s]; linarith
        have hsUpper : s ≤ (2 : ℝ) ^ (m + 1) := by
          dsimp [s]
          rw [show m + 1 + 1 = (m + 1) + 1 by omega, pow_succ] at hrUpper
          nlinarith
        have hi := ih hs1 hsUpper hθ
        have hk := norm_negativeLaplaceVerticalKernelLogFourth_le hs1 θ
        have hs0 : 0 < s := zero_lt_one.trans_le hs1
        have hrs : r = 2 * s := by dsimp [s]; ring
        rw [hrs, negativeLaplaceVerticalLogFourth_two_mul F hF hs0 θ]
        calc
          ‖negativeLaplaceVerticalKernelLogFourth s θ +
              negativeLaplaceVerticalLogFourth F s θ‖ ≤
              ‖negativeLaplaceVerticalKernelLogFourth s θ‖ +
                ‖negativeLaplaceVerticalLogFourth F s θ‖ := norm_add_le _ _
          _ ≤ 1542 + (A + (m + 1 : ℕ) * 1542) := add_le_add hk hi
          _ = A + (m + 1 + 1 : ℕ) * 1542 := by push_cast; ring

/-- Uniform `O(b + 1)` control of the fourth vertical logarithmic derivative
on the radius `r = 2^b`, throughout the fixed strip `|θ| ≤ 1`, for every
`b ≥ 0`.  The additive one is the natural boundary normalization: at `b = 0`
the radius is the compact-base endpoint `r = 1`, so a pure `C * b` estimate
cannot hold unless the derivative happens to vanish there. -/
theorem exists_norm_negativeLaplaceVerticalLogFourth_rpow_le_add_one
    (F : BoundedFabius) (hF : IsFabius F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {b θ : ℝ}, 0 ≤ b → |θ| ≤ 1 →
      ‖negativeLaplaceVerticalLogFourth F ((2 : ℝ) ^ b) θ‖ ≤ C * (b + 1) := by
  obtain ⟨A, hA, hscale⟩ :=
    exists_norm_negativeLaplaceVerticalLogFourth_le_dyadicScales F hF
  let C : ℝ := A + 2 * 1542
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro b θ hb0 hθ
  let m : ℕ := ⌈b⌉₊
  have hr1 : 1 ≤ (2 : ℝ) ^ b :=
    Real.one_le_rpow (by norm_num) hb0
  have hbceil : b ≤ (m : ℝ) := by
    dsimp [m]
    exact Nat.le_ceil b
  have hbUpper : b ≤ (m + 1 : ℕ) := by
    exact hbceil.trans (by push_cast; linarith)
  have hrUpperRpow : (2 : ℝ) ^ b ≤ (2 : ℝ) ^ ((m + 1 : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hbUpper
  have hrUpper : (2 : ℝ) ^ b ≤ (2 : ℝ) ^ (m + 1) := by
    simpa only [Real.rpow_natCast] using hrUpperRpow
  have hmain := hscale m hr1 hrUpper hθ
  have hmCeil : (m : ℝ) < b + 1 := by
    dsimp [m]
    exact Nat.ceil_lt_add_one hb0
  calc
    ‖negativeLaplaceVerticalLogFourth F ((2 : ℝ) ^ b) θ‖ ≤
        A + (m + 1 : ℕ) * 1542 := hmain
    _ ≤ A + (b + 2) * 1542 := by push_cast; nlinarith
    _ ≤ C * (b + 1) := by
      dsimp [C]
      nlinarith

/-- Uniform `O(b)` control of the fourth vertical logarithmic derivative on
the radius `r = 2^b`, throughout the fixed strip `|θ| ≤ 1`, for `b ≥ 1`.
This retains the original public estimate as a direct corollary of the
all-nonnegative-exponent `O(b + 1)` bound. -/
theorem exists_norm_negativeLaplaceVerticalLogFourth_rpow_le
    (F : BoundedFabius) (hF : IsFabius F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {b θ : ℝ}, 1 ≤ b → |θ| ≤ 1 →
      ‖negativeLaplaceVerticalLogFourth F ((2 : ℝ) ^ b) θ‖ ≤ C * b := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_norm_negativeLaplaceVerticalLogFourth_rpow_le_add_one F hF
  let C : ℝ := 2 * D
  have hC : 0 ≤ C := mul_nonneg (by norm_num) hD
  refine ⟨C, hC, ?_⟩
  intro b θ hb hθ
  have hmain := hbound (zero_le_one.trans hb) hθ
  calc
    ‖negativeLaplaceVerticalLogFourth F ((2 : ℝ) ^ b) θ‖ ≤
        D * (b + 1) := hmain
    _ ≤ C * b := by
      dsimp [C]
      nlinarith

/-- The uniform fourth-derivative bound in the explicit lower-Lambert saddle
coordinates used for the sharp Fabius asymptotic. -/
theorem exists_norm_negativeLaplaceVerticalLogFourth_lambertRadius_le
    (F : BoundedFabius) (hF : IsFabius F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {x θ : ℝ}, 1 ≤ fabiusLambertPhase x → |θ| ≤ 1 →
      ‖negativeLaplaceVerticalLogFourth F (fabiusLambertRadius x) θ‖ ≤
        C * fabiusLambertPhase x := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_negativeLaplaceVerticalLogFourth_rpow_le F hF
  refine ⟨C, hC, ?_⟩
  intro x θ hphase hθ
  simpa only [fabiusLambertRadius] using hbound hphase hθ

end Fabius
