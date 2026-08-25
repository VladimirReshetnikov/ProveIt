import FabiusFunction.FabiusSaddleCentral
import Mathlib.Analysis.Calculus.Taylor

/-!
# Branch-safe Taylor expansion of the vertical negative-Laplace logarithm

Fix `r > 0` and travel along the vertical line `z = -r (1 + i θ)`.  This module
differentiates the branch-safe logarithm `L(r, θ) = negativeLaplaceVerticalLog F r θ`
of `FabiusFunction.NegativeLaplaceVerticalLog` four times in `θ`, and converts those
derivatives into an exact cubic Taylor formula with an integral remainder.

The mechanism is the complex counterpart of
`FabiusFunction.NegativeLaplaceDerivatives`.  Let `M_k(r, θ)` be the `k`th tilted
complex moment, that is the `k`th iterated derivative of `complexGeneratingFunction`
at `-r (1 + i θ)`, and let `R_k = M_k / M_0`.  Differentiating in `θ` gives

`M_k' = (-i r) M_(k+1)`  and  `R_k' = (-i r) (R_(k+1) - R_k R_1)`,

so the first four cumulant polynomials `kappa_1, ..., kappa_4` in the `R_k` satisfy
`kappa_j' = (-i r) kappa_(j+1)` for `j ≤ 3` (the chain stops at `kappa_4`, which is
as far as this module needs it), and the `θ` derivatives of `L` are

`L⁽ʲ⁾(r, θ) = (-i r)ʲ kappa_j(r, θ)`,  for `1 ≤ j ≤ 4`.

At `θ = 0` each `R_k` collapses to the real `normalizedLaplaceMoment F k r`, hence

`L⁽ʲ⁾(r, 0) = (i r)ʲ q⁽ʲ⁾(r)`,

where `q = negativeLaplaceLog` and `q⁽ʲ⁾` runs through `negativeLaplaceLogFirst` to
`negativeLaplaceLogFourth`.  The cubic Taylor polynomial at the real point is
therefore explicit in real-axis data alone.

The module exists to hand the central saddle argument an expansion that never selects
a branch of `Complex.log`: the remainder is an interval integral of the fourth
vertical derivative, so the error is controlled purely by a uniform bound on that one
function.  `FabiusFunction.NegativeLaplaceVerticalFourthBound` produces such a bound
by iterating a dyadic dilation recurrence, and
`FabiusFunction.FabiusSaddleCentralLambert` consumes the cubic together with its
remainder estimate as the central-region exponent.

## Main results

* `negativeLaplaceVerticalMoment`, `normalizedNegativeLaplaceVerticalMoment` -- the
  tilted moments `M_k` and `R_k`, with their derivative rules and `θ = 0` values.
* `negativeLaplaceVerticalCumulantFirst` through `...Fourth` -- the complex cumulants,
  with `kappa_j(r, 0) = (-1)ʲ q⁽ʲ⁾(r)` identifying each one at `θ = 0` with the
  matching `negativeLaplaceLog` derivative.
* `negativeLaplaceVerticalLogFirst` through `...Fourth`, together with the chaining
  lemmas `negativeLaplaceVerticalLogDerivative_eq_cumulant`,
  `negativeLaplaceVerticalLog_hasDerivAt_cumulant`, and
  `iteratedDeriv_negativeLaplaceVerticalLog_one` through `..._four`.
* `contDiff_four_negativeLaplaceVerticalLog` -- `L` is `C⁴` in `θ` for every `r > 0`.
* `negativeLaplaceVerticalCubic` -- the explicit cubic Taylor polynomial, tied to the
  abstract jet form by `negativeLaplaceVerticalCubic_eq`.
* `negativeLaplaceVerticalLog_eq_cubic_add_integralRemainder` and
  `negativeLaplaceVerticalLog_eq_explicitCubic_add_integralRemainder` -- the exact
  Taylor formula with its integral remainder.
* `norm_negativeLaplaceVerticalLog_sub_cubic_le` and
  `norm_negativeLaplaceVerticalLog_sub_explicitCubic_le` -- the remainder bound
  `M * |θ|⁴ / 6` from a uniform bound `M` on the fourth vertical derivative over
  `uIcc 0 θ`.

Conventions and caveats.  Everything about `R_k` and `L` is stated for `r > 0`, which
is what keeps `M_0` nonzero and the normalization legitimate.  The remainder constant
`1/6` is deliberately crude -- the exact integral gives `1/24` -- and is sufficient
rather than sharp.  The smoothness proved here is `C⁴` in `θ` only; all-order vertical
smoothness and derivative bounds live in
`FabiusFunction.NegativeLaplaceVerticalSmooth` and
`FabiusFunction.NegativeLaplaceVerticalAllOrderBound`.
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped Interval Topology

namespace Fabius

/-- The `k`th raw complex tilted moment on the vertical line through `r`. -/
noncomputable def negativeLaplaceVerticalMoment
    (F : BoundedFabius) (k : ℕ) (r θ : ℝ) : ℂ :=
  iteratedDeriv k (complexGeneratingFunction F)
    (-((r : ℂ) * (1 + (θ : ℂ) * Complex.I)))

/-- The corresponding normalized complex tilted moment. -/
noncomputable def normalizedNegativeLaplaceVerticalMoment
    (F : BoundedFabius) (k : ℕ) (r θ : ℝ) : ℂ :=
  negativeLaplaceVerticalMoment F k r θ /
    negativeLaplaceVerticalMoment F 0 r θ

@[simp] lemma negativeLaplaceVerticalMoment_zero
    (F : BoundedFabius) (r θ : ℝ) :
    negativeLaplaceVerticalMoment F 0 r θ =
      negativeLaplaceVerticalCurve F r θ := by
  simp [negativeLaplaceVerticalMoment, negativeLaplaceVerticalCurve]

/-- The zeroth tilted moment `M_0(r, θ)` is nonzero for `r > 0`, which is
what makes the normalization in `normalizedNegativeLaplaceVerticalMoment`
legitimate. -/
lemma negativeLaplaceVerticalMoment_ne_zero
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    negativeLaplaceVerticalMoment F 0 r θ ≠ 0 := by
  rw [negativeLaplaceVerticalMoment_zero]
  exact negativeLaplaceVerticalCurve_ne_zero F hF hr θ

/-- Differentiating the `k`th tilted moment in `θ` raises the index:
`M_k' = M_(k+1) * (-i r)`.  This is the base recurrence of the module; the
normalized and cumulant derivative rules below all reduce to it. -/
lemma negativeLaplaceVerticalMoment_hasDerivAt
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) (r θ : ℝ) :
    HasDerivAt (negativeLaplaceVerticalMoment F k r)
      (negativeLaplaceVerticalMoment F (k + 1) r θ *
        (-((r : ℂ) * Complex.I))) θ := by
  let z : ℝ → ℂ := fun t => -((r : ℂ) * (1 + (t : ℂ) * Complex.I))
  have hz : HasDerivAt z (-((r : ℂ) * Complex.I)) θ := by
    have hlin := (hasDerivAt_id θ).smul_const (-((r : ℂ) * Complex.I))
    have h := (hasDerivAt_const θ (-(r : ℂ))).add hlin
    apply (h.congr_deriv (by simp)).congr_of_eventuallyEq
    filter_upwards with t
    simp only [z, Pi.add_apply, Complex.real_smul, id_eq]
    ring
  have hsmooth : ContDiff ℂ (↑(⊤ : ℕ∞))
      (iteratedDeriv k (complexGeneratingFunction F)) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv (𝕜 := ℂ) k
      ((contDiff_complexGeneratingFunction F hF).of_le (by simp))
  have hout : HasDerivAt (iteratedDeriv k (complexGeneratingFunction F))
      (iteratedDeriv (k + 1) (complexGeneratingFunction F) (z θ)) (z θ) := by
    have hd := (hsmooth.differentiable (by simp) (z θ)).hasDerivAt
    rw [iteratedDeriv_succ]
    exact hd
  have hcomp := ((hout.hasFDerivAt.restrictScalars ℝ).comp θ
    hz.hasFDerivAt).hasDerivAt
  have hcomp' := hcomp.congr_deriv (by
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.toSpanSingleton_apply, one_smul]
    change (-((r : ℂ) * Complex.I)) *
      iteratedDeriv (k + 1) (complexGeneratingFunction F) (z θ) =
        negativeLaplaceVerticalMoment F (k + 1) r θ *
          (-((r : ℂ) * Complex.I))
    unfold negativeLaplaceVerticalMoment
    dsimp only [z]
    ring)
  exact hcomp'.congr_of_eventuallyEq <| by
    filter_upwards with t
    rfl

/-- Quotient rule for the normalized tilted moments at `r > 0`:
`R_k' = (-i r) (R_(k+1) - R_k R_1)`.  Positivity of `r` enters only through
`negativeLaplaceVerticalMoment_ne_zero`, which supplies the nonvanishing
denominator. -/
lemma normalizedNegativeLaplaceVerticalMoment_hasDerivAt
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ)
    {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    HasDerivAt (normalizedNegativeLaplaceVerticalMoment F k r)
      ((-((r : ℂ) * Complex.I)) *
        (normalizedNegativeLaplaceVerticalMoment F (k + 1) r θ -
          normalizedNegativeLaplaceVerticalMoment F k r θ *
            normalizedNegativeLaplaceVerticalMoment F 1 r θ)) θ := by
  have hnum := negativeLaplaceVerticalMoment_hasDerivAt F hF k r θ
  have hden := negativeLaplaceVerticalMoment_hasDerivAt F hF 0 r θ
  have hne := negativeLaplaceVerticalMoment_ne_zero F hF hr θ
  unfold normalizedNegativeLaplaceVerticalMoment
  have hquot := hnum.div hden hne
  refine hquot.congr_deriv ?_
  field_simp [hne]
  ring

@[simp] theorem negativeLaplaceVerticalMoment_at_zero
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) (r : ℝ) :
    negativeLaplaceVerticalMoment F k r 0 =
      (fabiusLaplaceMoment F k r : ℂ) := by
  unfold negativeLaplaceVerticalMoment
  rw [iteratedDeriv_complexGeneratingFunction_eq_integral F hF]
  simp only [Complex.ofReal_zero, zero_mul, add_zero, mul_one]
  calc
    (∫ x : ℝ, (x : ℂ) ^ k * Complex.exp (-(r : ℂ) * x)
        ∂ProbabilityRepresentation.weightedSumDistribution) =
        ∫ x : ℝ, ((Real.exp (-r * x) * x ^ k : ℝ) : ℂ)
          ∂ProbabilityRepresentation.weightedSumDistribution := by
      apply integral_congr_ae
      filter_upwards with x
      have hexp : Complex.exp (-(r : ℂ) * x) =
          (Real.exp (-r * x) : ℂ) := by
        calc
          Complex.exp (-(r : ℂ) * x) =
              Complex.exp ((-r * x : ℝ) : ℂ) := by
            congr 1
            push_cast
            ring
          _ = (Real.exp (-r * x) : ℂ) := (Complex.ofReal_exp _).symm
      rw [hexp]
      push_cast
      ring
    _ = ((∫ x : ℝ, Real.exp (-r * x) * x ^ k
          ∂ProbabilityRepresentation.weightedSumDistribution : ℝ) : ℂ) :=
      integral_ofReal
    _ = (unitLaplaceMoment
          ProbabilityRepresentation.weightedSumDistribution r k : ℂ) := by
      congr 1
      unfold unitLaplaceMoment
      rw [ProbabilityRepresentation.weightedSumDistribution_restrict_Icc]
    _ = (fabiusLaplaceMoment F k r : ℂ) := by
      rw [ProbabilityRepresentation.unitLaplaceMoment_weightedSumDistribution_eq_fabiusLaplaceMoment
        F hF k r]

@[simp] theorem normalizedNegativeLaplaceVerticalMoment_at_zero
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) (r : ℝ) :
    normalizedNegativeLaplaceVerticalMoment F k r 0 =
      (normalizedLaplaceMoment F k r : ℂ) := by
  unfold normalizedNegativeLaplaceVerticalMoment
  rw [negativeLaplaceVerticalMoment_at_zero F hF k r,
    negativeLaplaceVerticalMoment_at_zero F hF 0 r]
  unfold normalizedLaplaceMoment
  push_cast
  rfl

/-- First normalized complex cumulant on a vertical line. -/
noncomputable def negativeLaplaceVerticalCumulantFirst
    (F : BoundedFabius) (r θ : ℝ) : ℂ :=
  normalizedNegativeLaplaceVerticalMoment F 1 r θ

/-- Second normalized complex cumulant on a vertical line. -/
noncomputable def negativeLaplaceVerticalCumulantSecond
    (F : BoundedFabius) (r θ : ℝ) : ℂ :=
  normalizedNegativeLaplaceVerticalMoment F 2 r θ -
    normalizedNegativeLaplaceVerticalMoment F 1 r θ ^ 2

/-- Third normalized complex cumulant on a vertical line. -/
noncomputable def negativeLaplaceVerticalCumulantThird
    (F : BoundedFabius) (r θ : ℝ) : ℂ :=
  normalizedNegativeLaplaceVerticalMoment F 3 r θ -
    3 * normalizedNegativeLaplaceVerticalMoment F 1 r θ *
      normalizedNegativeLaplaceVerticalMoment F 2 r θ +
    2 * normalizedNegativeLaplaceVerticalMoment F 1 r θ ^ 3

/-- Fourth normalized complex cumulant on a vertical line. -/
noncomputable def negativeLaplaceVerticalCumulantFourth
    (F : BoundedFabius) (r θ : ℝ) : ℂ :=
  normalizedNegativeLaplaceVerticalMoment F 4 r θ -
    4 * normalizedNegativeLaplaceVerticalMoment F 1 r θ *
      normalizedNegativeLaplaceVerticalMoment F 3 r θ -
    3 * normalizedNegativeLaplaceVerticalMoment F 2 r θ ^ 2 +
    12 * normalizedNegativeLaplaceVerticalMoment F 1 r θ ^ 2 *
      normalizedNegativeLaplaceVerticalMoment F 2 r θ -
    6 * normalizedNegativeLaplaceVerticalMoment F 1 r θ ^ 4

@[simp] lemma negativeLaplaceVerticalCumulantFirst_at_zero
    (F : BoundedFabius) (hF : IsFabius F) (r : ℝ) :
    negativeLaplaceVerticalCumulantFirst F r 0 =
      (-negativeLaplaceLogFirst F r : ℝ) := by
  unfold negativeLaplaceVerticalCumulantFirst negativeLaplaceLogFirst
  rw [normalizedNegativeLaplaceVerticalMoment_at_zero F hF 1 r]
  push_cast
  ring

@[simp] lemma negativeLaplaceVerticalCumulantSecond_at_zero
    (F : BoundedFabius) (hF : IsFabius F) (r : ℝ) :
    negativeLaplaceVerticalCumulantSecond F r 0 =
      (negativeLaplaceLogSecond F r : ℂ) := by
  unfold negativeLaplaceVerticalCumulantSecond negativeLaplaceLogSecond
  rw [normalizedNegativeLaplaceVerticalMoment_at_zero F hF 1 r,
    normalizedNegativeLaplaceVerticalMoment_at_zero F hF 2 r]
  push_cast
  ring

@[simp] lemma negativeLaplaceVerticalCumulantThird_at_zero
    (F : BoundedFabius) (hF : IsFabius F) (r : ℝ) :
    negativeLaplaceVerticalCumulantThird F r 0 =
      (-negativeLaplaceLogThird F r : ℝ) := by
  unfold negativeLaplaceVerticalCumulantThird negativeLaplaceLogThird
  rw [normalizedNegativeLaplaceVerticalMoment_at_zero F hF 1 r,
    normalizedNegativeLaplaceVerticalMoment_at_zero F hF 2 r,
    normalizedNegativeLaplaceVerticalMoment_at_zero F hF 3 r]
  push_cast
  ring

@[simp] lemma negativeLaplaceVerticalCumulantFourth_at_zero
    (F : BoundedFabius) (hF : IsFabius F) (r : ℝ) :
    negativeLaplaceVerticalCumulantFourth F r 0 =
      (negativeLaplaceLogFourth F r : ℂ) := by
  unfold negativeLaplaceVerticalCumulantFourth negativeLaplaceLogFourth
  rw [normalizedNegativeLaplaceVerticalMoment_at_zero F hF 1 r,
    normalizedNegativeLaplaceVerticalMoment_at_zero F hF 2 r,
    normalizedNegativeLaplaceVerticalMoment_at_zero F hF 3 r,
    normalizedNegativeLaplaceVerticalMoment_at_zero F hF 4 r]
  push_cast
  ring

/-- `kappa_1' = (-i r) kappa_2` in `θ`, for `r > 0`.  First link of the
cumulant chain that produces the `θ` derivatives of the vertical
logarithm. -/
lemma negativeLaplaceVerticalCumulantFirst_hasDerivAt
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    HasDerivAt (negativeLaplaceVerticalCumulantFirst F r)
      ((-((r : ℂ) * Complex.I)) *
        negativeLaplaceVerticalCumulantSecond F r θ) θ := by
  unfold negativeLaplaceVerticalCumulantFirst
  simpa only [negativeLaplaceVerticalCumulantSecond, Nat.reduceAdd,
    pow_two] using
    normalizedNegativeLaplaceVerticalMoment_hasDerivAt F hF 1 hr θ

/-- `kappa_2' = (-i r) kappa_3` in `θ`, for `r > 0`. -/
lemma negativeLaplaceVerticalCumulantSecond_hasDerivAt
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    HasDerivAt (negativeLaplaceVerticalCumulantSecond F r)
      ((-((r : ℂ) * Complex.I)) *
        negativeLaplaceVerticalCumulantThird F r θ) θ := by
  have h1 := normalizedNegativeLaplaceVerticalMoment_hasDerivAt F hF 1 hr θ
  have h2 := normalizedNegativeLaplaceVerticalMoment_hasDerivAt F hF 2 hr θ
  unfold negativeLaplaceVerticalCumulantSecond
  have h := h2.sub (h1.pow 2)
  refine h.congr_deriv ?_
  unfold negativeLaplaceVerticalCumulantThird
  ring

/-- `kappa_3' = (-i r) kappa_4` in `θ`, for `r > 0`.  The chain stops here:
no derivative of `kappa_4` is proved, since `C⁴` is all this module needs. -/
lemma negativeLaplaceVerticalCumulantThird_hasDerivAt
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    HasDerivAt (negativeLaplaceVerticalCumulantThird F r)
      ((-((r : ℂ) * Complex.I)) *
        negativeLaplaceVerticalCumulantFourth F r θ) θ := by
  have h1 := normalizedNegativeLaplaceVerticalMoment_hasDerivAt F hF 1 hr θ
  have h2 := normalizedNegativeLaplaceVerticalMoment_hasDerivAt F hF 2 hr θ
  have h3 := normalizedNegativeLaplaceVerticalMoment_hasDerivAt F hF 3 hr θ
  unfold negativeLaplaceVerticalCumulantThird
  have h := (h3.sub ((h1.mul h2).const_smul (3 : ℝ))).add
    ((h1.pow 3).const_smul (2 : ℝ))
  have h' : HasDerivAt
      (normalizedNegativeLaplaceVerticalMoment F 3 r -
          (3 : ℝ) • (normalizedNegativeLaplaceVerticalMoment F 1 r *
            normalizedNegativeLaplaceVerticalMoment F 2 r) +
        (2 : ℝ) • normalizedNegativeLaplaceVerticalMoment F 1 r ^ 3)
      ((-((r : ℂ) * Complex.I)) *
        negativeLaplaceVerticalCumulantFourth F r θ) θ := h.congr_deriv (by
    unfold negativeLaplaceVerticalCumulantFourth
    simp only [Complex.real_smul]
    norm_num
    ring_nf)
  apply h'.congr_of_eventuallyEq
  filter_upwards with t
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply,
    Pi.pow_apply, Complex.real_smul]
  norm_num
  ring

/-- The vertical logarithmic derivative equals `(-i r) kappa_1`, for every
real `r` and `θ`.  This is the bridge from the curve-quotient definition in
`FabiusFunction.NegativeLaplaceVerticalLog` to the cumulant calculus, and it
is reused by the dyadic dilation identities of
`FabiusFunction.NegativeLaplaceVerticalFourthBound`. -/
lemma negativeLaplaceVerticalLogDerivative_eq_cumulant
    (F : BoundedFabius) (hF : IsFabius F) (r θ : ℝ) :
    negativeLaplaceVerticalLogDerivative F r θ =
      (-((r : ℂ) * Complex.I)) *
        negativeLaplaceVerticalCumulantFirst F r θ := by
  have hzero := negativeLaplaceVerticalMoment_hasDerivAt F hF 0 r θ
  norm_num at hzero
  have hcurve : HasDerivAt (negativeLaplaceVerticalCurve F r)
      (negativeLaplaceVerticalMoment F 1 r θ *
        (-((r : ℂ) * Complex.I))) θ := by
    apply (hzero.congr_deriv (by ring)).congr_of_eventuallyEq
    filter_upwards with t
    exact negativeLaplaceVerticalMoment_zero F r t
  unfold negativeLaplaceVerticalLogDerivative
  rw [hcurve.deriv]
  unfold negativeLaplaceVerticalCumulantFirst
  unfold normalizedNegativeLaplaceVerticalMoment
  rw [negativeLaplaceVerticalMoment_zero]
  ring

/-- First derivative of the branch-safe vertical logarithm. -/
noncomputable def negativeLaplaceVerticalLogFirst
    (F : BoundedFabius) (r : ℝ) : ℝ → ℂ :=
  (-((r : ℂ) * Complex.I)) • negativeLaplaceVerticalCumulantFirst F r

/-- Second derivative of the branch-safe vertical logarithm. -/
noncomputable def negativeLaplaceVerticalLogSecond
    (F : BoundedFabius) (r : ℝ) : ℝ → ℂ :=
  ((-((r : ℂ) * Complex.I)) ^ 2) •
    negativeLaplaceVerticalCumulantSecond F r

/-- Third derivative of the branch-safe vertical logarithm. -/
noncomputable def negativeLaplaceVerticalLogThird
    (F : BoundedFabius) (r : ℝ) : ℝ → ℂ :=
  ((-((r : ℂ) * Complex.I)) ^ 3) •
    negativeLaplaceVerticalCumulantThird F r

/-- Fourth derivative of the branch-safe vertical logarithm. -/
noncomputable def negativeLaplaceVerticalLogFourth
    (F : BoundedFabius) (r : ℝ) : ℝ → ℂ :=
  ((-((r : ℂ) * Complex.I)) ^ 4) •
    negativeLaplaceVerticalCumulantFourth F r

@[simp] lemma negativeLaplaceVerticalLogFirst_apply
    (F : BoundedFabius) (r θ : ℝ) :
    negativeLaplaceVerticalLogFirst F r θ =
      (-((r : ℂ) * Complex.I)) *
        negativeLaplaceVerticalCumulantFirst F r θ := by
  simp [negativeLaplaceVerticalLogFirst, smul_eq_mul]

@[simp] lemma negativeLaplaceVerticalLogSecond_apply
    (F : BoundedFabius) (r θ : ℝ) :
    negativeLaplaceVerticalLogSecond F r θ =
      (-((r : ℂ) * Complex.I)) ^ 2 *
        negativeLaplaceVerticalCumulantSecond F r θ := by
  simp [negativeLaplaceVerticalLogSecond, smul_eq_mul]

@[simp] lemma negativeLaplaceVerticalLogThird_apply
    (F : BoundedFabius) (r θ : ℝ) :
    negativeLaplaceVerticalLogThird F r θ =
      (-((r : ℂ) * Complex.I)) ^ 3 *
        negativeLaplaceVerticalCumulantThird F r θ := by
  simp [negativeLaplaceVerticalLogThird, smul_eq_mul]

@[simp] lemma negativeLaplaceVerticalLogFourth_apply
    (F : BoundedFabius) (r θ : ℝ) :
    negativeLaplaceVerticalLogFourth F r θ =
      (-((r : ℂ) * Complex.I)) ^ 4 *
        negativeLaplaceVerticalCumulantFourth F r θ := by
  simp [negativeLaplaceVerticalLogFourth, smul_eq_mul]

@[simp] theorem negativeLaplaceVerticalLogFirst_at_zero
    (F : BoundedFabius) (hF : IsFabius F) (r : ℝ) :
    negativeLaplaceVerticalLogFirst F r 0 =
      ((r * negativeLaplaceLogFirst F r : ℝ) : ℂ) * Complex.I := by
  rw [negativeLaplaceVerticalLogFirst_apply,
    negativeLaplaceVerticalCumulantFirst_at_zero F hF r]
  push_cast
  ring

@[simp] theorem negativeLaplaceVerticalLogSecond_at_zero
    (F : BoundedFabius) (hF : IsFabius F) (r : ℝ) :
    negativeLaplaceVerticalLogSecond F r 0 =
      ((-(r ^ 2 * negativeLaplaceLogSecond F r) : ℝ) : ℂ) := by
  rw [negativeLaplaceVerticalLogSecond_apply,
    negativeLaplaceVerticalCumulantSecond_at_zero F hF r]
  push_cast
  rw [show -(↑r * Complex.I) = (-↑r) * Complex.I by ring, mul_pow]
  rw [Complex.I_sq]
  ring

@[simp] theorem negativeLaplaceVerticalLogThird_at_zero
    (F : BoundedFabius) (hF : IsFabius F) (r : ℝ) :
    negativeLaplaceVerticalLogThird F r 0 =
      -((r ^ 3 * negativeLaplaceLogThird F r : ℝ) : ℂ) * Complex.I := by
  rw [negativeLaplaceVerticalLogThird_apply,
    negativeLaplaceVerticalCumulantThird_at_zero F hF r]
  push_cast
  rw [show -(↑r * Complex.I) = (-↑r) * Complex.I by ring, mul_pow]
  rw [show Complex.I ^ 3 = -Complex.I by norm_num]
  ring

@[simp] theorem negativeLaplaceVerticalLogFourth_at_zero
    (F : BoundedFabius) (hF : IsFabius F) (r : ℝ) :
    negativeLaplaceVerticalLogFourth F r 0 =
      ((r ^ 4 * negativeLaplaceLogFourth F r : ℝ) : ℂ) := by
  rw [negativeLaplaceVerticalLogFourth_apply,
    negativeLaplaceVerticalCumulantFourth_at_zero F hF r]
  push_cast
  rw [show -(↑r * Complex.I) = (-↑r) * Complex.I by ring, mul_pow]
  rw [show Complex.I ^ 4 = 1 by norm_num]
  ring

/-- For `r > 0` the branch-safe vertical logarithm has `θ` derivative
`negativeLaplaceVerticalLogFirst`.  This restates
`negativeLaplaceVerticalLog_hasDerivAt` in cumulant form and starts the
ladder that `contDiff_four_negativeLaplaceVerticalLog` climbs. -/
lemma negativeLaplaceVerticalLog_hasDerivAt_cumulant
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    HasDerivAt (negativeLaplaceVerticalLog F r)
      (negativeLaplaceVerticalLogFirst F r θ) θ := by
  rw [negativeLaplaceVerticalLogFirst_apply]
  exact (negativeLaplaceVerticalLog_hasDerivAt F hF hr θ).congr_deriv
    (negativeLaplaceVerticalLogDerivative_eq_cumulant F hF r θ)

/-- For `r > 0`, `negativeLaplaceVerticalLogSecond` is the `θ` derivative of
`negativeLaplaceVerticalLogFirst`. -/
lemma negativeLaplaceVerticalLogFirst_hasDerivAt
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    HasDerivAt (negativeLaplaceVerticalLogFirst F r)
      (negativeLaplaceVerticalLogSecond F r θ) θ := by
  have h := (negativeLaplaceVerticalCumulantFirst_hasDerivAt F hF hr θ).const_smul
    (-((r : ℂ) * Complex.I))
  unfold negativeLaplaceVerticalLogFirst
  rw [negativeLaplaceVerticalLogSecond_apply]
  exact h.congr_deriv (by simp only [smul_eq_mul]; ring)

/-- For `r > 0`, `negativeLaplaceVerticalLogThird` is the `θ` derivative of
`negativeLaplaceVerticalLogSecond`. -/
lemma negativeLaplaceVerticalLogSecond_hasDerivAt
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    HasDerivAt (negativeLaplaceVerticalLogSecond F r)
      (negativeLaplaceVerticalLogThird F r θ) θ := by
  have h := (negativeLaplaceVerticalCumulantSecond_hasDerivAt F hF hr θ).const_smul
    ((-((r : ℂ) * Complex.I)) ^ 2)
  unfold negativeLaplaceVerticalLogSecond
  rw [negativeLaplaceVerticalLogThird_apply]
  exact h.congr_deriv (by simp only [smul_eq_mul]; ring)

/-- For `r > 0`, `negativeLaplaceVerticalLogFourth` is the `θ` derivative of
`negativeLaplaceVerticalLogThird`.  Last rung of the ladder used by
`contDiff_four_negativeLaplaceVerticalLog`. -/
lemma negativeLaplaceVerticalLogThird_hasDerivAt
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    HasDerivAt (negativeLaplaceVerticalLogThird F r)
      (negativeLaplaceVerticalLogFourth F r θ) θ := by
  have h := (negativeLaplaceVerticalCumulantThird_hasDerivAt F hF hr θ).const_smul
    ((-((r : ℂ) * Complex.I)) ^ 3)
  unfold negativeLaplaceVerticalLogThird
  rw [negativeLaplaceVerticalLogFourth_apply]
  exact h.congr_deriv (by simp only [smul_eq_mul]; ring)

/-- Each tilted moment `M_k(r, ·)` is `C^∞` in `θ`, for every real `r`.  The
exponent is the coercion of `⊤ : ℕ∞`, that is `C^∞`, and not the analytic
exponent `ω`. -/
theorem contDiff_negativeLaplaceVerticalMoment
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) (r : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (negativeLaplaceVerticalMoment F k r) := by
  unfold negativeLaplaceVerticalMoment
  have houter : ContDiff ℂ (↑(⊤ : ℕ∞))
      (iteratedDeriv k (complexGeneratingFunction F)) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv (𝕜 := ℂ) k
      ((contDiff_complexGeneratingFunction F hF).of_le (by simp))
  have hinner : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun θ : ℝ => -((r : ℂ) * (1 + (θ : ℂ) * Complex.I))) := by
    have hθ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun θ : ℝ => (θ : ℂ)) :=
      Complex.ofRealCLM.contDiff
    exact (contDiff_const.mul
      (contDiff_const.add (hθ.mul contDiff_const))).neg
  exact (houter.restrict_scalars ℝ).comp hinner

/-- The normalized tilted moment `R_k(r, ·)` is continuous in `θ` for
`r > 0`, read off from its derivative rule.  It feeds the continuity of the
fourth vertical derivative. -/
theorem continuous_normalizedNegativeLaplaceVerticalMoment
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ)
    {r : ℝ} (hr : 0 < r) :
    Continuous (normalizedNegativeLaplaceVerticalMoment F k r) := by
  rw [continuous_iff_continuousAt]
  intro θ
  exact (normalizedNegativeLaplaceVerticalMoment_hasDerivAt F hF k hr θ).continuousAt

/-- The fourth vertical derivative is continuous in `θ` for `r > 0`, being a
polynomial in the continuous normalized moments `R_1, ..., R_4`.  This is the
`C⁰` bottom of the ladder in `contDiff_four_negativeLaplaceVerticalLog`. -/
theorem continuous_negativeLaplaceVerticalLogFourth
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) :
    Continuous (negativeLaplaceVerticalLogFourth F r) := by
  have h1 := continuous_normalizedNegativeLaplaceVerticalMoment F hF 1 hr
  have h2 := continuous_normalizedNegativeLaplaceVerticalMoment F hF 2 hr
  have h3 := continuous_normalizedNegativeLaplaceVerticalMoment F hF 3 hr
  have h4 := continuous_normalizedNegativeLaplaceVerticalMoment F hF 4 hr
  unfold negativeLaplaceVerticalLogFourth negativeLaplaceVerticalCumulantFourth
  fun_prop

/-- For `r > 0` the branch-safe vertical logarithm is `C⁴` in `θ`.  Only
four derivatives are claimed, which is exactly the regularity that Mathlib's
`taylor_integral_remainder` needs for the cubic expansion below; all-order
vertical smoothness lives in
`FabiusFunction.NegativeLaplaceVerticalSmooth`. -/
theorem contDiff_four_negativeLaplaceVerticalLog
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ 4 (negativeLaplaceVerticalLog F r) := by
  have hcont4 : ContDiff ℝ 0 (negativeLaplaceVerticalLogFourth F r) :=
    contDiff_zero.mpr (continuous_negativeLaplaceVerticalLogFourth F hF hr)
  have hdiff3 : Differentiable ℝ (negativeLaplaceVerticalLogThird F r) :=
    fun θ => (negativeLaplaceVerticalLogThird_hasDerivAt F hF hr θ).differentiableAt
  have hderiv3 : deriv (negativeLaplaceVerticalLogThird F r) =
      negativeLaplaceVerticalLogFourth F r := by
    funext θ
    exact (negativeLaplaceVerticalLogThird_hasDerivAt F hF hr θ).deriv
  have hcont3 : ContDiff ℝ 1 (negativeLaplaceVerticalLogThird F r) := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num, contDiff_succ_iff_deriv]
    exact ⟨hdiff3, by simp, by simpa [hderiv3] using hcont4⟩
  have hdiff2 : Differentiable ℝ (negativeLaplaceVerticalLogSecond F r) :=
    fun θ => (negativeLaplaceVerticalLogSecond_hasDerivAt F hF hr θ).differentiableAt
  have hderiv2 : deriv (negativeLaplaceVerticalLogSecond F r) =
      negativeLaplaceVerticalLogThird F r := by
    funext θ
    exact (negativeLaplaceVerticalLogSecond_hasDerivAt F hF hr θ).deriv
  have hcont2 : ContDiff ℝ 2 (negativeLaplaceVerticalLogSecond F r) := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
    exact ⟨hdiff2, by simp, by simpa [hderiv2] using hcont3⟩
  have hdiff1 : Differentiable ℝ (negativeLaplaceVerticalLogFirst F r) :=
    fun θ => (negativeLaplaceVerticalLogFirst_hasDerivAt F hF hr θ).differentiableAt
  have hderiv1 : deriv (negativeLaplaceVerticalLogFirst F r) =
      negativeLaplaceVerticalLogSecond F r := by
    funext θ
    exact (negativeLaplaceVerticalLogFirst_hasDerivAt F hF hr θ).deriv
  have hcont1 : ContDiff ℝ 3 (negativeLaplaceVerticalLogFirst F r) := by
    rw [show (3 : WithTop ℕ∞) = 2 + 1 by norm_num, contDiff_succ_iff_deriv]
    exact ⟨hdiff1, by simp, by simpa [hderiv1] using hcont2⟩
  have hdiff0 : Differentiable ℝ (negativeLaplaceVerticalLog F r) :=
    fun θ => (negativeLaplaceVerticalLog_hasDerivAt_cumulant F hF hr θ).differentiableAt
  have hderiv0 : deriv (negativeLaplaceVerticalLog F r) =
      negativeLaplaceVerticalLogFirst F r := by
    funext θ
    exact (negativeLaplaceVerticalLog_hasDerivAt_cumulant F hF hr θ).deriv
  rw [show (4 : WithTop ℕ∞) = 3 + 1 by norm_num, contDiff_succ_iff_deriv]
  exact ⟨hdiff0, by simp, by simpa [hderiv0] using hcont1⟩

@[simp] theorem iteratedDeriv_negativeLaplaceVerticalLog_one
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    iteratedDeriv 1 (negativeLaplaceVerticalLog F r) θ =
      negativeLaplaceVerticalLogFirst F r θ := by
  rw [iteratedDeriv_one]
  exact (negativeLaplaceVerticalLog_hasDerivAt_cumulant F hF hr θ).deriv

@[simp] theorem iteratedDeriv_negativeLaplaceVerticalLog_two
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    iteratedDeriv 2 (negativeLaplaceVerticalLog F r) θ =
      negativeLaplaceVerticalLogSecond F r θ := by
  rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ]
  have heq : iteratedDeriv 1 (negativeLaplaceVerticalLog F r) =
      negativeLaplaceVerticalLogFirst F r := by
    funext t
    exact iteratedDeriv_negativeLaplaceVerticalLog_one F hF hr t
  rw [heq]
  exact (negativeLaplaceVerticalLogFirst_hasDerivAt F hF hr θ).deriv

@[simp] theorem iteratedDeriv_negativeLaplaceVerticalLog_three
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    iteratedDeriv 3 (negativeLaplaceVerticalLog F r) θ =
      negativeLaplaceVerticalLogThird F r θ := by
  rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ]
  have heq : iteratedDeriv 2 (negativeLaplaceVerticalLog F r) =
      negativeLaplaceVerticalLogSecond F r := by
    funext t
    exact iteratedDeriv_negativeLaplaceVerticalLog_two F hF hr t
  rw [heq]
  exact (negativeLaplaceVerticalLogSecond_hasDerivAt F hF hr θ).deriv

@[simp] theorem iteratedDeriv_negativeLaplaceVerticalLog_four
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    iteratedDeriv 4 (negativeLaplaceVerticalLog F r) θ =
      negativeLaplaceVerticalLogFourth F r θ := by
  rw [show 4 = 3 + 1 by norm_num, iteratedDeriv_succ]
  have heq : iteratedDeriv 3 (negativeLaplaceVerticalLog F r) =
      negativeLaplaceVerticalLogThird F r := by
    funext t
    exact iteratedDeriv_negativeLaplaceVerticalLog_three F hF hr t
  rw [heq]
  exact (negativeLaplaceVerticalLogThird_hasDerivAt F hF hr θ).deriv

/-- The explicit cubic Taylor polynomial of the vertical logarithm, expressed using the real-axis
derivatives of `negativeLaplaceLog`. -/
noncomputable def negativeLaplaceVerticalCubic
    (F : BoundedFabius) (r θ : ℝ) : ℂ :=
  ((r * negativeLaplaceLogFirst F r * θ : ℝ) : ℂ) * Complex.I -
    ((r ^ 2 * negativeLaplaceLogSecond F r * θ ^ 2 / 2 : ℝ) : ℂ) -
    ((r ^ 3 * negativeLaplaceLogThird F r * θ ^ 3 / 6 : ℝ) : ℂ) * Complex.I

/-- The explicit cubic agrees with the abstract third-order jet of `L` at
`θ = 0`, that is with the polynomial built from
`negativeLaplaceVerticalLogFirst`, `...Second`, and `...Third` evaluated at
`θ = 0`.  This is the translation step between the two Taylor statements
below. -/
theorem negativeLaplaceVerticalCubic_eq
    (F : BoundedFabius) (hF : IsFabius F) (r θ : ℝ) :
    negativeLaplaceVerticalCubic F r θ =
      θ • negativeLaplaceVerticalLogFirst F r 0 +
      (θ ^ 2 / 2) • negativeLaplaceVerticalLogSecond F r 0 +
      (θ ^ 3 / 6) • negativeLaplaceVerticalLogThird F r 0 := by
  rw [negativeLaplaceVerticalLogFirst_at_zero F hF r,
    negativeLaplaceVerticalLogSecond_at_zero F hF r,
    negativeLaplaceVerticalLogThird_at_zero F hF r]
  unfold negativeLaplaceVerticalCubic
  simp only [Complex.real_smul]
  push_cast
  ring

/-- Exact cubic Taylor formula for the branch-safe vertical logarithm.  The remainder is written
as an integral of the fourth vertical cumulant, so no choice of `Complex.log` is involved. -/
theorem negativeLaplaceVerticalLog_eq_cubic_add_integralRemainder
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    negativeLaplaceVerticalLog F r θ =
      θ • negativeLaplaceVerticalLogFirst F r 0 +
      (θ ^ 2 / 2) • negativeLaplaceVerticalLogSecond F r 0 +
      (θ ^ 3 / 6) • negativeLaplaceVerticalLogThird F r 0 +
      ∫ t in (0 : ℝ)..θ, ((θ - t) ^ 3 / 6) •
        negativeLaplaceVerticalLogFourth F r t := by
  by_cases hθ : θ = 0
  · subst θ
    simp
  have hcont := contDiff_four_negativeLaplaceVerticalLog F hF hr
  have huniq : UniqueDiffOn ℝ (uIcc (0 : ℝ) θ) :=
    uniqueDiffOn_uIcc (fun h => hθ h.symm)
  have hwithin (k : ℕ) (hk : k ≤ 4) (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) θ) :
      iteratedDerivWithin k (negativeLaplaceVerticalLog F r) (uIcc 0 θ) t =
        iteratedDeriv k (negativeLaplaceVerticalLog F r) t := by
    apply iteratedDerivWithin_eq_iteratedDeriv huniq
      ((hcont.of_le (by exact_mod_cast hk)).contDiffAt) ht
  have hwithin0 (k : ℕ) (hk : k ≤ 4) :
      iteratedDerivWithin k (negativeLaplaceVerticalLog F r) (uIcc 0 θ) 0 =
        iteratedDeriv k (negativeLaplaceVerticalLog F r) 0 :=
    hwithin k hk 0 left_mem_uIcc
  have htaylor :
      taylorWithinEval (negativeLaplaceVerticalLog F r) 3 (uIcc 0 θ) 0 θ =
        θ • negativeLaplaceVerticalLogFirst F r 0 +
        (θ ^ 2 / 2) • negativeLaplaceVerticalLogSecond F r 0 +
        (θ ^ 3 / 6) • negativeLaplaceVerticalLogThird F r 0 := by
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ]
    rw [hwithin0 0 (by norm_num), hwithin0 1 (by norm_num),
      hwithin0 2 (by norm_num), hwithin0 3 (by norm_num)]
    simp only [iteratedDeriv_zero, negativeLaplaceVerticalLog_zero,
      iteratedDeriv_negativeLaplaceVerticalLog_one F hF hr,
      iteratedDeriv_negativeLaplaceVerticalLog_two F hF hr,
      iteratedDeriv_negativeLaplaceVerticalLog_three F hF hr]
    norm_num
    ring
  have hremainder :
      (∫ t in (0 : ℝ)..θ,
          ((θ - t) ^ 3 / (3 : ℕ).factorial) •
            iteratedDerivWithin 4 (negativeLaplaceVerticalLog F r)
              (uIcc 0 θ) t) =
        ∫ t in (0 : ℝ)..θ, ((θ - t) ^ 3 / 6) •
          negativeLaplaceVerticalLogFourth F r t := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [hwithin 4 (by norm_num) t ht,
      iteratedDeriv_negativeLaplaceVerticalLog_four F hF hr]
    norm_num
  have ht := taylor_integral_remainder (n := 3)
    (show ContDiffOn ℝ (↑(3 + 1 : ℕ)) (negativeLaplaceVerticalLog F r)
        (uIcc 0 θ) by simpa using hcont.contDiffOn)
  rw [htaylor, hremainder] at ht
  exact sub_eq_iff_eq_add'.mp ht

/-- Exact cubic Taylor formula in explicit form: `L(r, θ)` is
`negativeLaplaceVerticalCubic` plus the same integral remainder in the fourth
vertical derivative, so the cubic part is written purely in real-axis
data. -/
theorem negativeLaplaceVerticalLog_eq_explicitCubic_add_integralRemainder
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    negativeLaplaceVerticalLog F r θ =
      negativeLaplaceVerticalCubic F r θ +
      ∫ t in (0 : ℝ)..θ, ((θ - t) ^ 3 / 6) •
        negativeLaplaceVerticalLogFourth F r t := by
  rw [negativeLaplaceVerticalCubic_eq F hF]
  exact negativeLaplaceVerticalLog_eq_cubic_add_integralRemainder F hF hr θ

/-- A uniform fourth-vertical-derivative bound gives a branch-safe cubic Taylor remainder.  The
constant `1/6` is deliberately simple (the exact integral gives `1/24` after a sharper
calculation); this form is sufficient for the corrected saddle estimate. -/
theorem norm_negativeLaplaceVerticalLog_sub_cubic_le
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r)
    (θ M : ℝ)
    (hM : ∀ t ∈ uIcc (0 : ℝ) θ,
      ‖negativeLaplaceVerticalLogFourth F r t‖ ≤ M) :
    ‖negativeLaplaceVerticalLog F r θ -
      (θ • negativeLaplaceVerticalLogFirst F r 0 +
       (θ ^ 2 / 2) • negativeLaplaceVerticalLogSecond F r 0 +
       (θ ^ 3 / 6) • negativeLaplaceVerticalLogThird F r 0)‖ ≤
      M * |θ| ^ 4 / 6 := by
  have hdist (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) θ) : |θ - t| ≤ |θ| := by
    rcases le_total 0 θ with hθ | hθ
    · rw [uIcc_of_le hθ] at ht
      rw [abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg hθ]
      exact sub_le_self θ ht.1
    · rw [uIcc_of_ge hθ] at ht
      rw [abs_of_nonpos (sub_nonpos.mpr ht.1), abs_of_nonpos hθ]
      calc
        -(θ - t) = t - θ := by ring
        _ ≤ 0 - θ := sub_le_sub_right ht.2 θ
        _ = -θ := by ring
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := θ) (C := M * |θ| ^ 3 / 6)
    (f := fun t => ((θ - t) ^ 3 / 6) •
      negativeLaplaceVerticalLogFourth F r t) (by
      intro t ht
      have ht' : t ∈ uIcc (0 : ℝ) θ := uIoc_subset_uIcc ht
      rw [norm_smul, Real.norm_eq_abs, abs_div, abs_pow,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
      calc
        |θ - t| ^ 3 / 6 * ‖negativeLaplaceVerticalLogFourth F r t‖
            ≤ |θ| ^ 3 / 6 * M := by
              apply mul_le_mul
              · exact div_le_div_of_nonneg_right
                  (pow_le_pow_left₀ (abs_nonneg _) (hdist t ht') 3) (by norm_num)
              · exact hM t ht'
              · exact norm_nonneg _
              · exact div_nonneg (pow_nonneg (abs_nonneg θ) 3) (by norm_num)
        _ = M * |θ| ^ 3 / 6 := by ring)
  rw [negativeLaplaceVerticalLog_eq_cubic_add_integralRemainder F hF hr]
  rw [add_sub_cancel_left]
  calc
    ‖∫ t in (0 : ℝ)..θ, ((θ - t) ^ 3 / 6) •
        negativeLaplaceVerticalLogFourth F r t‖
        ≤ (M * |θ| ^ 3 / 6) * |θ - 0| := hint
    _ = M * |θ| ^ 4 / 6 := by
      rw [sub_zero]
      ring

/-- Explicit-cubic form of the remainder bound: a uniform bound `M` on the
fourth vertical derivative over `uIcc 0 θ` gives
`‖L(r, θ) - negativeLaplaceVerticalCubic F r θ‖ ≤ M * |θ|⁴ / 6`.  The
constant `1/6` is sufficient rather than sharp.  This is the form consumed by
`norm_exponentRemainder_le` in
`FabiusFunction.FabiusSaddleCentralLambert`. -/
theorem norm_negativeLaplaceVerticalLog_sub_explicitCubic_le
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r)
    (θ M : ℝ)
    (hM : ∀ t ∈ uIcc (0 : ℝ) θ,
      ‖negativeLaplaceVerticalLogFourth F r t‖ ≤ M) :
    ‖negativeLaplaceVerticalLog F r θ - negativeLaplaceVerticalCubic F r θ‖ ≤
      M * |θ| ^ 4 / 6 := by
  rw [negativeLaplaceVerticalCubic_eq F hF]
  exact norm_negativeLaplaceVerticalLog_sub_cubic_le F hF hr θ M hM

end Fabius
