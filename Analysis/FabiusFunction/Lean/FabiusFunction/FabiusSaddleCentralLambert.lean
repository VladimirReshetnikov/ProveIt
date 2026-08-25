import FabiusFunction.FabiusLambertDerivativeBounds
import FabiusFunction.NegativeLaplaceVerticalFourthBound
import FabiusFunction.FabiusLambertMinorArc
import FabiusFunction.FabiusSaddleReferenceTail
import FabiusFunction.FabiusSaddleReduction
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# The central Fabius saddle at the explicit dyadic Lambert radius

This module runs the quantitative central saddle estimate for the Fabius
generating function on the single concrete orbit the sharp theory needs: the
argument `x = 2 ^ (-t)`, the radius `r = fabiusLambertRadius x = 2 ^ b`, and
the Gaussian scale `b = fabiusLambertPhase x = dyadicLambertPhase t`, the
lower-Lambert phase solving the saddle equation `r * x = b`.  After the
Bromwich substitution `z = r * (1 + i * v / sqrt b)` the normalized integrand
is `QuantitativeSaddle.scaledSaddleKernel`, and the content here is its exact
factorization

`K v = exp (-v ^ 2 / 2) * exp (i * (a * v + c * v ^ 3) + R v)`,

whose odd coefficients are, writing `q` for `negativeLaplaceLog`,

`a = (r * x + r * q' r - 1) / sqrt b`,
`c = (2 - r ^ 3 * q''' r) / (6 * b * sqrt b)`.

Three sources feed that exponent: the tilt `exp (i * r * x * v / sqrt b)`, the
branch-safe vertical logarithm `negativeLaplaceVerticalLog`, and the Bromwich
denominator `-log (1 + i * theta)` at `theta = v / sqrt b`.  Each is expanded
to cubic order and the leftovers are collected into `exponentRemainder`.

The module is the bridge between the generic saddle machinery and the
Fabius-specific input it needs.  `FabiusFunction.FabiusSaddleCentral` proves
the central `L^1` estimate for an abstract kernel obeying such hypotheses, and
`FabiusFunction.FabiusSaddleReferenceTail` with
`FabiusFunction.FabiusLambertMinorArc` covers the complementary outer region;
what was missing was a proof that the genuine Fabius kernel at the genuine
Lambert saddle obeys them.  Supplying it produces the one statement the sharp
small-argument theory consumes: the normalized kernel mass is `1 + O(1 / b)`.

## Main results

* `scaledSaddleKernel_eq_gaussian_exp` -- the exact factorization displayed
  above, for arbitrary `r, b > 0` and every `v`; no saddle equation is used.
* `norm_exponentRemainder_le` -- the quadratic-plus-quartic remainder bound
  `((Csecond + 1) / 2 * v ^ 2 + (Cfourth / 6 + 1 / 2) * v ^ 4) / b`, valid for
  `1 <= b` and `|v / sqrt b| <= 1 / 2`, from a curvature defect bound and a
  uniform fourth vertical derivative bound.
* `linearCoefficient_rpow_eq` and `cubicCoefficient_rpow_eq` -- the odd
  coefficients at radius `2 ^ b` rewritten through
  `negativeLaplaceRpowFirstResidual` and `negativeLaplaceRpowThirdResidual`;
  the linear rewrite needs the saddle equation `2 ^ b * x = b`, the cubic one
  is unconditional.
* `exists_rpow_coefficient_bounds` -- uniform `b * a ^ 2 <= Clinear ^ 2` and
  `b * c ^ 2 <= Ccubic ^ 2` along the dyadic orbit, which is the exact
  normalization the generic central theorem asks for.
* `dyadicLambertKernel`, together with `dyadicLambertLinearCoefficient`,
  `dyadicLambertCubicCoefficient` and `dyadicLambertExponentRemainder` -- the
  specializations to `x = 2 ^ (-t)`.  `dyadicLambertKernel` is the corpus-wide
  name for this kernel and is reused verbatim by
  `FabiusFunction.FabiusSaddleCentralAllOrders` and
  `FabiusFunction.FabiusSaddleMassAllOrders`.
* `dyadicLambert_central_corrected_error_isBigO` -- the central `L^1` error
  against `standardGaussian + oddCorrection` is `O(1 / b)`.
* `fabiusSaddleKernelMass_dyadicLambert_sub_one_isBigO` -- the headline
  result `fabiusSaddleKernelMass F (2 ^ (-t)) r b - 1 = O(1 / b)`, the final
  analytic input of `FabiusFunction.FabiusSharpAsymptotic`.

The remaining public declarations are the definitions named in the formulas
above (`denominatorCubic`, `denominatorRemainder`, `linearCoefficient`,
`cubicCoefficient`, `curvatureRemainder`, `exponentRemainder`) and the cubic
Taylor bound `norm_denominatorRemainder_le`.  Most of the private lemmas are
decay bookkeeping at the standard radius
`fabiusSaddleCentralRadius b = sqrt (32 * log b)`: there the odd phase and the
exponent remainder are eventually at most `1`, and `v / sqrt b` eventually
stays within `1 / 2` of the origin.  The two remaining private results
transport the coefficient bounds onto the dyadic orbit and glue the central
and tail estimates into the normalized mass.

## Conventions and caveats

The Gaussian scale is taken to be the Lambert phase `b` itself rather than the
exact curvature `1 + r ^ 2 * q'' r` of the exponent.  That mismatch is real
and is carried by `curvatureRemainder`; it is why the quadratic constant reads
`(Csecond + 1) / 2` and not `Csecond / 2`, the extra `1` being the curvature
contributed by the Bromwich denominator itself.

`norm_denominatorRemainder_le` is stated only for `|theta| <= 1 / 2`, which
keeps `1 + i * theta` inside the principal branch and makes the geometric
majorant available; the radius lemmas exist to check that the standard radius
eventually satisfies it.  Every `atTop` statement is eventual in `t`, with no
uniformity claimed for small `t`, and every constant produced here is
sufficient rather than sharp.
-/

set_option autoImplicit false

open Filter Set MeasureTheory Asymptotics
open scoped Topology

namespace Fabius

namespace SaddleLambert

/-- Cubic Taylor polynomial of `-log (1 + i theta)`. -/
noncomputable def denominatorCubic (theta : ℝ) : ℂ :=
  -((theta : ℂ) * Complex.I) - (theta : ℂ) ^ 2 / 2 +
    (theta : ℂ) ^ 3 * Complex.I / 3

/-- The branch-safe remainder in `-log (1 + i theta)`. -/
noncomputable def denominatorRemainder (theta : ℝ) : ℂ :=
  -Complex.log (1 + (theta : ℂ) * Complex.I) - denominatorCubic theta

/-- Quartic bound on `denominatorRemainder`, the remainder of
`-log (1 + i theta)` past its cubic Taylor polynomial, stated only for
`|theta| ≤ 1 / 2`:
`‖denominatorRemainder theta‖ ≤ (1 / 2) * |theta| ^ 4`.  The restriction
keeps `1 + i theta` inside the principal branch and makes the geometric
majorant `(1 - |theta|)⁻¹ ≤ 2` available.  The constant `1 / 2` is
sufficient, not sharp.  Used by `norm_exponentRemainder_le` below. -/
lemma norm_denominatorRemainder_le {theta : ℝ} (htheta : |theta| ≤ 1 / 2) :
    ‖denominatorRemainder theta‖ ≤ (1 / 2 : ℝ) * |theta| ^ 4 := by
  have hz : ‖(theta : ℂ) * Complex.I‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    linarith
  have h := Complex.norm_log_sub_logTaylor_le 3 hz
  have hpoly : Complex.logTaylor 4 ((theta : ℂ) * Complex.I) =
      (theta : ℂ) * Complex.I + (theta : ℂ) ^ 2 / 2 -
        (theta : ℂ) ^ 3 * Complex.I / 3 := by
    have hI2 : Complex.I ^ 2 = -(1 : ℂ) := by
      rw [sq, Complex.I_mul_I]
    have hI3 : Complex.I ^ 3 = -Complex.I := by
      rw [pow_succ, hI2]
      ring
    simp [Complex.logTaylor_succ, Complex.logTaylor_zero]
    rw [mul_pow, mul_pow]
    rw [hI2, hI3]
    ring
  rw [hpoly] at h
  norm_num at h
  have heq : denominatorRemainder theta =
      -(Complex.log (1 + (theta : ℂ) * Complex.I) -
        ((theta : ℂ) * Complex.I + (theta : ℂ) ^ 2 / 2 -
          (theta : ℂ) ^ 3 * Complex.I / 3)) := by
    unfold denominatorRemainder denominatorCubic
    ring
  rw [heq, norm_neg]
  calc
    ‖Complex.log (1 + (theta : ℂ) * Complex.I) -
        ((theta : ℂ) * Complex.I + (theta : ℂ) ^ 2 / 2 -
          (theta : ℂ) ^ 3 * Complex.I / 3)‖ ≤
        |theta| ^ 4 * (1 - |theta|)⁻¹ / 4 := h
    _ ≤ (1 / 2 : ℝ) * |theta| ^ 4 := by
      have hden : (1 - |theta|)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith [abs_nonneg theta]) (by norm_num : (0 : ℝ) < 2)]
        linarith
      nlinarith [pow_nonneg (abs_nonneg theta) 4]

/-- Scaled coefficient of the odd linear saddle phase. -/
noncomputable def linearCoefficient
    (F : BoundedFabius) (x r b : ℝ) : ℝ :=
  (r * x + r * negativeLaplaceLogFirst F r - 1) / Real.sqrt b

/-- Scaled coefficient of the odd cubic saddle phase. -/
noncomputable def cubicCoefficient
    (F : BoundedFabius) (r b : ℝ) : ℝ :=
  (2 - r ^ 3 * negativeLaplaceLogThird F r) /
    (6 * b * Real.sqrt b)

/-- Even curvature defect from replacing the exact quadratic term by the
standard Gaussian exponent. -/
noncomputable def curvatureRemainder
    (F : BoundedFabius) (r b v : ℝ) : ℂ :=
  (((b - (1 + r ^ 2 * negativeLaplaceLogSecond F r)) * v ^ 2 /
    (2 * b) : ℝ) : ℂ)

/-- Full central exponent remainder after extracting the Gaussian and the
odd linear-plus-cubic phase. -/
noncomputable def exponentRemainder
    (F : BoundedFabius) (r b v : ℝ) : ℂ :=
  (negativeLaplaceVerticalLog F r (v / Real.sqrt b) -
      negativeLaplaceVerticalCubic F r (v / Real.sqrt b)) +
    denominatorRemainder (v / Real.sqrt b) +
    curvatureRemainder F r b v

/-- Exact factorization of the scaled Bromwich kernel of the negated Fabius
generating function: for `0 < r`, `0 < b` and every real `x` and `v`, the
kernel equals `standardGaussian v` times the exponential of
`oddPhase (linearCoefficient F x r b) (cubicCoefficient F r b) v +
exponentRemainder F r b v`.  This is an identity rather than an estimate:
no saddle equation linking `x`, `r` and `b` is assumed, and every mismatch
is absorbed into `exponentRemainder`.  Requires `IsFabius F`. -/
lemma scaledSaddleKernel_eq_gaussian_exp
    (F : BoundedFabius) (hF : IsFabius F)
    (x r b v : ℝ) (hr : 0 < r) (hb : 0 < b) :
    QuantitativeSaddle.scaledSaddleKernel
        (fun z => complexGeneratingFunction F (-z)) x r b v =
      QuantitativeSaddle.standardGaussian v *
        Complex.exp
          (SaddleCentral.oddPhase (linearCoefficient F x r b)
              (cubicCoefficient F r b) v +
            exponentRemainder F r b v) := by
  let theta : ℝ := v / Real.sqrt b
  let w : ℂ := 1 + (theta : ℂ) * Complex.I
  have hsqrt : Real.sqrt b ≠ 0 := (Real.sqrt_pos.2 hb).ne'
  have hw : w ≠ 0 := by
    apply (norm_one_add_mul_I_pos theta).ne'.comp norm_eq_zero.mpr
  have hcurve0 : negativeLaplaceVerticalCurve F r 0 =
      complexGeneratingFunction F (-(r : ℂ)) := by
    simp [negativeLaplaceVerticalCurve]
  have hcurve : negativeLaplaceVerticalCurve F r theta =
      complexGeneratingFunction F
        (-((r : ℂ) + ((r * v / Real.sqrt b : ℝ) : ℂ) * Complex.I)) := by
    unfold negativeLaplaceVerticalCurve
    dsimp [theta]
    congr 2
    push_cast
    ring
  have hratio :
      complexGeneratingFunction F
          (-((r : ℂ) + ((r * v / Real.sqrt b : ℝ) : ℂ) * Complex.I)) /
        complexGeneratingFunction F (-(r : ℂ)) =
      Complex.exp (negativeLaplaceVerticalLog F r theta) := by
    rw [← hcurve, ← hcurve0]
    exact (exp_negativeLaplaceVerticalLog F hF hr theta).symm
  have hden : w⁻¹ = Complex.exp (-Complex.log w) := by
    rw [Complex.exp_neg, Complex.exp_log hw]
  unfold QuantitativeSaddle.scaledSaddleKernel
  rw [show (fun z => complexGeneratingFunction F (-z))
      ((r : ℂ) + ((r * v / Real.sqrt b : ℝ) : ℂ) * Complex.I) =
      complexGeneratingFunction F
        (-((r : ℂ) + ((r * v / Real.sqrt b : ℝ) : ℂ) * Complex.I)) by rfl]
  change Complex.exp ((((r * x * v / Real.sqrt b : ℝ) : ℂ) * Complex.I)) *
      (complexGeneratingFunction F
          (-((r : ℂ) + ((r * v / Real.sqrt b : ℝ) : ℂ) * Complex.I)) /
        complexGeneratingFunction F (-(r : ℂ))) /
      (1 + ((v / Real.sqrt b : ℝ) : ℂ) * Complex.I) = _
  rw [hratio]
  change Complex.exp ((((r * x * v / Real.sqrt b : ℝ) : ℂ) * Complex.I)) *
      Complex.exp (negativeLaplaceVerticalLog F r theta) * w⁻¹ = _
  rw [hden, ← Complex.exp_add, ← Complex.exp_add]
  rw [show QuantitativeSaddle.standardGaussian v =
      Complex.exp (((-(v ^ 2) / 2 : ℝ) : ℂ)) by
    rw [QuantitativeSaddle.standardGaussian, Complex.ofReal_exp],
    ← Complex.exp_add]
  congr 1
  unfold SaddleCentral.oddPhase exponentRemainder curvatureRemainder
  unfold linearCoefficient cubicCoefficient denominatorRemainder denominatorCubic
  unfold negativeLaplaceVerticalCubic
  dsimp [theta, w]
  push_cast
  have hsqrtC : ((Real.sqrt b : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hsqrt
  have hsqrtSqC : (((Real.sqrt b : ℝ) : ℂ)) ^ 2 = (b : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hb.le]
  rw [← hsqrtSqC]
  field_simp [hsqrtC]
  ring

/-- A uniform fourth vertical derivative bound and a bounded curvature defect
give the quadratic-plus-quartic remainder required by the generic central
saddle theorem. -/
lemma norm_exponentRemainder_le
    (F : BoundedFabius) (hF : IsFabius F)
    {r b v Csecond Cfourth : ℝ}
    (hr : 0 < r) (hb : 1 ≤ b)
    (hsecond : |r ^ 2 * negativeLaplaceLogSecond F r - b| ≤ Csecond)
    (hfourth : ∀ theta : ℝ, |theta| ≤ 1 →
      ‖negativeLaplaceVerticalLogFourth F r theta‖ ≤ Cfourth * b)
    (htheta : |v / Real.sqrt b| ≤ 1 / 2) :
    ‖exponentRemainder F r b v‖ ≤
      (((Csecond + 1) / 2) * v ^ 2 +
        (Cfourth / 6 + 1 / 2) * v ^ 4) / b := by
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  have hsqrt : 0 < Real.sqrt b := Real.sqrt_pos.2 hb0
  let theta : ℝ := v / Real.sqrt b
  have hthetaOne : |theta| ≤ 1 := htheta.trans (by norm_num)
  have hverticalFourth : ∀ t ∈ uIcc (0 : ℝ) theta,
      ‖negativeLaplaceVerticalLogFourth F r t‖ ≤ Cfourth * b := by
    intro t ht
    apply hfourth t
    have habs : |t| ≤ |theta| := by
      simpa only [sub_zero] using abs_sub_left_of_mem_uIcc ht
    exact habs.trans hthetaOne
  have hvertical := norm_negativeLaplaceVerticalLog_sub_explicitCubic_le
    F hF hr theta (Cfourth * b) hverticalFourth
  have hdenominator := norm_denominatorRemainder_le htheta
  have hcurvatureDefect :
      |b - (1 + r ^ 2 * negativeLaplaceLogSecond F r)| ≤ Csecond + 1 := by
    have htri := abs_add_le
      (b - r ^ 2 * negativeLaplaceLogSecond F r) (-1)
    have heq : b - (1 + r ^ 2 * negativeLaplaceLogSecond F r) =
        (b - r ^ 2 * negativeLaplaceLogSecond F r) + (-1) := by ring
    rw [heq]
    calc
      |b - r ^ 2 * negativeLaplaceLogSecond F r + -1| ≤
          |b - r ^ 2 * negativeLaplaceLogSecond F r| + |-1| := htri
      _ = |r ^ 2 * negativeLaplaceLogSecond F r - b| + 1 := by
        rw [show b - r ^ 2 * negativeLaplaceLogSecond F r =
          -(r ^ 2 * negativeLaplaceLogSecond F r - b) by ring, abs_neg]
        norm_num
      _ ≤ Csecond + 1 := by linarith
  have hcurvature : ‖curvatureRemainder F r b v‖ ≤
      ((Csecond + 1) / 2) * v ^ 2 / b := by
    unfold curvatureRemainder
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
      abs_of_pos hb0, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      |b - (1 + r ^ 2 * negativeLaplaceLogSecond F r)| * |v| ^ 2 /
          (2 * b) ≤ (Csecond + 1) * |v| ^ 2 / (2 * b) := by
        gcongr
      _ = (Csecond + 1) / 2 * v ^ 2 / b := by rw [sq_abs]; ring
  have hvertical' :
      ‖negativeLaplaceVerticalLog F r theta -
          negativeLaplaceVerticalCubic F r theta‖ ≤
        (Cfourth / 6) * v ^ 4 / b := by
    calc
      ‖negativeLaplaceVerticalLog F r theta -
          negativeLaplaceVerticalCubic F r theta‖ ≤
          Cfourth * b * |theta| ^ 4 / 6 := hvertical
      _ = (Cfourth / 6) * v ^ 4 / b := by
        dsimp [theta]
        rw [abs_div, abs_of_pos hsqrt, div_pow]
        have hsqrt4 : Real.sqrt b ^ 4 = b ^ 2 := by
          rw [show Real.sqrt b ^ 4 = (Real.sqrt b ^ 2) ^ 2 by ring,
            Real.sq_sqrt hb0.le]
        rw [hsqrt4, show |v| ^ 4 = v ^ 4 by
          rw [show |v| ^ 4 = (|v| ^ 2) ^ 2 by ring, sq_abs]
          ring]
        field_simp
  have hdenominator' : ‖denominatorRemainder theta‖ ≤
      (1 / 2 : ℝ) * v ^ 4 / b := by
    calc
      ‖denominatorRemainder theta‖ ≤ (1 / 2 : ℝ) * |theta| ^ 4 :=
        hdenominator
      _ = (1 / 2 : ℝ) * v ^ 4 / b ^ 2 := by
        dsimp [theta]
        rw [abs_div, abs_of_pos hsqrt, div_pow]
        have hsqrt4 : Real.sqrt b ^ 4 = b ^ 2 := by
          rw [show Real.sqrt b ^ 4 = (Real.sqrt b ^ 2) ^ 2 by ring,
            Real.sq_sqrt hb0.le]
        rw [hsqrt4]
        rw [show |v| ^ 4 = v ^ 4 by
          rw [show |v| ^ 4 = (|v| ^ 2) ^ 2 by ring, sq_abs]
          ring]
        ring
      _ ≤ (1 / 2 : ℝ) * v ^ 4 / b := by
        have hv4 : 0 ≤ (1 / 2 : ℝ) * v ^ 4 := by positivity
        exact div_le_div_of_nonneg_left hv4 hb0 (by nlinarith)
  unfold exponentRemainder
  dsimp [theta] at hvertical' hdenominator' ⊢
  calc
    ‖(negativeLaplaceVerticalLog F r (v / Real.sqrt b) -
          negativeLaplaceVerticalCubic F r (v / Real.sqrt b)) +
        denominatorRemainder (v / Real.sqrt b) +
        curvatureRemainder F r b v‖ ≤
      ‖negativeLaplaceVerticalLog F r (v / Real.sqrt b) -
          negativeLaplaceVerticalCubic F r (v / Real.sqrt b)‖ +
        ‖denominatorRemainder (v / Real.sqrt b)‖ +
        ‖curvatureRemainder F r b v‖ := (norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (Cfourth / 6) * v ^ 4 / b +
        (1 / 2 : ℝ) * v ^ 4 / b +
        ((Csecond + 1) / 2) * v ^ 2 / b := by
      gcongr
    _ = (((Csecond + 1) / 2) * v ^ 2 +
        (Cfourth / 6 + 1 / 2) * v ^ 4) / b := by ring

/-- The odd linear coefficient at radius `2 ^ b` rewritten through the
scaled first residual, assuming the saddle equation `2 ^ b * x = b`:
`linearCoefficient F x (2 ^ b) b =
(negativeLaplaceRpowFirstResidual F b - 1) / √b`.  The saddle equation is
what turns the term `r * x` into the `+ b` carried inside the residual. -/
lemma linearCoefficient_rpow_eq
    (F : BoundedFabius) {x b : ℝ}
    (hsaddle : (2 : ℝ) ^ b * x = b) :
    linearCoefficient F x ((2 : ℝ) ^ b) b =
      (negativeLaplaceRpowFirstResidual F b - 1) / Real.sqrt b := by
  unfold linearCoefficient negativeLaplaceRpowFirstResidual
  rw [hsaddle]
  ring

/-- The odd cubic coefficient at radius `2 ^ b` rewritten through the scaled
third residual: `cubicCoefficient F (2 ^ b) b =
(2 + 2 b - negativeLaplaceRpowThirdResidual F b) / (6 b √b)`.  Unlike the
linear rewrite this is an algebraic identity, needing neither the saddle
equation nor positivity of `b`. -/
lemma cubicCoefficient_rpow_eq
    (F : BoundedFabius) (b : ℝ) :
    cubicCoefficient F ((2 : ℝ) ^ b) b =
      (2 + 2 * b - negativeLaplaceRpowThirdResidual F b) /
        (6 * b * Real.sqrt b) := by
  unfold cubicCoefficient negativeLaplaceRpowThirdResidual
  ring

/-- Uniform scaled bounds for the odd linear and cubic coefficients at an
explicit dyadic-radius saddle. -/
theorem exists_rpow_coefficient_bounds
    (F : BoundedFabius) (hF : IsFabius F) :
    ∃ Clinear Ccubic : ℝ, 0 ≤ Clinear ∧ 0 ≤ Ccubic ∧
      ∀ {x b : ℝ}, 1 ≤ b → (2 : ℝ) ^ b * x = b →
        b * (linearCoefficient F x ((2 : ℝ) ^ b) b) ^ 2 ≤ Clinear ^ 2 ∧
        b * (cubicCoefficient F ((2 : ℝ) ^ b) b) ^ 2 ≤ Ccubic ^ 2 := by
  obtain ⟨C₁, hC₁0, hC₁⟩ :=
    exists_bound_abs_negativeLaplaceRpowFirstResidual F hF
  obtain ⟨C₃, hC₃0, hC₃⟩ :=
    exists_bound_abs_negativeLaplaceRpowThirdResidual F hF
  let Clinear := C₁ + 1
  let Ccubic := (C₃ + 4) / 6
  have hClinear : 0 ≤ Clinear := by dsimp [Clinear]; positivity
  have hCcubic : 0 ≤ Ccubic := by dsimp [Ccubic]; positivity
  refine ⟨Clinear, Ccubic, hClinear, hCcubic, ?_⟩
  intro x b hb hsaddle
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  have hsqrt : Real.sqrt b ≠ 0 := (Real.sqrt_pos.2 hb0).ne'
  have hres1 := hC₁ (show 0 ≤ b by linarith)
  have hres3 := hC₃ (show 0 ≤ b by linarith)
  have hlinAbs : |negativeLaplaceRpowFirstResidual F b - 1| ≤ Clinear := by
    calc
      |negativeLaplaceRpowFirstResidual F b - 1| ≤
          |negativeLaplaceRpowFirstResidual F b| + |1| := abs_sub _ _
      _ ≤ C₁ + 1 := by norm_num; linarith
      _ = Clinear := rfl
  have hcubAbs :
      |2 + 2 * b - negativeLaplaceRpowThirdResidual F b| ≤
        (C₃ + 4) * b := by
    calc
      |2 + 2 * b - negativeLaplaceRpowThirdResidual F b| ≤
          |2 + 2 * b| + |negativeLaplaceRpowThirdResidual F b| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (2 + 2 * b) (-negativeLaplaceRpowThirdResidual F b)
      _ = 2 + 2 * b + |negativeLaplaceRpowThirdResidual F b| := by
        rw [abs_of_pos (by linarith : 0 < 2 + 2 * b)]
      _ ≤ 2 + 2 * b + C₃ := by linarith
      _ ≤ (C₃ + 4) * b := by nlinarith
  constructor
  · rw [linearCoefficient_rpow_eq F hsaddle]
    have hsq : (negativeLaplaceRpowFirstResidual F b - 1) ^ 2 ≤
        Clinear ^ 2 := by
      rw [← sq_abs]
      exact sq_le_sq₀ (abs_nonneg _) hClinear |>.2 hlinAbs
    rw [div_pow]
    rw [Real.sq_sqrt hb0.le]
    field_simp
    exact hsq
  · rw [cubicCoefficient_rpow_eq]
    have hnumSq :
        (2 + 2 * b - negativeLaplaceRpowThirdResidual F b) ^ 2 ≤
          ((C₃ + 4) * b) ^ 2 := by
      rw [← sq_abs]
      exact sq_le_sq₀ (abs_nonneg _)
        (mul_nonneg (by positivity) hb0.le) |>.2 hcubAbs
    have hden : 0 < 36 * b ^ 2 := by positivity
    have heq :
        b * ((2 + 2 * b - negativeLaplaceRpowThirdResidual F b) /
          (6 * b * Real.sqrt b)) ^ 2 =
          (2 + 2 * b - negativeLaplaceRpowThirdResidual F b) ^ 2 /
            (36 * b ^ 2) := by
      rw [div_pow]
      have hdenSq : (6 * b * Real.sqrt b) ^ 2 = 36 * b ^ 3 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hb0.le]
        ring
      rw [hdenSq]
      field_simp
    rw [heq]
    dsimp [Ccubic]
    rw [div_pow]
    have hrhs : (C₃ + 4) ^ 2 / 6 ^ 2 =
        ((C₃ + 4) * b) ^ 2 / (36 * b ^ 2) := by
      field_simp
      ring
    rw [hrhs]
    exact div_le_div_of_nonneg_right hnumSq hden.le

private lemma tendsto_log_pow_div_id_atTop (n : ℕ) :
    Tendsto (fun b : ℝ => Real.log b ^ n / b) atTop (nhds 0) :=
  Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero

private lemma tendsto_standardRadius_phaseBound
    (Clinear Ccubic : ℝ) :
    Tendsto (fun b : ℝ =>
      (2 * Clinear ^ 2 * fabiusSaddleCentralRadius b ^ 2 +
        2 * Ccubic ^ 2 * fabiusSaddleCentralRadius b ^ 6) / b)
      atTop (nhds 0) := by
  have h1 := (tendsto_log_pow_div_id_atTop 1).const_mul
    (64 * Clinear ^ 2)
  have h3 := (tendsto_log_pow_div_id_atTop 3).const_mul
    (2 * Ccubic ^ 2 * 32 ^ 3)
  have hsum := h1.add h3
  have hsum0 : Tendsto (fun b : ℝ =>
      64 * Clinear ^ 2 * (Real.log b ^ 1 / b) +
        2 * Ccubic ^ 2 * 32 ^ 3 * (Real.log b ^ 3 / b))
      atTop (nhds 0) := by simpa using hsum
  apply hsum0.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
  rw [sq_fabiusSaddleCentralRadius hb]
  have hpow6 : fabiusSaddleCentralRadius b ^ 6 =
      (32 * Real.log b) ^ 3 := by
    rw [show fabiusSaddleCentralRadius b ^ 6 =
      (fabiusSaddleCentralRadius b ^ 2) ^ 3 by ring,
      sq_fabiusSaddleCentralRadius hb]
  rw [hpow6]
  norm_num
  ring

private lemma tendsto_standardRadius_remainderBound
    (Cquadratic Cquartic : ℝ) :
    Tendsto (fun b : ℝ =>
      (Cquadratic * fabiusSaddleCentralRadius b ^ 2 +
        Cquartic * fabiusSaddleCentralRadius b ^ 4) / b)
      atTop (nhds 0) := by
  have h1 := (tendsto_log_pow_div_id_atTop 1).const_mul
    (32 * Cquadratic)
  have h2 := (tendsto_log_pow_div_id_atTop 2).const_mul
    (32 ^ 2 * Cquartic)
  have hsum := h1.add h2
  have hsum0 : Tendsto (fun b : ℝ =>
      32 * Cquadratic * (Real.log b ^ 1 / b) +
        32 ^ 2 * Cquartic * (Real.log b ^ 2 / b))
      atTop (nhds 0) := by simpa using hsum
  apply hsum0.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
  rw [sq_fabiusSaddleCentralRadius hb]
  have hpow4 : fabiusSaddleCentralRadius b ^ 4 =
      (32 * Real.log b) ^ 2 := by
    rw [show fabiusSaddleCentralRadius b ^ 4 =
      (fabiusSaddleCentralRadius b ^ 2) ^ 2 by ring,
      sq_fabiusSaddleCentralRadius hb]
  rw [hpow4]
  norm_num
  ring

private lemma eventually_standardRadius_div_sqrt_le_half :
    ∀ᶠ b : ℝ in atTop,
      fabiusSaddleCentralRadius b / Real.sqrt b ≤ 1 / 2 := by
  have hdecay := (tendsto_log_pow_div_id_atTop 1).const_mul 128
  have hdecay' : Tendsto (fun b : ℝ => 128 * Real.log b / b)
      atTop (nhds 0) := by
    convert hdecay using 1
    · funext b
      simp only [pow_one]
      ring
    · norm_num
  have hsmall : ∀ᶠ b : ℝ in atTop, 128 * Real.log b / b ≤ 1 :=
    hdecay'.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsmall] with b hb hratio
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  have hsqrt : 0 < Real.sqrt b := Real.sqrt_pos.2 hb0
  have hlog : 128 * Real.log b ≤ b := by
    exact (div_le_one hb0).mp hratio
  have hA0 : 0 ≤ fabiusSaddleCentralRadius b := Real.sqrt_nonneg _
  have hsqrt0 : 0 ≤ Real.sqrt b := hsqrt.le
  have hAsq := sq_fabiusSaddleCentralRadius hb
  have hbsq := Real.sq_sqrt hb0.le
  rw [div_le_iff₀ hsqrt]
  nlinarith [sq_nonneg (2 * fabiusSaddleCentralRadius b + Real.sqrt b),
    sq_nonneg (2 * fabiusSaddleCentralRadius b - Real.sqrt b)]

private lemma eventually_standardRadius_theta_le_half
    {alpha : Type*} {l : Filter alpha} (b : alpha → ℝ)
    (hbinfty : Tendsto b l atTop) :
    ∀ᶠ i in l, ∀ v ∈ Icc (-(fabiusSaddleCentralRadius (b i)))
        (fabiusSaddleCentralRadius (b i)),
      |v / Real.sqrt (b i)| ≤ 1 / 2 := by
  filter_upwards
    [hbinfty.eventually eventually_standardRadius_div_sqrt_le_half,
      hbinfty.eventually (eventually_ge_atTop (1 : ℝ))]
      with i hradius hbi v hv
  have hb0 : 0 < b i := zero_lt_one.trans_le hbi
  have hsqrt : 0 < Real.sqrt (b i) := Real.sqrt_pos.2 hb0
  have hvabs : |v| ≤ fabiusSaddleCentralRadius (b i) := abs_le.mpr hv
  rw [abs_div, abs_of_pos hsqrt]
  calc
    |v| / Real.sqrt (b i) ≤
        fabiusSaddleCentralRadius (b i) / Real.sqrt (b i) := by gcongr
    _ ≤ 1 / 2 := hradius

private lemma eventually_oddPhase_small
    {alpha : Type*} {l : Filter alpha}
    (b a c : alpha → ℝ) (Clinear Ccubic : ℝ)
    (hbinfty : Tendsto b l atTop)
    (ha : ∀ᶠ i in l, b i * (a i) ^ 2 ≤ Clinear ^ 2)
    (hc : ∀ᶠ i in l, b i * (c i) ^ 2 ≤ Ccubic ^ 2) :
    ∀ᶠ i in l, ∀ v ∈ Icc (-(fabiusSaddleCentralRadius (b i)))
        (fabiusSaddleCentralRadius (b i)),
      ‖SaddleCentral.oddPhase (a i) (c i) v‖ ≤ 1 := by
  have hbound : ∀ᶠ z : ℝ in atTop,
      (2 * Clinear ^ 2 * fabiusSaddleCentralRadius z ^ 2 +
        2 * Ccubic ^ 2 * fabiusSaddleCentralRadius z ^ 6) / z ≤ 1 :=
    (tendsto_standardRadius_phaseBound Clinear Ccubic).eventually
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hbinfty.eventually (eventually_ge_atTop (1 : ℝ)),
    hbinfty.eventually hbound, ha, hc] with i hbi hboundi hai hci v hv
  have hb0 : 0 < b i := zero_lt_one.trans_le hbi
  have hvabs : |v| ≤ fabiusSaddleCentralRadius (b i) := abs_le.mpr hv
  have hsq := SaddleCentral.oddPhase_sq_le_div
    (b i) (a i) (c i) Clinear Ccubic v hb0 hai hci
  have hv2 : v ^ 2 ≤ fabiusSaddleCentralRadius (b i) ^ 2 := by
    rw [← sq_abs v]
    exact sq_le_sq₀ (abs_nonneg v) (Real.sqrt_nonneg _) |>.2 hvabs
  have hv6 : v ^ 6 ≤ fabiusSaddleCentralRadius (b i) ^ 6 := by
    have hv3 : |v| ^ 3 ≤ fabiusSaddleCentralRadius (b i) ^ 3 :=
      pow_le_pow_left₀ (abs_nonneg v) hvabs 3
    rw [show v ^ 6 = (|v| ^ 3) ^ 2 by
      rw [show v ^ 6 = (v ^ 3) ^ 2 by ring, ← sq_abs (v ^ 3), abs_pow]]
    have hsquare := sq_le_sq₀ (by positivity)
      (pow_nonneg (Real.sqrt_nonneg _) 3) |>.2 hv3
    rw [show fabiusSaddleCentralRadius (b i) ^ 6 =
      (fabiusSaddleCentralRadius (b i) ^ 3) ^ 2 by ring]
    exact hsquare
  have hsq' : ‖SaddleCentral.oddPhase (a i) (c i) v‖ ^ 2 ≤ 1 := by
    calc
      ‖SaddleCentral.oddPhase (a i) (c i) v‖ ^ 2 ≤
          (2 * Clinear ^ 2 * v ^ 2 + 2 * Ccubic ^ 2 * v ^ 6) / b i := hsq
      _ ≤ (2 * Clinear ^ 2 * fabiusSaddleCentralRadius (b i) ^ 2 +
          2 * Ccubic ^ 2 * fabiusSaddleCentralRadius (b i) ^ 6) / b i := by
        gcongr
      _ ≤ 1 := hboundi
  nlinarith [norm_nonneg (SaddleCentral.oddPhase (a i) (c i) v)]

private lemma eventually_remainder_small_of_bound
    {alpha : Type*} {l : Filter alpha}
    (R : alpha → ℝ → ℂ) (b : alpha → ℝ)
    (Cquadratic Cquartic : ℝ)
    (hCquadratic : 0 ≤ Cquadratic) (hCquartic : 0 ≤ Cquartic)
    (hbinfty : Tendsto b l atTop)
    (hR : ∀ᶠ i in l, ∀ v ∈ Icc (-(fabiusSaddleCentralRadius (b i)))
        (fabiusSaddleCentralRadius (b i)),
      ‖R i v‖ ≤ (Cquadratic * v ^ 2 + Cquartic * v ^ 4) / b i) :
    ∀ᶠ i in l, ∀ v ∈ Icc (-(fabiusSaddleCentralRadius (b i)))
        (fabiusSaddleCentralRadius (b i)), ‖R i v‖ ≤ 1 := by
  have hbound : ∀ᶠ z : ℝ in atTop,
      (Cquadratic * fabiusSaddleCentralRadius z ^ 2 +
        Cquartic * fabiusSaddleCentralRadius z ^ 4) / z ≤ 1 :=
    (tendsto_standardRadius_remainderBound Cquadratic Cquartic).eventually
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hbinfty.eventually (eventually_ge_atTop (1 : ℝ)),
    hbinfty.eventually hbound, hR] with i hbi hboundi hRi v hv
  have hvabs : |v| ≤ fabiusSaddleCentralRadius (b i) := abs_le.mpr hv
  have hv2 : v ^ 2 ≤ fabiusSaddleCentralRadius (b i) ^ 2 := by
    rw [← sq_abs v]
    exact sq_le_sq₀ (abs_nonneg v) (Real.sqrt_nonneg _) |>.2 hvabs
  have hv4 : v ^ 4 ≤ fabiusSaddleCentralRadius (b i) ^ 4 := by
    calc
      v ^ 4 = (v ^ 2) ^ 2 := by ring
      _ ≤ (fabiusSaddleCentralRadius (b i) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg v) hv2 2
      _ = fabiusSaddleCentralRadius (b i) ^ 4 := by ring
  calc
    ‖R i v‖ ≤ (Cquadratic * v ^ 2 + Cquartic * v ^ 4) / b i := hRi v hv
    _ ≤ (Cquadratic * fabiusSaddleCentralRadius (b i) ^ 2 +
        Cquartic * fabiusSaddleCentralRadius (b i) ^ 4) / b i := by
      gcongr
    _ ≤ 1 := hboundi

/-- The scaled saddle kernel on the explicit dyadic Lambert orbit. -/
noncomputable def dyadicLambertKernel
    (F : BoundedFabius) (t v : ℝ) : ℂ :=
  QuantitativeSaddle.scaledSaddleKernel
    (fun z => complexGeneratingFunction F (-z))
    ((2 : ℝ) ^ (-t))
    (fabiusLambertRadius ((2 : ℝ) ^ (-t)))
    (dyadicLambertPhase t) v

/-- Odd linear coefficient on the explicit dyadic Lambert orbit. -/
noncomputable def dyadicLambertLinearCoefficient
    (F : BoundedFabius) (t : ℝ) : ℝ :=
  linearCoefficient F ((2 : ℝ) ^ (-t))
    (fabiusLambertRadius ((2 : ℝ) ^ (-t)))
    (dyadicLambertPhase t)

/-- Odd cubic coefficient on the explicit dyadic Lambert orbit. -/
noncomputable def dyadicLambertCubicCoefficient
    (F : BoundedFabius) (t : ℝ) : ℝ :=
  cubicCoefficient F
    (fabiusLambertRadius ((2 : ℝ) ^ (-t)))
    (dyadicLambertPhase t)

/-- Central exponent remainder on the explicit dyadic Lambert orbit. -/
noncomputable def dyadicLambertExponentRemainder
    (F : BoundedFabius) (t v : ℝ) : ℂ :=
  exponentRemainder F
    (fabiusLambertRadius ((2 : ℝ) ^ (-t)))
    (dyadicLambertPhase t) v

private lemma eventually_dyadicLambert_coefficient_bounds
    (F : BoundedFabius) (hF : IsFabius F) :
    ∃ Clinear Ccubic : ℝ, 0 ≤ Clinear ∧ 0 ≤ Ccubic ∧
      (∀ᶠ t : ℝ in atTop,
        dyadicLambertPhase t * (dyadicLambertLinearCoefficient F t) ^ 2 ≤
          Clinear ^ 2) ∧
      (∀ᶠ t : ℝ in atTop,
        dyadicLambertPhase t * (dyadicLambertCubicCoefficient F t) ^ 2 ≤
          Ccubic ^ 2) := by
  obtain ⟨Clinear, Ccubic, hClinear, hCcubic, hcoeff⟩ :=
    exists_rpow_coefficient_bounds F hF
  refine ⟨Clinear, Ccubic, hClinear, hCcubic, ?_, ?_⟩
  all_goals
    filter_upwards [tendsto_dyadicLambertPhase_atTop.eventually_ge_atTop 1,
      eventually_dyadicLambertPhase_domain] with t hphase hsmall
    have hsaddle := fabiusLambertRadius_mul_argument
      (x := (2 : ℝ) ^ (-t)) (Real.rpow_pos_of_pos (by norm_num) _) hsmall
    have h := hcoeff hphase (by
      simpa only [fabiusLambertRadius_dyadic, fabiusLambertPhase_dyadic] using hsaddle)
    first
    | simpa only [dyadicLambertLinearCoefficient,
        fabiusLambertRadius_dyadic] using h.1
    | simpa only [dyadicLambertCubicCoefficient,
        fabiusLambertRadius_dyadic] using h.2

/-- Corrected central `L¹` error at the explicit dyadic Lambert saddle. -/
theorem dyadicLambert_central_corrected_error_isBigO
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun t : ℝ => ∫ v in
      Icc (-fabiusSaddleCentralRadius (dyadicLambertPhase t))
        (fabiusSaddleCentralRadius (dyadicLambertPhase t)),
      ‖dyadicLambertKernel F t v -
        (QuantitativeSaddle.standardGaussian v +
          SaddleCentral.oddCorrection
            (dyadicLambertLinearCoefficient F t)
            (dyadicLambertCubicCoefficient F t) v)‖) =O[atTop]
      (fun t : ℝ => (dyadicLambertPhase t)⁻¹) := by
  obtain ⟨Clinear, Ccubic, hClinear, hCcubic, hlinear, hcubic⟩ :=
    eventually_dyadicLambert_coefficient_bounds F hF
  obtain ⟨Csecond, hCsecond, hsecond⟩ :=
    exists_bound_abs_negativeLaplaceRpowSecondResidual F hF
  obtain ⟨Cfourth, hCfourth, hfourth⟩ :=
    exists_norm_negativeLaplaceVerticalLogFourth_rpow_le F hF
  let Cquadratic : ℝ := (Csecond + 1) / 2
  let Cquartic : ℝ := Cfourth / 6 + 1 / 2
  have hCquadratic : 0 ≤ Cquadratic := by dsimp [Cquadratic]; positivity
  have hCquartic : 0 ≤ Cquartic := by dsimp [Cquartic]; positivity
  have hbpos : ∀ᶠ t : ℝ in atTop, 0 < dyadicLambertPhase t :=
    (tendsto_dyadicLambertPhase_atTop.eventually_ge_atTop 1).mono
      (fun _ h => zero_lt_one.trans_le h)
  have hKint : ∀ᶠ t : ℝ in atTop, Integrable (dyadicLambertKernel F t) := by
    filter_upwards [hbpos] with t hbt
    exact integrable_fabius_scaledSaddleKernel F hF
      ((2 : ℝ) ^ (-t)) (fabiusLambertRadius ((2 : ℝ) ^ (-t)))
      (dyadicLambertPhase t) (fabiusLambertRadius_pos _) hbt
  have hrepresentation : ∀ᶠ t : ℝ in atTop,
      ∀ v ∈ Icc (-fabiusSaddleCentralRadius (dyadicLambertPhase t))
        (fabiusSaddleCentralRadius (dyadicLambertPhase t)),
      dyadicLambertKernel F t v = QuantitativeSaddle.standardGaussian v *
        Complex.exp
          (SaddleCentral.oddPhase (dyadicLambertLinearCoefficient F t)
              (dyadicLambertCubicCoefficient F t) v +
            dyadicLambertExponentRemainder F t v) := by
    filter_upwards [hbpos] with t hbt v _hv
    exact scaledSaddleKernel_eq_gaussian_exp F hF _ _ _ _
      (fabiusLambertRadius_pos _) hbt
  have htheta := eventually_standardRadius_theta_le_half
    dyadicLambertPhase tendsto_dyadicLambertPhase_atTop
  have hremainder : ∀ᶠ t : ℝ in atTop,
      ∀ v ∈ Icc (-fabiusSaddleCentralRadius (dyadicLambertPhase t))
        (fabiusSaddleCentralRadius (dyadicLambertPhase t)),
      ‖dyadicLambertExponentRemainder F t v‖ ≤
        (Cquadratic * v ^ 2 + Cquartic * v ^ 4) /
          dyadicLambertPhase t := by
    filter_upwards
      [tendsto_dyadicLambertPhase_atTop.eventually_ge_atTop 1, htheta]
      with t hbt hthetaAt v hv
    have hsecondAt := hsecond (show 0 ≤ dyadicLambertPhase t by linarith)
    have hfourthAt : ∀ theta : ℝ, |theta| ≤ 1 →
        ‖negativeLaplaceVerticalLogFourth F
          (fabiusLambertRadius ((2 : ℝ) ^ (-t))) theta‖ ≤
            Cfourth * dyadicLambertPhase t := by
      intro theta hthetaOne
      simpa only [fabiusLambertRadius_dyadic] using
        hfourth hbt hthetaOne
    simpa only [dyadicLambertExponentRemainder, Cquadratic, Cquartic,
      fabiusLambertRadius_dyadic] using
      norm_exponentRemainder_le F hF
        (fabiusLambertRadius_pos ((2 : ℝ) ^ (-t))) hbt
        hsecondAt hfourthAt (hthetaAt v hv)
  have hphaseSmall := eventually_oddPhase_small dyadicLambertPhase
    (dyadicLambertLinearCoefficient F) (dyadicLambertCubicCoefficient F)
    Clinear Ccubic tendsto_dyadicLambertPhase_atTop hlinear hcubic
  have hremainderSmall := eventually_remainder_small_of_bound
    (dyadicLambertExponentRemainder F) dyadicLambertPhase
    Cquadratic Cquartic hCquadratic hCquartic
    tendsto_dyadicLambertPhase_atTop hremainder
  exact SaddleCentral.standardRadius_central_corrected_error_isBigO
    atTop (dyadicLambertKernel F) (dyadicLambertExponentRemainder F)
    dyadicLambertPhase (dyadicLambertLinearCoefficient F)
    (dyadicLambertCubicCoefficient F)
    Clinear Ccubic Cquadratic Cquartic hCquadratic hCquartic
    hbpos hlinear hcubic hKint hrepresentation hphaseSmall
    hremainderSmall hremainder

private theorem normalized_integral_sub_one_isBigO_of_corrected_parts_isBigO
    {alpha : Type*} (l : Filter alpha)
    (K J : alpha → ℝ → ℂ) (central : alpha → Set ℝ)
    (b : alpha → ℝ)
    (hb : ∀ᶠ i in l, 0 < b i)
    (hK : ∀ᶠ i in l, Integrable (K i))
    (hJ : ∀ᶠ i in l, Integrable (J i))
    (hJodd : ∀ᶠ i in l, Function.Odd (J i))
    (hcentralMeas : ∀ᶠ i in l, MeasurableSet (central i))
    (hcentral :
      (fun i => ∫ v in central i,
        ‖K i v - (QuantitativeSaddle.standardGaussian v + J i v)‖) =O[l]
          (fun i => (b i)⁻¹))
    (htail :
      (fun i => ∫ v in (central i)ᶜ,
        ‖K i v - (QuantitativeSaddle.standardGaussian v + J i v)‖) =O[l]
          (fun i => (b i)⁻¹)) :
    (fun i => (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * (∫ v : ℝ, K i v) - 1)
      =O[l] (fun i => (b i)⁻¹) := by
  rw [isBigO_iff] at hcentral htail
  obtain ⟨Ccentral, hcentral⟩ := hcentral
  obtain ⟨Ctail, htail⟩ := htail
  apply QuantitativeSaddle.normalized_integral_sub_one_isBigO_of_central_tail_odd_correction
    l b K J central Ccentral Ctail hb hK hJ hJodd hcentralMeas
  · filter_upwards [hb, hcentral] with i hbi hi
    have hnonneg : 0 ≤ ∫ v in central i,
        ‖K i v - (QuantitativeSaddle.standardGaussian v + J i v)‖ :=
      integral_nonneg fun _ => norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, norm_inv,
      Real.norm_eq_abs, abs_of_pos hbi] at hi
    exact hi
  · filter_upwards [hb, htail] with i hbi hi
    have hnonneg : 0 ≤ ∫ v in (central i)ᶜ,
        ‖K i v - (QuantitativeSaddle.standardGaussian v + J i v)‖ :=
      integral_nonneg fun _ => norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, norm_inv,
      Real.norm_eq_abs, abs_of_pos hbi] at hi
    exact hi

/-- The normalized Bromwich kernel at the explicit dyadic Lambert saddle is
`1 + O(1/lambda)`.  This is the final analytic input required by the sharp
small-argument transfer theorems. -/
theorem fabiusSaddleKernelMass_dyadicLambert_sub_one_isBigO
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun t : ℝ => fabiusSaddleKernelMass F ((2 : ℝ) ^ (-t))
        (fabiusLambertRadius ((2 : ℝ) ^ (-t)))
        (fabiusLambertPhase ((2 : ℝ) ^ (-t))) - 1) =O[atTop]
      (fun t : ℝ => (fabiusLambertPhase ((2 : ℝ) ^ (-t)))⁻¹) := by
  obtain ⟨Clinear, Ccubic, hClinear, hCcubic, hlinear, hcubic⟩ :=
    eventually_dyadicLambert_coefficient_bounds F hF
  let b : ℝ → ℝ := dyadicLambertPhase
  let a : ℝ → ℝ := dyadicLambertLinearCoefficient F
  let c : ℝ → ℝ := dyadicLambertCubicCoefficient F
  let K : ℝ → ℝ → ℂ := dyadicLambertKernel F
  let J : ℝ → ℝ → ℂ := fun t => SaddleCentral.oddCorrection (a t) (c t)
  let central : ℝ → Set ℝ := fun t =>
    Icc (-fabiusSaddleCentralRadius (b t)) (fabiusSaddleCentralRadius (b t))
  have hbpos : ∀ᶠ t : ℝ in atTop, 0 < b t :=
    (tendsto_dyadicLambertPhase_atTop.eventually_ge_atTop 1).mono
      (fun _ h => zero_lt_one.trans_le h)
  have hKint : ∀ᶠ t : ℝ in atTop, Integrable (K t) := by
    filter_upwards [hbpos] with t hbt
    exact integrable_fabius_scaledSaddleKernel F hF
      ((2 : ℝ) ^ (-t)) (fabiusLambertRadius ((2 : ℝ) ^ (-t)))
      (dyadicLambertPhase t) (fabiusLambertRadius_pos _) hbt
  have hcentral :
      (fun t => ∫ v in central t,
        ‖K t v - (QuantitativeSaddle.standardGaussian v + J t v)‖) =O[atTop]
        (fun t => (b t)⁻¹) := by
    simpa only [central, K, J, a, c, b] using
      dyadicLambert_central_corrected_error_isBigO F hF
  have hKtail :
      (fun t => ∫ v in (central t)ᶜ, ‖K t v‖) =O[atTop]
        (fun t => (b t)⁻¹) := by
    simpa only [central, K, b, dyadicLambertKernel] using
      integral_norm_fabius_scaledSaddleKernel_dyadicLambert_isBigO F hF
  have htail :=
    SaddleCentral.integral_norm_sub_gaussian_add_oddCorrection_standardRadius_isBigO
      atTop b a c K Clinear Ccubic hClinear hCcubic
      tendsto_dyadicLambertPhase_atTop
      (by simpa only [b, a] using hlinear)
      (by simpa only [b, c] using hcubic) hKint hKtail
  have hnormalized := normalized_integral_sub_one_isBigO_of_corrected_parts_isBigO
    atTop K J central b hbpos hKint
    (Filter.Eventually.of_forall fun t => SaddleCentral.integrable_oddCorrection (a t) (c t))
    (Filter.Eventually.of_forall fun t => SaddleCentral.oddCorrection_odd (a t) (c t))
    (Filter.Eventually.of_forall fun _ => measurableSet_Icc)
    hcentral (by simpa only [central, K, J, a, c, b] using htail)
  simpa only [fabiusSaddleKernelMass, K, b, dyadicLambertKernel,
    fabiusLambertPhase_dyadic] using hnormalized

end SaddleLambert

end Fabius

