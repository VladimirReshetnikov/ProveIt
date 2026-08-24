import IntegerPoints.IwaniecMozzochiEq114Fourier
import IntegerPoints.IwaniecMozzochiEq115ReciprocalPhase
import IntegerPoints.IwaniecMozzochiReciprocalQuadraticBound
import IntegerPoints.IwaniecMozzochiReductionEq117
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The Fourier multiplier behind Iwaniec--Mozzochi (11.2)/(11.3)

This file reduces the remaining analytic assertion in Lemma 11.1 to the
exact generalized reciprocal-Bessel transform used in the paper.  The
reduction is quantitative: all of the stationary-frequency Taylor estimate,
the Fourier inversion, the integrability, and the final `y^2 |fhat(y)|`
majorization are proved here.

For `a > 0`, put

```
  A(a) = (2 * I * a)^(-1/2).
```

The full reciprocal-Bessel multiplier is

```
  K(a,c) = A(a) * e(-2*sqrt(a*c))                    if 0 < c,
           A(a) * exp(-4*pi*sqrt(a*|c|))             if c <= 0.
```

The second branch is the nonstationary continuation recorded immediately
after (11.5) in the paper.  It has norm at most `|A(a)|`.  Around a positive
frequency `b`, the first branch agrees through first order with

```
  K(a,b) * e(sqrt(a/b) * y)
```

at `c = b-y`.  The elementary square-root identity

```
  sqrt(b-y) - sqrt(b) + y/(2*sqrt(b))
    = -(sqrt(b)-sqrt(b-y))^2/(2*sqrt(b))
```

therefore gives a quadratic error.  Outside `2*|y| < b`, boundedness of both
multipliers gives the complementary `a^(-1/2) b^(-2) y^2` term.

Mathlib's forward Fourier kernel has the negative sign, so its inversion
formula contributes `e(x*y)`: the paper's `b+y` is therefore `b-y` below.

The source below now proves the fixed-cutoff Fubini identity and the complete
dominated cutoff-limit/Fourier interchange.  Two genuinely oscillatory inputs
remain explicit: the nonstationary continuation at a strictly negative
shifted frequency, and a truncated-kernel bound uniform in that frequency.
The positive-frequency limit is the already proved (11.5), and the zero
endpoint is reduced here to the proved half-Fresnel integral.  No part of the
desired remainder estimate is assumed by either residual.
-/

open scoped ContDiff FourierTransform SchwartzMap
open Real Set Filter MeasureTheory

namespace LeanProofs.IntegerPoints

noncomputable section

/-! ## The exact generalized reciprocal-Bessel multiplier -/

/-- The principal-branch constant in (11.5). -/
noncomputable def eq112BesselAmplitude (a : Real) : Complex :=
  (2 * Complex.I * (a : Complex)) ^ (-(1 : Complex) / 2)

/-- The continuation of the reciprocal-Bessel integral to every real linear
frequency.  At a nonpositive frequency its exponential is real and decaying.
-/
noncomputable def eq112BesselMultiplier (a c : Real) : Complex :=
  eq112BesselAmplitude a *
    if 0 < c then e (-2 * Real.sqrt (a * c))
    else ((Real.exp (-4 * Real.pi * Real.sqrt (a * abs c)) : Real) : Complex)

/-- The absolutely convergent lower-cutoff reciprocal-Bessel kernel.  Only
the limit `delta -> 0+` is improper; for every positive cutoff this is an
ordinary `L^1` integral. -/
noncomputable def eq112TruncatedBesselKernel
    (a c delta : Real) : Complex :=
  ∫ t in Set.Ioi delta,
    ((t ^ (-(3 : Real) / 2) : Real) : Complex) *
      e (-a / t - c * t)

private theorem measurable_e_comp {α : Type*} [MeasurableSpace α]
    {g : α → Real} (hg : Measurable g) :
    Measurable (fun x => e (g x)) := by
  unfold e
  exact Complex.measurable_exp.comp
    (measurable_const.mul (Complex.measurable_ofReal.comp hg))

private theorem eq112_cpow_scale {a : Real} (ha : 0 < a) :
    eq112BesselAmplitude a =
      (a : Complex) ^ (-(1 : Complex) / 2) *
        ((2 : Complex) * Complex.I) ^ (-(1 : Complex) / 2) := by
  have ha0 : (a : Complex) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hI0 : (2 : Complex) * Complex.I ≠ 0 :=
    mul_ne_zero (by norm_num) Complex.I_ne_zero
  unfold eq112BesselAmplitude
  rw [show (2 : Complex) * Complex.I * (a : Complex) =
      (a : Complex) * ((2 : Complex) * Complex.I) by ring,
    Complex.cpow_def_of_ne_zero (mul_ne_zero ha0 hI0),
    Complex.log_ofReal_mul ha hI0, Complex.ofReal_log ha.le,
    add_mul, Complex.exp_add,
    ← Complex.cpow_def_of_ne_zero ha0,
    ← Complex.cpow_def_of_ne_zero hI0]

private theorem eq112_ofReal_cpow_neg_half {a : Real} (ha : 0 < a) :
    (a : Complex) ^ (-(1 : Complex) / 2) =
      (((Real.sqrt a)⁻¹ : Real) : Complex) := by
  have hrpow : a ^ (-(1 : Real) / 2) = (Real.sqrt a)⁻¹ := by
    rw [show -(1 : Real) / 2 = -((1 : Real) / 2) by ring,
      Real.rpow_neg ha.le, ← Real.sqrt_eq_rpow]
  calc
    (a : Complex) ^ (-(1 : Complex) / 2) =
        ((a ^ (-(1 : Real) / 2) : Real) : Complex) := by
      symm
      simpa using Complex.ofReal_cpow ha.le (-(1 : Real) / 2)
    _ = (((Real.sqrt a)⁻¹ : Real) : Complex) := by rw [hrpow]

private theorem eq112_inv_sqrt_eq_rpow {a : Real} (ha : 0 < a) :
    (Real.sqrt a)⁻¹ = a ^ (-(1 : Real) / 2) := by
  rw [show -(1 : Real) / 2 = -((1 : Real) / 2) by ring,
    Real.rpow_neg ha.le, ← Real.sqrt_eq_rpow]

/-- The principal complex amplitude has no larger norm than `a^(-1/2)`.
The omitted factor is exactly `1/sqrt 2`. -/
private theorem norm_eq112BesselAmplitude_le {a : Real} (ha : 0 < a) :
    norm (eq112BesselAmplitude a) ≤ a ^ (-(1 : Real) / 2) := by
  rw [eq112_cpow_scale ha, eq112_ofReal_cpow_neg_half ha,
    eq115_two_mul_I_cpow_neg_half, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (Real.sqrt_pos.2 ha)), norm_div,
    norm_e, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.2 (by norm_num : (0 : Real) < 2))]
  rw [eq112_inv_sqrt_eq_rpow ha]
  have hsqrtTwo : 1 ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hinv : (Real.sqrt 2)⁻¹ ≤ 1 :=
    (inv_le_one₀ (Real.sqrt_pos.2 (by norm_num))).2 hsqrtTwo
  simpa only [div_eq_mul_inv, one_mul, mul_one] using
    mul_le_mul_of_nonneg_left hinv
      (Real.rpow_nonneg ha.le (-(1 : Real) / 2))

/-- The generalized multiplier is uniformly bounded by the principal
amplitude, including on the nonstationary branch. -/
private theorem norm_eq112BesselMultiplier_le {a c : Real} (ha : 0 < a) :
    norm (eq112BesselMultiplier a c) ≤ a ^ (-(1 : Real) / 2) := by
  unfold eq112BesselMultiplier
  split_ifs with hc
  · rw [norm_mul, norm_e, mul_one]
    exact norm_eq112BesselAmplitude_le ha
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (-4 * Real.pi * Real.sqrt (a * abs c)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hnonneg : 0 ≤ 4 * Real.pi * Real.sqrt (a * abs c) := by
        positivity
      linarith
    calc
      norm (eq112BesselAmplitude a) *
          Real.exp (-4 * Real.pi * Real.sqrt (a * abs c)) ≤
          norm (eq112BesselAmplitude a) * 1 :=
        mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
      _ ≤ a ^ (-(1 : Real) / 2) := by
        simpa using norm_eq112BesselAmplitude_le ha

private theorem eq112BesselMultiplier_at_pos {a b : Real} (hb : 0 < b) :
    eq112BesselMultiplier a b =
      eq112BesselAmplitude a * e (-2 * Real.sqrt (a * b)) := by
  simp [eq112BesselMultiplier, hb]

/-- On the positive-frequency branch, the multiplier is not a new analytic
assumption: it is exactly the already proved reciprocal-phase formula (11.5).
The only branch of the generalized kernel not covered by (11.5) is `c ≤ 0`.
-/
theorem eq112_besselMultiplier_positive_limit {a c : Real}
    (ha : 0 < a) (hc : 0 < c) :
    Tendsto
      (eq112TruncatedBesselKernel a c)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (eq112BesselMultiplier a c)) := by
  change Tendsto
    (fun delta : Real => ∫ t in Set.Ioi delta,
      ((t ^ (-(3 : Real) / 2) : Real) : Complex) *
        e (-a / t - c * t))
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds (eq112BesselMultiplier a c))
  simpa [eq112BesselMultiplier, eq112BesselAmplitude, hc] using
    (iwaniecMozzochi_eq115_holds a c ha hc)

/-- The zero-frequency endpoint is also unconditional.  After the same
`t = a/u^2` substitution as in (11.5), it is exactly a constant multiple of
the already evaluated negative half-Fresnel integral. -/
theorem eq112_besselMultiplier_zero_limit {a : Real} (ha : 0 < a) :
    Tendsto
      (eq112TruncatedBesselKernel a 0)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (eq112BesselMultiplier a 0)) := by
  let K : Complex := ((2 / Real.sqrt a : Real) : Complex)
  have hcore := iwaniecMozzochi_eq115_halfFresnel.comp
    (tendsto_eq115_truncationEndpoint ha)
  have hlimit :
      Tendsto
        (fun delta : Real => K *
          eq115HalfFresnelIntegral (Real.sqrt (a / delta)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (K *
          (((2 : Complex) * Complex.I) ^ (-(1 : Complex) / 2) / 2))) :=
    tendsto_const_nhds.mul hcore
  have heventually :
      (fun delta : Real => K *
        eq115HalfFresnelIntegral (Real.sqrt (a / delta))) =ᶠ[
          nhdsWithin 0 (Set.Ioi 0)]
        eq112TruncatedBesselKernel a 0 := by
    filter_upwards [self_mem_nhdsWithin] with delta hdelta
    simpa [K, eq112TruncatedBesselKernel, eq115HalfFresnelIntegral,
      intervalIntegral.integral_of_le (Real.sqrt_nonneg _)] using
      (Eq115Change.iwaniecMozzochi_eq115_truncatedChangeOfVariables_zero
        (a := a) (δ := delta) ha hdelta).symm
  have htarget :
      K * (((2 : Complex) * Complex.I) ^ (-(1 : Complex) / 2) / 2) =
        eq112BesselMultiplier a 0 := by
    have hzero : eq112BesselMultiplier a 0 = eq112BesselAmplitude a := by
      simp [eq112BesselMultiplier]
    rw [hzero, eq112_cpow_scale ha, eq112_ofReal_cpow_neg_half ha]
    dsimp only [K]
    push_cast
    simp only [div_eq_mul_inv]
    ring
  rw [← htarget]
  exact hlimit.congr' heventually

private theorem eq112_kernel_measurable (a c : Real) :
    Measurable (fun t : Real =>
      ((t ^ (-(3 : Real) / 2) : Real) : Complex) *
        e (-a / t - c * t)) := by
  unfold e
  fun_prop

private theorem eq112_truncatedKernel_integrable
    {a c delta : Real} (hdelta : 0 < delta) :
    Integrable (Set.indicator (Set.Ioi delta) (fun t : Real =>
      ((t ^ (-(3 : Real) / 2) : Real) : Complex) *
        e (-a / t - c * t))) := by
  rw [integrable_indicator_iff measurableSet_Ioi]
  have hmajor : IntegrableOn
      (fun t : Real => t ^ (-(3 : Real) / 2)) (Set.Ioi delta) :=
    integrableOn_Ioi_rpow_of_lt (a := -(3 : Real) / 2)
      (by norm_num) hdelta
  refine hmajor.mono'
    (eq112_kernel_measurable a c).aestronglyMeasurable.restrict ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2
    (Eventually.of_forall fun t ht => ?_)
  have ht0 : 0 < t := hdelta.trans ht
  rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos ht0 _)]

/-- Absolute convergence at a fixed cutoff gives a useful, but deliberately
non-uniform, baseline bound.  The factor `delta^(-1/2)` pinpoints why plain
absolute convergence cannot justify removal of the cutoff. -/
theorem norm_eq112TruncatedBesselKernel_le
    {a c delta : Real} (hdelta : 0 < delta) :
    norm (eq112TruncatedBesselKernel a c delta) <=
      2 * delta ^ (-(1 : Real) / 2) := by
  unfold eq112TruncatedBesselKernel
  calc
    norm (∫ t in Set.Ioi delta,
        ((t ^ (-(3 : Real) / 2) : Real) : Complex) *
          e (-a / t - c * t)) <=
        ∫ t in Set.Ioi delta, t ^ (-(3 : Real) / 2) := by
      apply MeasureTheory.norm_integral_le_of_norm_le
        (integrableOn_Ioi_rpow_of_lt (a := -(3 : Real) / 2)
          (by norm_num) hdelta)
      refine (ae_restrict_iff' measurableSet_Ioi).2
        (Eventually.of_forall fun t ht => ?_)
      have ht0 : 0 < t := hdelta.trans ht
      rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
    _ = 2 * delta ^ (-(1 : Real) / 2) := by
      rw [integral_Ioi_rpow_of_lt (a := -(3 : Real) / 2)
        (by norm_num) hdelta]
      ring_nf

/-- At a fixed lower cutoff, the reciprocal-Bessel kernel is measurable in
the linear-frequency parameter.  This is a direct parameter-integral
measurability statement; it does not use any improper-limit assertion. -/
private theorem eq112_truncatedBesselKernel_measurable (a delta : Real) :
    Measurable (fun c : Real => eq112TruncatedBesselKernel a c delta) := by
  let G : Real × Real -> Complex := fun z =>
    if z.2 ∈ Set.Ioi delta then
      ((z.2 ^ (-(3 : Real) / 2) : Real) : Complex) *
        e (-a / z.2 - z.1 * z.2)
    else 0
  have hG : StronglyMeasurable G := by
    apply Measurable.stronglyMeasurable
    dsimp only [G]
    apply Measurable.ite
      (measurableSet_Ioi.preimage measurable_snd)
    · apply (by fun_prop : Measurable (fun z : Real × Real =>
          (((z.2 ^ (-(3 : Real) / 2) : Real) : Complex)))).mul
      exact measurable_e_comp (by fun_prop)
    · exact measurable_const
  have hEq :
      (fun c : Real => eq112TruncatedBesselKernel a c delta) =
        fun c : Real => ∫ t : Real, G (c, t) := by
    funext c
    unfold eq112TruncatedBesselKernel
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with t
    by_cases ht : t ∈ Set.Ioi delta
    · simp only [Set.indicator_of_mem ht, G, ht, if_pos]
    · simp only [Set.indicator_of_notMem ht]
      dsimp only [G]
      rw [if_neg ht]
  rw [hEq]
  exact hG.integral_prod_right.measurable

/-! ## Quadratic comparison at the stationary frequency -/

/-- Chord length on the unit circle is at most arc length in the project's
`e(t) = exp(2*pi*I*t)` normalization. -/
private theorem norm_e_sub_e_le (x y : Real) :
    norm (e x - e y) ≤ 2 * Real.pi * abs (x - y) := by
  have hfactor : e x - e y = e y * (e (x - y) - 1) := by
    rw [mul_sub, mul_one, ← KL.e_add]
    congr 2
    ring
  rw [hfactor, norm_mul, norm_e, one_mul]
  have heq : e (x - y) =
      Complex.exp (Complex.I * ((2 * Real.pi * (x - y) : Real) : Complex)) := by
    unfold e
    congr 1
    push_cast
    ring
  rw [heq]
  calc
    norm (Complex.exp
        (Complex.I * ((2 * Real.pi * (x - y) : Real) : Complex)) - 1) ≤
        norm (2 * Real.pi * (x - y)) :=
      Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * abs (x - y) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_pos (by norm_num : (0 : Real) < 2),
        abs_of_pos Real.pi_pos]

/-- The reciprocal cube of `sqrt b` is the negative three-halves power used
in the catalogue statement. -/
private theorem eq112_inv_sqrt_cube {b : Real} (hb : 0 < b) :
    ((Real.sqrt b) ^ 3)⁻¹ = b ^ (-(3 : Real) / 2) := by
  rw [show -(3 : Real) / 2 = -((3 : Real) / 2) by ring,
    Real.rpow_neg hb.le]
  congr 1
  rw [show (3 : Real) / 2 = 1 + (1 : Real) / 2 by ring,
    Real.rpow_add hb 1 ((1 : Real) / 2), Real.rpow_one,
    ← Real.sqrt_eq_rpow]
  rw [← Real.sq_sqrt hb.le]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (Real.sqrt_nonneg b)]
  ring

/-- Exact algebraic second-order remainder for the square root, in a form
whose denominator is manifestly positive. -/
private theorem sqrt_linear_remainder_le {b y : Real}
    (hb : 0 < b) (hy : 2 * abs y < b) :
    abs (Real.sqrt (b - y) - Real.sqrt b +
        y / (2 * Real.sqrt b)) ≤
      y ^ 2 / (2 * Real.sqrt b ^ 3) := by
  have hby : 0 < b - y := by
    have hyLe : y ≤ abs y := le_abs_self y
    linarith
  let r : Real := Real.sqrt b
  let d : Real := Real.sqrt (b - y)
  have hr : 0 < r := Real.sqrt_pos.2 hb
  have hd : 0 < d := Real.sqrt_pos.2 hby
  have hr2 : r ^ 2 = b := Real.sq_sqrt hb.le
  have hd2 : d ^ 2 = b - y := Real.sq_sqrt hby.le
  have hyFactor : y = (r - d) * (r + d) := by
    nlinarith
  have hdiff : abs (r - d) ≤ abs y / r := by
    rw [le_div_iff₀ hr, hyFactor, abs_mul,
      abs_of_pos (add_pos hr hd)]
    exact mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right hd.le) (abs_nonneg (r - d))
  have hsq : (r - d) ^ 2 ≤ (abs y / r) ^ 2 := by
    rw [← sq_abs (r - d)]
    exact pow_le_pow_left₀ (abs_nonneg _) hdiff 2
  have hidentity :
      d - r + y / (2 * r) = -(r - d) ^ 2 / (2 * r) := by
    rw [hyFactor]
    field_simp [hr.ne']
    ring
  change abs (d - r + y / (2 * r)) ≤ y ^ 2 / (2 * r ^ 3)
  rw [hidentity, abs_div, abs_neg, abs_of_nonneg (sq_nonneg _),
    abs_of_pos (mul_pos (by norm_num) hr)]
  calc
    (r - d) ^ 2 / (2 * r) ≤ (abs y / r) ^ 2 / (2 * r) :=
      (div_le_div_iff_of_pos_right (mul_pos (by norm_num) hr)).2 hsq
    _ = y ^ 2 / (2 * r ^ 3) := by
      rw [div_pow, sq_abs]
      field_simp [hr.ne']

/-- The two real phases agree to first order at `y = 0`. -/
private theorem eq112_phase_remainder_le {a b y : Real}
    (ha : 0 < a) (hb : 0 < b) (hy : 2 * abs y < b) :
    abs ((-2 * Real.sqrt (a * (b - y))) -
        (-2 * Real.sqrt (a * b) + Real.sqrt (a / b) * y)) ≤
      Real.sqrt a * b ^ (-(3 : Real) / 2) * y ^ 2 := by
  have hby : 0 < b - y := by
    have hyLe : y ≤ abs y := le_abs_self y
    linarith
  rw [Real.sqrt_mul ha.le, Real.sqrt_mul ha.le,
    Real.sqrt_div ha.le b]
  have hsqrtb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hrewrite :
      (-2 * (Real.sqrt a * Real.sqrt (b - y))) -
          (-2 * (Real.sqrt a * Real.sqrt b) +
            Real.sqrt a / Real.sqrt b * y) =
        -2 * Real.sqrt a *
          (Real.sqrt (b - y) - Real.sqrt b +
            y / (2 * Real.sqrt b)) := by
    field_simp [hsqrtb.ne']
    ring
  rw [hrewrite, abs_mul, abs_mul,
    abs_of_neg (by norm_num : (-2 : Real) < 0),
    abs_of_nonneg (Real.sqrt_nonneg a)]
  norm_num only [neg_neg]
  have hroot := sqrt_linear_remainder_le hb hy
  calc
    2 * Real.sqrt a *
        abs (Real.sqrt (b - y) - Real.sqrt b +
          y / (2 * Real.sqrt b)) ≤
        2 * Real.sqrt a * (y ^ 2 / (2 * Real.sqrt b ^ 3)) :=
      mul_le_mul_of_nonneg_left hroot
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg a))
    _ = Real.sqrt a * b ^ (-((3 : Real) / 2)) * y ^ 2 := by
      rw [show -((3 : Real) / 2) = -(3 : Real) / 2 by ring]
      rw [← eq112_inv_sqrt_cube hb]
      field_simp [hsqrtb.ne']

/-- In the central window the exact positive-frequency multiplier has the
quadratic Taylor error responsible for the `b^(-3/2)` term in (11.3). -/
private theorem eq112_multiplier_central {a b y : Real}
    (ha : 0 < a) (hb : 0 < b) (hy : 2 * abs y < b) :
    norm (eq112BesselMultiplier a (b - y) -
        eq112BesselMultiplier a b * e (Real.sqrt (a / b) * y)) ≤
      8 * b ^ (-(3 : Real) / 2) * y ^ 2 := by
  have hby : 0 < b - y := by
    have hyLe : y ≤ abs y := le_abs_self y
    linarith
  rw [eq112BesselMultiplier_at_pos hby,
    eq112BesselMultiplier_at_pos hb]
  rw [show eq112BesselAmplitude a * e (-2 * Real.sqrt (a * (b - y))) -
      eq112BesselAmplitude a * e (-2 * Real.sqrt (a * b)) *
        e (Real.sqrt (a / b) * y) =
      eq112BesselAmplitude a *
        (e (-2 * Real.sqrt (a * (b - y))) -
          e (-2 * Real.sqrt (a * b)) * e (Real.sqrt (a / b) * y)) by ring,
    ← KL.e_add]
  rw [norm_mul]
  have hphase := eq112_phase_remainder_le ha hb hy
  have hexp := norm_e_sub_e_le
    (-2 * Real.sqrt (a * (b - y)))
    (-2 * Real.sqrt (a * b) + Real.sqrt (a / b) * y)
  have hsqrta : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hcancel :
      a ^ (-(1 : Real) / 2) * Real.sqrt a = 1 := by
    rw [← eq112_inv_sqrt_eq_rpow ha]
    exact inv_mul_cancel₀ hsqrta.ne'
  calc
    norm (eq112BesselAmplitude a) *
        norm (e (-2 * Real.sqrt (a * (b - y))) -
          e (-2 * Real.sqrt (a * b) + Real.sqrt (a / b) * y)) ≤
        a ^ (-(1 : Real) / 2) *
          (2 * Real.pi * abs
            ((-2 * Real.sqrt (a * (b - y))) -
              (-2 * Real.sqrt (a * b) + Real.sqrt (a / b) * y))) :=
      mul_le_mul (norm_eq112BesselAmplitude_le ha) hexp
        (norm_nonneg _) (Real.rpow_nonneg ha.le _)
    _ ≤ a ^ (-(1 : Real) / 2) *
        (2 * Real.pi *
          (Real.sqrt a * b ^ (-(3 : Real) / 2) * y ^ 2)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hphase (by positivity))
        (Real.rpow_nonneg ha.le _)
    _ = (2 * Real.pi) * b ^ (-(3 : Real) / 2) * y ^ 2 := by
      calc
        a ^ (-(1 : Real) / 2) *
            (2 * Real.pi *
              (Real.sqrt a * b ^ (-(3 : Real) / 2) * y ^ 2)) =
            (2 * Real.pi) *
              (a ^ (-(1 : Real) / 2) * Real.sqrt a) *
                b ^ (-(3 : Real) / 2) * y ^ 2 := by ring
        _ = (2 * Real.pi) * b ^ (-(3 : Real) / 2) * y ^ 2 := by
          rw [hcancel]
          ring
    _ ≤ 8 * b ^ (-(3 : Real) / 2) * y ^ 2 := by
      have hpi : 2 * Real.pi ≤ 8 := by
        nlinarith [Real.pi_le_four]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpi
          (Real.rpow_nonneg hb.le _)) (sq_nonneg y)

/-- Away from the central window, boundedness alone yields the second term
in (11.3). -/
private theorem eq112_multiplier_far {a b y : Real}
    (ha : 0 < a) (hb : 0 < b) (hy : b ≤ 2 * abs y) :
    norm (eq112BesselMultiplier a (b - y) -
        eq112BesselMultiplier a b * e (Real.sqrt (a / b) * y)) ≤
      8 * (a ^ (-(1 : Real) / 2) * b ^ (-(2 : Real))) * y ^ 2 := by
  have hfirst := norm_eq112BesselMultiplier_le (c := b - y) ha
  have hsecond :
      norm (eq112BesselMultiplier a b * e (Real.sqrt (a / b) * y)) ≤
        a ^ (-(1 : Real) / 2) := by
    rw [norm_mul, norm_e, mul_one]
    exact norm_eq112BesselMultiplier_le ha
  have hnorm :
      norm (eq112BesselMultiplier a (b - y) -
        eq112BesselMultiplier a b * e (Real.sqrt (a / b) * y)) ≤
          2 * a ^ (-(1 : Real) / 2) := by
    calc
      _ ≤ norm (eq112BesselMultiplier a (b - y)) +
          norm (eq112BesselMultiplier a b * e (Real.sqrt (a / b) * y)) :=
        norm_sub_le _ _
      _ ≤ a ^ (-(1 : Real) / 2) + a ^ (-(1 : Real) / 2) :=
        add_le_add hfirst hsecond
      _ = 2 * a ^ (-(1 : Real) / 2) := by ring
  have hySq : b ^ 2 ≤ 4 * y ^ 2 := by
    have hsquare := (sq_le_sq₀ hb.le (by positivity)).2 hy
    nlinarith [sq_abs y]
  have hbpow : b ^ (-(2 : Real)) = (b ^ 2)⁻¹ := by
    rw [show -(2 : Real) = -((2 : Nat) : Real) by norm_num,
      Real.rpow_neg hb.le, Real.rpow_natCast]
  have hfactor : 2 ≤ 8 * b ^ (-(2 : Real)) * y ^ 2 := by
    rw [hbpow]
    calc
      2 = (2 * b ^ 2) / b ^ 2 := by
        field_simp [hb.ne']
      _ ≤ (8 * y ^ 2) / b ^ 2 :=
        (div_le_div_iff_of_pos_right (pow_pos hb 2)).2 (by nlinarith)
      _ = 8 * (b ^ 2)⁻¹ * y ^ 2 := by
        field_simp [hb.ne']
  exact hnorm.trans <| by
    calc
      2 * a ^ (-(1 : Real) / 2) ≤
          (8 * b ^ (-(2 : Real)) * y ^ 2) *
            a ^ (-(1 : Real) / 2) :=
        mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg ha.le _)
      _ = 8 * (a ^ (-(1 : Real) / 2) * b ^ (-(2 : Real))) * y ^ 2 := by
        ring

/-- The complete pointwise multiplier estimate underlying (11.3).  The
constant `8` is deliberately elementary rather than optimized. -/
theorem eq112_besselMultiplier_quadratic_bound
    {a b : Real} (ha : 0 < a) (hb : 0 < b) (y : Real) :
    norm (eq112BesselMultiplier a (b - y) -
        eq112BesselMultiplier a b * e (Real.sqrt (a / b) * y)) ≤
      8 * (b ^ (-(3 : Real) / 2) +
        a ^ (-(1 : Real) / 2) * b ^ (-(2 : Real))) * y ^ 2 := by
  by_cases hy : 2 * abs y < b
  · have h := eq112_multiplier_central ha hb hy
    exact h.trans <| by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right
            (mul_nonneg (Real.rpow_nonneg ha.le _)
              (Real.rpow_nonneg hb.le _))) (by norm_num)
      · exact sq_nonneg y
  · have hfar : b ≤ 2 * abs y := le_of_not_gt hy
    have h := eq112_multiplier_far ha hb hfar
    exact h.trans <| by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (Real.rpow_nonneg hb.le _)) (by norm_num)
      · exact sq_nonneg y

/-! ## The exact remaining transform identity -/

/-- The genuinely new pointwise transform evaluation needed beyond (11.5).
The positive-frequency case is `eq112_besselMultiplier_positive_limit`, and
the zero endpoint is `eq112_besselMultiplier_zero_limit`; this statement
contains precisely the remaining strictly negative nonstationary branch. -/
def IwaniecMozzochiEq112NegativeBesselLimit : Prop :=
  ∀ (a c : Real), 0 < a → c < 0 →
    Tendsto
      (eq112TruncatedBesselKernel a c)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (eq112BesselMultiplier a c))

/-- The uniform oscillatory estimate that makes cutoff removal compatible
with Fourier inversion.  Absolute values inside the reciprocal-Bessel
integral only give a `delta^(-1/2)` bound, so a uniform estimate of this kind
must use phase cancellation.  Uniformity in `c` is exactly what is needed
when `c = b - y` ranges over the whole Fourier line. -/
def IwaniecMozzochiEq112UniformTruncatedBound : Prop :=
  ∃ C : Real, 0 ≤ C ∧
    ∀ (a c delta : Real), 0 < a → 0 < delta →
      norm (eq112TruncatedBesselKernel a c delta) ≤
        C * a ^ (-(1 : Real) / 2)

/-- The cutoff kernel has the frequency-uniform bound needed for dominated
convergence.  After `t = a/u^2`, this is exactly the uniform partial-integral
estimate for `e(-u^2-(a*c)/u^2)`; the remaining factor is `2/sqrt(a)`. -/
theorem iwaniecMozzochi_eq112_uniformTruncatedBound_holds :
    IwaniecMozzochiEq112UniformTruncatedBound := by
  obtain ⟨B, hB, hnormalized⟩ :=
    ReciprocalQuadratic.exists_uniform_intervalIntegral_bound
  refine ⟨2 * B, by positivity, ?_⟩
  intro a c delta ha hdelta
  have hchange :=
    Eq115Change.iwaniecMozzochi_eq112_truncatedChangeOfVariables
      (a := a) (c := c) (δ := delta) ha hdelta
  have hU : 0 ≤ Real.sqrt (a / delta) := Real.sqrt_nonneg _
  have hbound := hnormalized (a * c) (Real.sqrt (a / delta)) hU
  unfold eq112TruncatedBesselKernel
  rw [hchange]
  calc
    norm (((2 / Real.sqrt a : Real) : Complex) *
        (∫ u in (0 : Real)..Real.sqrt (a / delta),
          e (-(u ^ 2) - (a * c) / u ^ 2))) =
        (2 / Real.sqrt a) *
          norm (∫ u in (0 : Real)..Real.sqrt (a / delta),
            e (-(u ^ 2) - (a * c) / u ^ 2)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (div_pos (by norm_num) (Real.sqrt_pos.2 ha))]
    _ ≤ (2 / Real.sqrt a) * B := by
      apply mul_le_mul_of_nonneg_left _
        (div_nonneg (by norm_num) (Real.sqrt_nonneg _))
      simpa only [ReciprocalQuadratic.phase] using hbound
    _ = (2 * B) * a ^ (-(1 : Real) / 2) := by
      rw [div_eq_mul_inv, eq112_inv_sqrt_eq_rpow ha]
      ring

/-- Combining the already proved positive branch with the exact residual
nonpositive branch gives the pointwise generalized Bessel limit for every
real linear frequency. -/
theorem eq112_besselMultiplier_limit_of_negative
    (hnegative : IwaniecMozzochiEq112NegativeBesselLimit)
    {a c : Real} (ha : 0 < a) :
    Tendsto
      (eq112TruncatedBesselKernel a c)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (eq112BesselMultiplier a c)) := by
  by_cases hc : 0 < c
  · exact eq112_besselMultiplier_positive_limit ha hc
  · by_cases hc0 : c = 0
    · subst c
      exact eq112_besselMultiplier_zero_limit ha
    · exact hnegative a c ha (lt_of_le_of_ne (le_of_not_gt hc) hc0)

/-- Compatibility wrapper for the exact transform identity used by the
downstream remainder proof.  It is derived below from the two smaller analytic
inputs, rather than being treated as a monolithic premise. -/
def IwaniecMozzochiLemma111BesselFourierRepresentation : Prop :=
  forall (f : Real -> Real) (a b : Real),
    IsSmoothCompactPos f -> 0 < a -> 0 < b ->
      incompleteBessel f a b =
        ∫ y : Real,
          (FourierTransform.fourier
            (fun t : Real => (f t : Complex)) y) *
              eq112BesselMultiplier a (b - y)

/-! ## Fourier inversion and the catalogue remainder -/

private theorem eq112_fourier_inversion
    {f : Real -> Real} (hf : IsSmoothCompactPos f) (x : Real) :
    (f x : Complex) =
      ∫ y : Real,
        FourierTransform.fourier (fun t : Real => (f t : Complex)) y *
          e (x * y) := by
  let fc : Real -> Complex := Complex.ofRealCLM ∘ f
  have hfcCompact : HasCompactSupport fc := by
    dsimp only [fc]
    exact hf.2.1.comp_left rfl
  have hfcSmooth : ContDiff Real ∞ fc := by
    dsimp only [fc]
    exact Complex.ofRealCLM.contDiff.comp hf.1
  let phi : 𝓢(Real, Complex) := hfcCompact.toSchwartzMap hfcSmooth
  have hphiFun : (phi : Real -> Complex) = fc := rfl
  have hfcIntegrable : Integrable fc := phi.integrable
  have hfourierIntegrable : Integrable (FourierTransform.fourier fc) := by
    rw [← hphiFun, ← SchwartzMap.fourier_coe]
    exact (FourierTransform.fourier phi).integrable
  change fc x = ∫ y : Real,
    FourierTransform.fourier fc y * e (x * y)
  have hinv := congrFun
    (hfcSmooth.continuous.fourierInv_fourier_eq
      hfcIntegrable hfourierIntegrable) x
  rw [Real.fourierInv_eq'] at hinv
  rw [← hinv]
  apply integral_congr_ae
  filter_upwards with y
  simp only [Real.inner_apply, smul_eq_mul]
  rw [mul_comm]
  congr 1
  unfold e
  congr 1
  push_cast
  ring

private theorem eq112_fourier_integrable
    {f : Real -> Real} (hf : IsSmoothCompactPos f) :
    Integrable (FourierTransform.fourier
      (fun t : Real => (f t : Complex))) := by
  let fc : Real -> Complex := Complex.ofRealCLM ∘ f
  have hfcCompact : HasCompactSupport fc := by
    dsimp only [fc]
    exact hf.2.1.comp_left rfl
  have hfcSmooth : ContDiff Real ∞ fc := by
    dsimp only [fc]
    exact Complex.ofRealCLM.contDiff.comp hf.1
  let phi : 𝓢(Real, Complex) := hfcCompact.toSchwartzMap hfcSmooth
  have hphiFun : (phi : Real -> Complex) = fc := rfl
  change Integrable (FourierTransform.fourier fc)
  rw [← hphiFun, ← SchwartzMap.fourier_coe]
  exact (FourierTransform.fourier phi).integrable

/-- With a positive lower cutoff, Fourier inversion and the reciprocal-Bessel
integral may be interchanged by ordinary Fubini.  The proof is absolutely
convergent: the cutoff makes `t^(-3/2)` integrable, while the Fourier transform
of the compactly supported smooth function is in `L^1`. -/
private theorem eq112_truncated_fourier_representation
    {f : Real -> Real} (hf : IsSmoothCompactPos f)
    {a b delta : Real} (hdelta : 0 < delta) :
    (∫ t in Set.Ioi delta,
      (((t ^ (-(3 : Real) / 2) * f t : Real) : Complex) *
        e (-a / t - b * t))) =
      ∫ y : Real,
        FourierTransform.fourier (fun t : Real => (f t : Complex)) y *
          eq112TruncatedBesselKernel a (b - y) delta := by
  let fhat : Real -> Complex := fun y =>
    FourierTransform.fourier (fun t : Real => (f t : Complex)) y
  let g : Real -> Complex := fun t =>
    Set.indicator (Set.Ioi delta) (fun u : Real =>
      ((u ^ (-(3 : Real) / 2) : Real) : Complex) *
        e (-a / u - b * u)) t
  have hfhat : Integrable fhat := by
    simpa only [fhat] using eq112_fourier_integrable hf
  have hg : Integrable g := by
    simpa only [g] using
      (eq112_truncatedKernel_integrable
        (a := a) (c := b) (delta := delta) hdelta)
  have hbase : Integrable (fun z : Real × Real =>
      g z.1 * fhat z.2) (volume.prod volume) :=
    hg.mul_prod hfhat
  have hphase : AEStronglyMeasurable (fun z : Real × Real =>
      e (z.1 * z.2)) := by
    have hphaseContinuous : Continuous (fun z : Real × Real => z.1 * z.2) := by
      fun_prop
    exact (measurable_e_comp hphaseContinuous.measurable).aestronglyMeasurable
  have hprod : Integrable (fun z : Real × Real =>
      (g z.1 * fhat z.2) * e (z.1 * z.2)) (volume.prod volume) :=
    hbase.mul_bdd (c := 1) hphase
      (Eventually.of_forall fun z => by rw [norm_e])
  calc
    (∫ t in Set.Ioi delta,
        (((t ^ (-(3 : Real) / 2) * f t : Real) : Complex) *
          e (-a / t - b * t))) =
        ∫ t : Real, ∫ y : Real,
          (g t * fhat y) * e (t * y) := by
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with t
      have hinner :
          (∫ y : Real, (g t * fhat y) * e (t * y)) =
            g t * (f t : Complex) := by
        calc
          (∫ y : Real, (g t * fhat y) * e (t * y)) =
              g t * ∫ y : Real, fhat y * e (t * y) := by
            rw [← MeasureTheory.integral_const_mul]
            apply integral_congr_ae
            filter_upwards with y
            ring
          _ = g t * (f t : Complex) := by
            rw [← eq112_fourier_inversion hf t]
      rw [hinner]
      by_cases ht : t ∈ Set.Ioi delta
      · simp only [g, Set.indicator_of_mem ht]
        push_cast
        ring
      · simp [g, Set.indicator_of_notMem ht]
    _ = ∫ y : Real, ∫ t : Real,
          (g t * fhat y) * e (t * y) := by
      exact MeasureTheory.integral_integral_swap hprod
    _ = ∫ y : Real,
        fhat y * eq112TruncatedBesselKernel a (b - y) delta := by
      apply integral_congr_ae
      filter_upwards with y
      calc
        (∫ t : Real, (g t * fhat y) * e (t * y)) =
            ∫ t : Real, Set.indicator (Set.Ioi delta)
              (fun u : Real => fhat y *
                (((u ^ (-(3 : Real) / 2) : Real) : Complex) *
                  e (-a / u - (b - y) * u))) t := by
          apply integral_congr_ae
          filter_upwards with t
          by_cases ht : t ∈ Set.Ioi delta
          · simp only [g, Set.indicator_of_mem ht]
            rw [show -a / t - (b - y) * t =
                (-a / t - b * t) + t * y by ring, KL.e_add]
            ring
          · simp [g, Set.indicator_of_notMem ht]
        _ = ∫ t in Set.Ioi delta, fhat y *
              (((t ^ (-(3 : Real) / 2) : Real) : Complex) *
                e (-a / t - (b - y) * t)) := by
          rw [integral_indicator measurableSet_Ioi]
        _ = fhat y * eq112TruncatedBesselKernel a (b - y) delta := by
          rw [MeasureTheory.integral_const_mul]
          rfl

/-- A compact support contained in `(0, infinity)` is separated from zero.
Consequently, once the lower cutoff lies below that separation, inserting the
cutoff does not alter the incomplete Bessel integral. -/
private theorem eq112_incompleteBessel_eq_truncated_of_support_gap
    {f : Real -> Real} {a b epsilon delta : Real}
    (hsupport : ∀ t ∈ tsupport f, epsilon ≤ t)
    (hdelta : 0 < delta) (hdeltaepsilon : delta < epsilon) :
    incompleteBessel f a b =
      ∫ t in Set.Ioi delta,
        (((t ^ (-(3 : Real) / 2) * f t : Real) : Complex) *
          e (-a / t - b * t)) := by
  unfold incompleteBessel
  rw [← integral_indicator measurableSet_Ioi,
    ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with t
  by_cases htDelta : t ∈ Set.Ioi delta
  · have htZero : t ∈ Set.Ioi (0 : Real) := hdelta.trans htDelta
    simp [Set.indicator_of_mem htDelta, Set.indicator_of_mem htZero]
  · by_cases htZero : t ∈ Set.Ioi (0 : Real)
    · have htLe : t ≤ delta := le_of_not_gt htDelta
      have hft : f t = 0 := by
        by_contra hne
        have htSupport : t ∈ tsupport f := subset_tsupport f hne
        have := hsupport t htSupport
        linarith
      simp [Set.indicator_of_mem htZero,
        Set.indicator_of_notMem htDelta, hft]
    · simp [Set.indicator_of_notMem htZero,
        Set.indicator_of_notMem htDelta]

private theorem eq112_secondMoment_integrable
    {f : Real -> Real} (hf : IsSmoothCompactPos f) :
    Integrable (fun y : Real =>
      y ^ 2 * norm (FourierTransform.fourier
        (fun t : Real => (f t : Complex)) y)) := by
  let fc : Real -> Complex := Complex.ofRealCLM ∘ f
  have hfcCompact : HasCompactSupport fc := by
    dsimp only [fc]
    exact hf.2.1.comp_left rfl
  have hfcSmooth : ContDiff Real ∞ fc := by
    dsimp only [fc]
    exact Complex.ofRealCLM.contDiff.comp hf.1
  let phi : 𝓢(Real, Complex) := hfcCompact.toSchwartzMap hfcSmooth
  have hphiFun : (phi : Real -> Complex) = fc := rfl
  change Integrable (fun y : Real =>
    y ^ 2 * norm (FourierTransform.fourier fc y))
  have hpoly : Function.HasTemperateGrowth
      (fun y : Real => (y : Complex) ^ 2) := by
    fun_prop
  let W : 𝓢(Real, Complex) :=
    SchwartzMap.smulLeftCLM Complex
      (fun y : Real => (y : Complex) ^ 2) (FourierTransform.fourier phi)
  have hWApply (y : Real) :
      W y = (y : Complex) ^ 2 * FourierTransform.fourier phi y := by
    simp only [W, SchwartzMap.smulLeftCLM_apply_apply hpoly, smul_eq_mul]
  have hWIntegrable : Integrable (fun y : Real => norm (W y)) :=
    (W.integrable.norm)
  refine hWIntegrable.congr (Eventually.of_forall fun y => ?_)
  change norm (W y) = y ^ 2 * norm (FourierTransform.fourier fc y)
  rw [hWApply, SchwartzMap.fourier_coe, hphiFun]
  simp only [norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

private theorem eq112_multiplier_measurable (a : Real) :
    Measurable (fun y : Real => eq112BesselMultiplier a y) := by
  unfold eq112BesselMultiplier
  apply measurable_const.mul
  apply Measurable.ite measurableSet_Ioi
  · exact (GK32.continuous_e_comp (by fun_prop)).measurable
  · exact (by fun_prop : Continuous (fun y : Real =>
        ((Real.exp (-4 * Real.pi * Real.sqrt (a * abs y)) : Real) : Complex))).measurable

/-- Pointwise convergence of the generalized reciprocal-Bessel kernel and a
uniform truncated-kernel estimate imply the required cutoff-limit/Fourier
interchange.  This is exactly Mathlib's filter-form dominated convergence
theorem, with `C * a^(-1/2) * |fhat(y)|` as the integrable majorant. -/
private theorem eq112_cutoff_fourier_limit_of_negative_uniform
    (hnegative : IwaniecMozzochiEq112NegativeBesselLimit)
    (huniform : IwaniecMozzochiEq112UniformTruncatedBound)
    {f : Real -> Real} (hf : IsSmoothCompactPos f)
    {a b : Real} (ha : 0 < a) :
    Tendsto
      (fun delta : Real => ∫ y : Real,
        FourierTransform.fourier (fun t : Real => (f t : Complex)) y *
          eq112TruncatedBesselKernel a (b - y) delta)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ y : Real,
        FourierTransform.fourier (fun t : Real => (f t : Complex)) y *
          eq112BesselMultiplier a (b - y))) := by
  rcases huniform with ⟨C, hC, hbound⟩
  let fhat : Real -> Complex := fun y =>
    FourierTransform.fourier (fun t : Real => (f t : Complex)) y
  let scale : Real := C * a ^ (-(1 : Real) / 2)
  have hfhat : Integrable fhat := by
    simpa only [fhat] using eq112_fourier_integrable hf
  have hscale : 0 ≤ scale := by
    exact mul_nonneg hC (Real.rpow_nonneg ha.le _)
  have hmajor : Integrable (fun y : Real => scale * norm (fhat y)) :=
    hfhat.norm.const_mul scale
  have hmeas : ∀ᶠ delta in nhdsWithin (0 : Real) (Set.Ioi 0),
      AEStronglyMeasurable (fun y : Real =>
        fhat y * eq112TruncatedBesselKernel a (b - y) delta) := by
    exact Eventually.of_forall fun delta =>
      hfhat.aestronglyMeasurable.mul
        (((eq112_truncatedBesselKernel_measurable a delta).comp
          (by fun_prop)).aestronglyMeasurable)
  have hdominated : ∀ᶠ delta in nhdsWithin (0 : Real) (Set.Ioi 0),
      ∀ᵐ y ∂volume,
        norm (fhat y * eq112TruncatedBesselKernel a (b - y) delta) ≤
          scale * norm (fhat y) := by
    filter_upwards [self_mem_nhdsWithin] with delta hdelta
    exact Eventually.of_forall fun y => by
      rw [norm_mul]
      calc
        norm (fhat y) *
            norm (eq112TruncatedBesselKernel a (b - y) delta) ≤
            norm (fhat y) * (C * a ^ (-(1 : Real) / 2)) :=
          mul_le_mul_of_nonneg_left
            (hbound a (b - y) delta ha hdelta) (norm_nonneg _)
        _ = scale * norm (fhat y) := by
          dsimp only [scale]
          ring
  have hpointwise : ∀ᵐ y ∂volume,
      Tendsto
        (fun delta : Real =>
          fhat y * eq112TruncatedBesselKernel a (b - y) delta)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (fhat y * eq112BesselMultiplier a (b - y))) :=
    Eventually.of_forall fun y =>
      tendsto_const_nhds.mul
        (eq112_besselMultiplier_limit_of_negative
          hnegative ha)
  simpa only [fhat] using
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun y : Real => scale * norm (fhat y))
      hmeas hdominated hmajor hpointwise

/-- The two honest analytic inputs above imply the exact Bessel--Fourier
representation.  Everything else in the proof is ordinary fixed-cutoff
Fubini, compact-support separation from zero, and dominated convergence. -/
theorem iwaniecMozzochi_lemma111_besselFourierRepresentation_of_negative_uniform
    (hnegative : IwaniecMozzochiEq112NegativeBesselLimit)
    (huniform : IwaniecMozzochiEq112UniformTruncatedBound) :
    IwaniecMozzochiLemma111BesselFourierRepresentation := by
  intro f a b hf ha _hb
  obtain ⟨epsilon, hepsilon, hsupport⟩ :=
    hf.2.1.exists_forall_le'
      (f := fun t : Real => t) continuous_id.continuousOn
      (a := (0 : Real)) (fun t ht => hf.2.2 ht)
  have hlimit :=
    eq112_cutoff_fourier_limit_of_negative_uniform
      hnegative huniform hf (a := a) (b := b) ha
  have heventually :
      (fun delta : Real => ∫ y : Real,
        FourierTransform.fourier (fun t : Real => (f t : Complex)) y *
          eq112TruncatedBesselKernel a (b - y) delta) =ᶠ[
        nhdsWithin 0 (Set.Ioi 0)]
      (fun _ : Real => incompleteBessel f a b) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hepsilon)]
      with delta hdelta hdeltaepsilon
    calc
      (∫ y : Real,
          FourierTransform.fourier (fun t : Real => (f t : Complex)) y *
            eq112TruncatedBesselKernel a (b - y) delta) =
          (∫ t in Set.Ioi delta,
            (((t ^ (-(3 : Real) / 2) * f t : Real) : Complex) *
              e (-a / t - b * t))) :=
        (eq112_truncated_fourier_representation hf hdelta).symm
      _ = incompleteBessel f a b :=
        (eq112_incompleteBessel_eq_truncated_of_support_gap
          hsupport hdelta hdeltaepsilon).symm
  have hconstant := hlimit.congr' heventually
  letI : NeBot (nhdsWithin (0 : Real) (Set.Ioi 0)) :=
    mem_closure_iff_nhdsWithin_neBot.mp (by simp)
  exact (tendsto_nhds_unique hconstant tendsto_const_nhds).symm

/-- Once the universal reciprocal-quadratic estimate is supplied above, the
strictly negative pointwise transform evaluation is the only analytic input
left in the Bessel--Fourier representation. -/
theorem iwaniecMozzochi_lemma111_besselFourierRepresentation_of_negative
    (hnegative : IwaniecMozzochiEq112NegativeBesselLimit) :
    IwaniecMozzochiLemma111BesselFourierRepresentation :=
  iwaniecMozzochi_lemma111_besselFourierRepresentation_of_negative_uniform
    hnegative iwaniecMozzochi_eq112_uniformTruncatedBound_holds

/-- The exact Bessel--Fourier representation implies the complete catalogue
statement (11.2)/(11.3), with the explicit absolute constant `8`. -/
theorem iwaniecMozzochi_lemma111_eq112_eq113_of_besselFourierRepresentation
    (hrepresentation : IwaniecMozzochiLemma111BesselFourierRepresentation) :
    iwaniecMozzochi_lemma111_eq112_eq113 := by
  refine ⟨8, ?_⟩
  intro f a b hf ha hb
  let fhat : Real -> Complex := fun y =>
    FourierTransform.fourier (fun t : Real => (f t : Complex)) y
  let t0 : Real := Real.sqrt (a / b)
  let base : Real := b ^ (-(3 : Real) / 2) +
    a ^ (-(1 : Real) / 2) * b ^ (-(2 : Real))
  have hrepr := hrepresentation f a b hf ha hb
  have hinv := eq112_fourier_inversion hf t0
  have hmultb := eq112BesselMultiplier_at_pos (a := a) hb
  have hFhatIntegrable : Integrable fhat := by
    simpa only [fhat] using eq112_fourier_integrable hf
  have hmomentIntegrable : Integrable (fun y : Real => y ^ 2 * norm (fhat y)) := by
    simpa only [fhat] using eq112_secondMoment_integrable hf
  have hphaseMeasurable : AEStronglyMeasurable (fun y : Real => e (t0 * y)) :=
    (GK32.continuous_e_comp (by fun_prop)).aestronglyMeasurable
  have hphaseIntegrable : Integrable (fun y : Real => fhat y * e (t0 * y)) :=
    hFhatIntegrable.mul_bdd (c := 1) hphaseMeasurable
      (Eventually.of_forall fun y => by rw [norm_e])
  have hshiftMeasurable : AEStronglyMeasurable
      (fun y : Real => eq112BesselMultiplier a (b - y)) := by
    exact ((eq112_multiplier_measurable a).comp (by fun_prop)).aestronglyMeasurable
  have hshiftIntegrable : Integrable
      (fun y : Real => fhat y * eq112BesselMultiplier a (b - y)) :=
    hFhatIntegrable.mul_bdd (c := a ^ (-(1 : Real) / 2)) hshiftMeasurable
      (Eventually.of_forall fun y => norm_eq112BesselMultiplier_le ha)
  have hmainIntegrable : Integrable (fun y : Real =>
      eq112BesselMultiplier a b * (fhat y * e (t0 * y))) :=
    hphaseIntegrable.const_mul _
  have hdiff :
      incompleteBessel f a b -
          eq112BesselMultiplier a b * (f t0 : Complex) =
        ∫ y : Real,
          fhat y * (eq112BesselMultiplier a (b - y) -
            eq112BesselMultiplier a b * e (t0 * y)) := by
    rw [hrepr, hinv, ← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_sub hshiftIntegrable hmainIntegrable]
    apply integral_congr_ae
    filter_upwards with y
    dsimp only [fhat]
    ring
  have hdomIntegrable : Integrable
      (fun y : Real => (8 * base) * (y ^ 2 * norm (fhat y))) :=
    hmomentIntegrable.const_mul _
  have hnormIntegral :
      norm (∫ y : Real,
        fhat y * (eq112BesselMultiplier a (b - y) -
          eq112BesselMultiplier a b * e (t0 * y))) ≤
        ∫ y : Real, (8 * base) *
          (y ^ 2 * norm (fhat y)) := by
    apply MeasureTheory.norm_integral_le_of_norm_le hdomIntegrable
    exact Eventually.of_forall fun y => by
      rw [norm_mul]
      have hpoint := eq112_besselMultiplier_quadratic_bound ha hb y
      dsimp only [base, t0] at hpoint ⊢
      calc
        norm (fhat y) *
            norm (eq112BesselMultiplier a (b - y) -
              eq112BesselMultiplier a b * e (Real.sqrt (a / b) * y)) ≤
            norm (fhat y) * (8 * base * y ^ 2) :=
          mul_le_mul_of_nonneg_left hpoint (norm_nonneg _)
        _ = (8 * base) * (y ^ 2 * norm (fhat y)) := by ring
  change norm (incompleteBessel f a b -
      eq112BesselAmplitude a * e (-2 * Real.sqrt (a * b)) *
        (f t0 : Complex)) ≤ 8 * (base * secondMomentFourier f)
  rw [← hmultb, hdiff]
  calc
    norm (∫ y : Real,
        fhat y * (eq112BesselMultiplier a (b - y) -
          eq112BesselMultiplier a b * e (t0 * y))) ≤
        ∫ y : Real, (8 * base) *
          (y ^ 2 * norm (fhat y)) := hnormIntegral
    _ = 8 * (base * secondMomentFourier f) := by
      rw [MeasureTheory.integral_const_mul]
      unfold secondMomentFourier
      dsimp only [fhat]
      ring
    _ = 8 * ((b ^ (-(3 : Real) / 2) +
        a ^ (-(1 : Real) / 2) * b ^ (-(2 : Real))) *
          secondMomentFourier f) := by
      rfl

/-- With the already proved Fourier--Carlson estimate (11.4), the exact
transform identity is a sufficient compatibility interface for (11.7). -/
theorem iwaniecMozzochi_eq117_of_besselFourierRepresentation
    (hrepresentation : IwaniecMozzochiLemma111BesselFourierRepresentation) :
    iwaniecMozzochi_eq117 :=
  iwaniecMozzochi_eq117_of_lemma111
    (iwaniecMozzochi_lemma111_eq112_eq113_of_besselFourierRepresentation
      hrepresentation)
    iwaniecMozzochi_lemma111_eq114_holds

/-- Direct form of Lemma 11.1 from the two remaining oscillatory inputs. -/
theorem iwaniecMozzochi_lemma111_eq112_eq113_of_negative_uniform
    (hnegative : IwaniecMozzochiEq112NegativeBesselLimit)
    (huniform : IwaniecMozzochiEq112UniformTruncatedBound) :
    iwaniecMozzochi_lemma111_eq112_eq113 :=
  iwaniecMozzochi_lemma111_eq112_eq113_of_besselFourierRepresentation
    (iwaniecMozzochi_lemma111_besselFourierRepresentation_of_negative_uniform
      hnegative huniform)

/-- Direct form of (11.7) from the same two remaining oscillatory inputs. -/
theorem iwaniecMozzochi_eq117_of_negative_uniform
    (hnegative : IwaniecMozzochiEq112NegativeBesselLimit)
    (huniform : IwaniecMozzochiEq112UniformTruncatedBound) :
    iwaniecMozzochi_eq117 :=
  iwaniecMozzochi_eq117_of_besselFourierRepresentation
    (iwaniecMozzochi_lemma111_besselFourierRepresentation_of_negative_uniform
      hnegative huniform)

/-- Direct form of Lemma 11.1 from the sole remaining strictly negative
reciprocal-Bessel limit. -/
theorem iwaniecMozzochi_lemma111_eq112_eq113_of_negative
    (hnegative : IwaniecMozzochiEq112NegativeBesselLimit) :
    iwaniecMozzochi_lemma111_eq112_eq113 :=
  iwaniecMozzochi_lemma111_eq112_eq113_of_besselFourierRepresentation
    (iwaniecMozzochi_lemma111_besselFourierRepresentation_of_negative hnegative)

/-- Direct form of (11.7) from the same single analytic input. -/
theorem iwaniecMozzochi_eq117_of_negative
    (hnegative : IwaniecMozzochiEq112NegativeBesselLimit) :
    iwaniecMozzochi_eq117 :=
  iwaniecMozzochi_eq117_of_besselFourierRepresentation
    (iwaniecMozzochi_lemma111_besselFourierRepresentation_of_negative hnegative)

end

end LeanProofs.IntegerPoints
