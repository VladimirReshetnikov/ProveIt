import IntegerPoints.IwaniecMozzochi
import IntegerPoints.GKLemma33

/-!
# The Fresnel core of Iwaniec--Mozzochi (11.5)

Equation (11.5) is an improper oscillatory integral at the origin.  It is not
a consequence of the Fourier--Carlson argument used for (11.4).  Its analytic
constant is nevertheless already available from the quantitative Fresnel
estimate proved in `IntegerPoints.GKLemma33`.

This file makes that consequence explicit.  It proves, with Mathlib's
principal branch of complex power,

```
  lim_{X -> +infinity} integral_0^X e(-u^2) du
    = (2 * I)^(-1/2) / 2.
```

The remaining step towards (11.5) is isolated in two precise interfaces:

* `IwaniecMozzochiEq115ReciprocalPhaseLimit` is the genuinely oscillatory
  reciprocal phase-straightening identity for `u - c/u`;
* `IwaniecMozzochiEq115TruncatedChangeOfVariables` is the exact finite-
  truncation substitution `t = a/u^2`.

The latter is ordinary one-dimensional change of variables; it is kept
separate so that it cannot conceal any convergence or branch assumption.
Together these two explicitly stated inputs imply the catalogue proposition
`iwaniecMozzochi_eq115`, with its original quantifier order and one-sided
filter at `delta = 0`.

At the displayed interval integral's endpoint `u = 0`, Lean interprets
division by zero as zero.  This affects a singleton only and hence not the
integral.  Negative upper endpoints are also harmless: all limiting claims
use `Filter.atTop`, so the positive range is eventual.
-/

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace LeanProofs.IntegerPoints

/-- The undamped half-Fresnel partial integral in the normalization
`e(x) = exp(2 * pi * I * x)`. -/
noncomputable def eq115HalfFresnelIntegral (X : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..X, e (-(u ^ 2))

private theorem continuous_eq115HalfFresnelIntegrand :
    Continuous (fun u : ℝ => e (-(u ^ 2))) :=
  GK32.continuous_e_comp (by fun_prop)

private theorem eq115HalfFresnelIntegrand_even (u : ℝ) :
    e (-((-u) ^ 2)) = e (-(u ^ 2)) := by
  congr 1
  ring

/-- Evenness identifies a half-Fresnel integral with half of the symmetric
integral used in Graham--Kolesnik Lemma 3.3.  This identity is valid for every
real endpoint, including zero and negative endpoints. -/
theorem eq115HalfFresnelIntegral_eq_half_symmetric (X : ℝ) :
    eq115HalfFresnelIntegral X =
      (∫ u in (-X)..X, e (-(u ^ 2))) / 2 := by
  have hleft :
      (∫ u in (-X)..(0 : ℝ), e (-(u ^ 2))) =
        ∫ u in (0 : ℝ)..X, e (-(u ^ 2)) := by
    calc
      (∫ u in (-X)..(0 : ℝ), e (-(u ^ 2))) =
        ∫ u in (0 : ℝ)..X, e (-((-u) ^ 2)) := by
            simpa only [neg_zero] using
              (intervalIntegral.integral_comp_neg
                (f := fun u : ℝ => e (-(u ^ 2)))
                (a := (0 : ℝ)) (b := X)).symm
      _ = ∫ u in (0 : ℝ)..X, e (-(u ^ 2)) := by
        apply intervalIntegral.integral_congr
        intro u _
        exact eq115HalfFresnelIntegrand_even u
  have hsplit :
      (∫ u in (-X)..(0 : ℝ), e (-(u ^ 2))) +
          (∫ u in (0 : ℝ)..X, e (-(u ^ 2))) =
        ∫ u in (-X)..X, e (-(u ^ 2)) :=
    intervalIntegral.integral_add_adjacent_intervals
      (continuous_eq115HalfFresnelIntegrand.intervalIntegrable _ _)
      (continuous_eq115HalfFresnelIntegrand.intervalIntegrable _ _)
  rw [hleft] at hsplit
  unfold eq115HalfFresnelIntegral
  rw [← hsplit]
  ring

/-- The quantitative symmetric Fresnel estimate for positive phase, conjugated
to the negative phase needed in (11.5). -/
private theorem exists_eq115_symmetricFresnel_bound :
    ∃ C : ℝ, ∀ X : ℝ, 0 < X →
      ‖(∫ u in (-X)..X, e (-(u ^ 2))) -
          e (-(1 : ℝ) / 8) / ((Real.sqrt 2 : ℝ) : ℂ)‖ ≤ C / X := by
  rcases gk_lemma33_holds with ⟨C, hC⟩
  refine ⟨C, fun X hX => ?_⟩
  have hconj :
      (∫ u in (-X)..X, e (-(u ^ 2))) -
          e (-(1 : ℝ) / 8) / ((Real.sqrt 2 : ℝ) : ℂ) =
        starRingEnd ℂ
          ((∫ u in (-X)..X, e (u ^ 2)) -
            e ((1 : ℝ) / 8) / ((Real.sqrt 2 : ℝ) : ℂ)) := by
    rw [map_sub, map_div₀, Complex.conj_ofReal,
      ← GK32.integral_e_neg, ← KL.e_neg]
    congr 3
    ring
  rw [hconj, Complex.norm_conj]
  simpa using hC 1 X (by norm_num) hX

/-- The ordinary symmetric negative-phase Fresnel integrals converge.  This is
an ordinary improper limit, not an Abel-regularized value. -/
theorem tendsto_eq115_symmetricFresnel :
    Tendsto
      (fun X : ℝ => ∫ u in (-X)..X, e (-(u ^ 2)))
      atTop
      (nhds (e (-(1 : ℝ) / 8) / ((Real.sqrt 2 : ℝ) : ℂ))) := by
  rcases exists_eq115_symmetricFresnel_bound with ⟨C, hC⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    exact hC X hX
  · have hinv : Tendsto (fun X : ℝ => X⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero
    change Tendsto (fun X : ℝ => C * X⁻¹) atTop (nhds 0)
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hinv :
        Tendsto (fun X : ℝ => C * X⁻¹) atTop (nhds (C * 0)))

/-- The half-Fresnel limit first in exponential notation. -/
theorem tendsto_eq115_halfFresnel_exponential :
    Tendsto eq115HalfFresnelIntegral atTop
      (nhds (e (-(1 : ℝ) / 8) / ((Real.sqrt 2 : ℝ) : ℂ) / 2)) := by
  refine (tendsto_eq115_symmetricFresnel.div_const (2 : ℂ)).congr' ?_
  exact Eventually.of_forall fun X =>
    (eq115HalfFresnelIntegral_eq_half_symmetric X).symm

/-- Principal-branch evaluation of the negative half power of `2i`.

The branch choice is explicit in the proof: `arg (2i) = pi/2`, so multiplying
the principal logarithm by `-1/2` contributes the phase `e(-1/8)`. -/
theorem eq115_two_mul_I_cpow_neg_half :
    ((2 : ℂ) * Complex.I) ^ (-(1 : ℂ) / 2) =
      e (-(1 : ℝ) / 8) / ((Real.sqrt 2 : ℝ) : ℂ) := by
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hz0 : (2 : ℂ) * Complex.I ≠ 0 := by
    exact mul_ne_zero (by norm_num) Complex.I_ne_zero
  rw [Complex.cpow_def_of_ne_zero hz0]
  have hnorm : ‖(2 : ℂ) * Complex.I‖ = 2 := by
    rw [norm_mul, Complex.norm_I, mul_one]
    norm_num
  have harg : Complex.arg ((2 : ℂ) * Complex.I) = Real.pi / 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.arg_real_mul Complex.I htwo, Complex.arg_I]
  have hlog :
      Complex.log ((2 : ℂ) * Complex.I) =
        (Real.log 2 : ℂ) + (Real.pi / 2 : ℝ) * Complex.I := by
    rw [Complex.log, hnorm, harg]
  rw [hlog]
  have hsplit :
      ((Real.log 2 : ℂ) + (Real.pi / 2 : ℝ) * Complex.I) *
          (-(1 : ℂ) / 2) =
        ((-Real.log 2 / 2 : ℝ) : ℂ) +
          2 * Real.pi * Complex.I * ((-(1 : ℝ) / 8 : ℝ) : ℂ) := by
    push_cast
    ring
  have hexp_real :
      Complex.exp (((-Real.log 2 / 2 : ℝ) : ℂ)) =
        1 / ((Real.sqrt 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp]
    have hsqrt : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
      symm
      rw [Real.sqrt_eq_iff_mul_self_eq htwo.le (Real.exp_pos _).le,
        ← Real.exp_add,
        show Real.log 2 / 2 + Real.log 2 / 2 = Real.log 2 by ring,
        Real.exp_log htwo]
    rw [show -Real.log 2 / 2 = -(Real.log 2 / 2) by ring,
      Real.exp_neg, hsqrt]
    push_cast
    rw [one_div]
  rw [hsplit, Complex.exp_add, hexp_real]
  unfold e
  ring

/-- The reusable, canonical half-Fresnel evaluation needed by (11.5). -/
theorem iwaniecMozzochi_eq115_halfFresnel :
    Tendsto eq115HalfFresnelIntegral atTop
      (nhds (((2 : ℂ) * Complex.I) ^ (-(1 : ℂ) / 2) / 2)) := by
  rw [eq115_two_mul_I_cpow_neg_half]
  exact tendsto_eq115_halfFresnel_exponential

/-- The exact remaining oscillatory identity after the Fresnel constant has
been evaluated.  For `c > 0`, the substitution `v = u - c/u`, paired with the
reciprocal involution `u |-> c/u`, should reduce this limit to
`iwaniecMozzochi_eq115_halfFresnel`.

This is deliberately a one-parameter statement.  It contains neither the
original variables `a,b,delta` nor the target of (11.5), and therefore cannot
silently assume the theorem it is intended to prove. -/
def IwaniecMozzochiEq115ReciprocalPhaseLimit : Prop :=
  ∀ c : ℝ, 0 < c →
    Tendsto
      (fun U : ℝ =>
        ∫ u in (0 : ℝ)..U, e (-((u - c / u) ^ 2)))
      atTop
      (nhds (((2 : ℂ) * Complex.I) ^ (-(1 : ℂ) / 2) / 2))

/-- The degenerate `c = 0` phase limit is already exactly the proved
half-Fresnel theorem.  It is not needed by (11.5), whose hypotheses give
`c = sqrt (a*b) > 0`, but records the zero-parameter endpoint explicitly. -/
theorem iwaniecMozzochi_eq115_reciprocalPhase_zero :
    Tendsto
      (fun U : ℝ =>
        ∫ u in (0 : ℝ)..U, e (-((u - 0 / u) ^ 2)))
      atTop
      (nhds (((2 : ℂ) * Complex.I) ^ (-(1 : ℂ) / 2) / 2)) := by
  have hfun :
      (fun U : ℝ =>
        ∫ u in (0 : ℝ)..U, e (-((u - 0 / u) ^ 2))) =
        eq115HalfFresnelIntegral := by
    funext U
    simp only [zero_div, sub_zero, eq115HalfFresnelIntegral]
  rw [hfun]
  exact iwaniecMozzochi_eq115_halfFresnel

/-- The exact finite-truncation substitution still required after reciprocal
phase straightening.  For fixed `delta > 0`, the integral on the left is
absolutely convergent at infinity.  The formula is the substitution
`t = a/u^2`, followed by

```
  a/t + b*t = (u - sqrt(a*b)/u)^2 + 2*sqrt(a*b).
```

The value assigned to the displayed right-hand integrand at `u = 0` is
irrelevant because `{0}` has measure zero. -/
def IwaniecMozzochiEq115TruncatedChangeOfVariables : Prop :=
  ∀ a b δ : ℝ, 0 < a → 0 < b → 0 < δ →
    (∫ t in Set.Ioi δ,
      ((t ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * e (-a / t - b * t)) =
      (((2 / Real.sqrt a : ℝ) : ℂ) * e (-2 * Real.sqrt (a * b))) *
        (∫ u in (0 : ℝ)..Real.sqrt (a / δ),
          e (-((u - Real.sqrt (a * b) / u) ^ 2)))

private theorem eq115_cpow_scale {a : ℝ} (ha : 0 < a) :
    ((2 : ℂ) * Complex.I * (a : ℂ)) ^ (-(1 : ℂ) / 2) =
      (a : ℂ) ^ (-(1 : ℂ) / 2) *
        ((2 : ℂ) * Complex.I) ^ (-(1 : ℂ) / 2) := by
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hI0 : (2 : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by norm_num) Complex.I_ne_zero
  rw [show (2 : ℂ) * Complex.I * (a : ℂ) =
      (a : ℂ) * ((2 : ℂ) * Complex.I) by ring,
    Complex.cpow_def_of_ne_zero (mul_ne_zero ha0 hI0),
    Complex.log_ofReal_mul ha hI0, Complex.ofReal_log ha.le,
    add_mul, Complex.exp_add,
    ← Complex.cpow_def_of_ne_zero ha0,
    ← Complex.cpow_def_of_ne_zero hI0]

private theorem eq115_ofReal_cpow_neg_half {a : ℝ} (ha : 0 < a) :
    (a : ℂ) ^ (-(1 : ℂ) / 2) =
      (((Real.sqrt a)⁻¹ : ℝ) : ℂ) := by
  have hrpow :
      a ^ (-(1 : ℝ) / 2) = (Real.sqrt a)⁻¹ := by
    rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring,
      Real.rpow_neg ha.le, ← Real.sqrt_eq_rpow]
  calc
    (a : ℂ) ^ (-(1 : ℂ) / 2) =
        ((a ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) := by
      symm
      simpa using Complex.ofReal_cpow ha.le (-(1 : ℝ) / 2)
    _ = (((Real.sqrt a)⁻¹ : ℝ) : ℂ) := by rw [hrpow]

/-- The moving upper endpoint produced by `t = a/u^2` tends to infinity as
`delta -> 0+`. -/
theorem tendsto_eq115_truncationEndpoint {a : ℝ} (ha : 0 < a) :
    Tendsto (fun δ : ℝ => Real.sqrt (a / δ))
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  apply Real.tendsto_sqrt_atTop.comp
  have hinv : Tendsto (fun δ : ℝ => δ⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    tendsto_inv_nhdsGT_zero
  change Tendsto (fun δ : ℝ => a * δ⁻¹)
    (nhdsWithin 0 (Set.Ioi 0)) atTop
  exact (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => a)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds a)).pos_mul_atTop ha hinv

/-- The reciprocal phase limit supplies the limit of the fully transformed
right-hand side of (11.5).  This theorem contains all positivity, filter,
square-root, and principal-complex-power algebra surrounding the two explicit
change-of-variable interfaces. -/
theorem iwaniecMozzochi_eq115_transformed_limit
    (hphase : IwaniecMozzochiEq115ReciprocalPhaseLimit)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun δ : ℝ =>
        (((2 / Real.sqrt a : ℝ) : ℂ) * e (-2 * Real.sqrt (a * b))) *
          (∫ u in (0 : ℝ)..Real.sqrt (a / δ),
            e (-((u - Real.sqrt (a * b) / u) ^ 2))))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (((2 : ℂ) * Complex.I * (a : ℂ)) ^
        (-(1 : ℂ) / 2) * e (-2 * Real.sqrt (a * b)))) := by
  have hc : 0 < Real.sqrt (a * b) :=
    Real.sqrt_pos.2 (mul_pos ha hb)
  have hcore :=
    (hphase (Real.sqrt (a * b)) hc).comp
      (tendsto_eq115_truncationEndpoint ha)
  have hlim :=
    (tendsto_const_nhds :
      Tendsto
        (fun _ : ℝ =>
          ((2 / Real.sqrt a : ℝ) : ℂ) * e (-2 * Real.sqrt (a * b)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (((2 / Real.sqrt a : ℝ) : ℂ) *
          e (-2 * Real.sqrt (a * b))))).mul hcore
  have hlim' :
      Tendsto
        (fun δ : ℝ =>
          (((2 / Real.sqrt a : ℝ) : ℂ) * e (-2 * Real.sqrt (a * b))) *
            (∫ u in (0 : ℝ)..Real.sqrt (a / δ),
              e (-((u - Real.sqrt (a * b) / u) ^ 2))))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((((2 / Real.sqrt a : ℝ) : ℂ) *
          e (-2 * Real.sqrt (a * b))) *
            (((2 : ℂ) * Complex.I) ^ (-(1 : ℂ) / 2) / 2))) := by
    simpa only [Function.comp_apply] using hlim
  have htarget :
      (((2 / Real.sqrt a : ℝ) : ℂ) * e (-2 * Real.sqrt (a * b))) *
          (((2 : ℂ) * Complex.I) ^ (-(1 : ℂ) / 2) / 2) =
        ((2 : ℂ) * Complex.I * (a : ℂ)) ^ (-(1 : ℂ) / 2) *
          e (-2 * Real.sqrt (a * b)) := by
    rw [eq115_cpow_scale ha, eq115_ofReal_cpow_neg_half ha]
    push_cast
    simp only [div_eq_mul_inv]
    ring
  rw [← htarget]
  exact hlim'

/-- Exact reduction of Iwaniec--Mozzochi (11.5) to the reciprocal phase limit
and the finite-truncation change of variables.  No (11.2), (11.3), (11.4), or
Section 12 premise is used. -/
theorem iwaniecMozzochi_eq115_of_reciprocal_change
    (hphase : IwaniecMozzochiEq115ReciprocalPhaseLimit)
    (hchange : IwaniecMozzochiEq115TruncatedChangeOfVariables) :
    iwaniecMozzochi_eq115 := by
  intro a b ha hb
  have hlim := iwaniecMozzochi_eq115_transformed_limit hphase ha hb
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (hchange a b δ ha hb hδ).symm

end LeanProofs.IntegerPoints
