import IntegerPoints.IwaniecMozzochiEq115Fresnel
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Change of variables for Iwaniec--Mozzochi (11.5)

This companion to `IntegerPoints.IwaniecMozzochiEq115Fresnel` proves the
finite-truncation substitution isolated there.  For `a, delta > 0`, the map

```
  tau(u) = a / u^2
```

is an injective differentiable map from
`(0, sqrt (a/delta))` onto `(delta, infinity)`, with absolute derivative
`2*a/u^3`.  The positive-real power in the original integrand cancels that
Jacobian exactly, leaving the constant `2/sqrt a`.

No improper limit is taken in this argument: for fixed positive `delta`, the
left-hand integral is absolutely convergent at infinity, and the change of
variables theorem applies directly to the measurable open interval.  The two
finite endpoints differ from the interval-integral convention by null
singletons only.
-/

open Real Set MeasureTheory intervalIntegral

noncomputable section

namespace LeanProofs.IntegerPoints

namespace Eq115Change

/-- The decreasing reciprocal-square map used in (11.5). -/
private def tau (a u : ℝ) : ℝ := a / u ^ 2

private theorem upper_pos {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    0 < Real.sqrt (a / δ) :=
  Real.sqrt_pos.2 (div_pos ha hδ)

private theorem upper_sq {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    Real.sqrt (a / δ) ^ 2 = a / δ :=
  Real.sq_sqrt (div_nonneg ha.le hδ.le)

private theorem tau_upper {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    tau a (Real.sqrt (a / δ)) = δ := by
  rw [tau, upper_sq ha hδ]
  field_simp [ha.ne', hδ.ne']

/-- `tau` maps the open finite `u` interval exactly onto the open ray used by
the set integral.  In particular, neither endpoint is accidentally retained. -/
private theorem image_tau_Ioo {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    tau a '' Set.Ioo 0 (Real.sqrt (a / δ)) = Set.Ioi δ := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hU : 0 < Real.sqrt (a / δ) := upper_pos ha hδ
    have hu2 : u ^ 2 < Real.sqrt (a / δ) ^ 2 := by
      nlinarith [hu.1, hu.2]
    calc
      δ = a / (Real.sqrt (a / δ) ^ 2) := (tau_upper ha hδ).symm
      _ < a / u ^ 2 :=
        (div_lt_div_iff_of_pos_left ha (sq_pos_of_pos hU)
          (sq_pos_of_pos hu.1)).2 hu2
  · intro ht
    have ht0 : 0 < t := hδ.trans ht
    let u : ℝ := Real.sqrt (a / t)
    have hu0 : 0 < u := by
      dsimp only [u]
      exact Real.sqrt_pos.2 (div_pos ha ht0)
    have huU : u < Real.sqrt (a / δ) := by
      dsimp only [u]
      apply Real.sqrt_lt_sqrt (div_nonneg ha.le ht0.le)
      exact (div_lt_div_iff_of_pos_left ha ht0 hδ).2 ht
    refine ⟨u, ⟨hu0, huU⟩, ?_⟩
    rw [tau]
    have hu2 : u ^ 2 = a / t := by
      dsimp only [u]
      exact Real.sq_sqrt (div_nonneg ha.le ht0.le)
    rw [hu2]
    field_simp [ha.ne', ht0.ne']

private theorem tau_injOn {a δ : ℝ} (ha : 0 < a) :
    Set.InjOn (tau a) (Set.Ioo 0 (Real.sqrt (a / δ))) := by
  intro u hu v hv huv
  unfold tau at huv
  have hsquares : u ^ 2 = v ^ 2 := by
    have hcross : a * v ^ 2 = a * u ^ 2 :=
      (div_eq_div_iff (pow_ne_zero 2 hu.1.ne')
        (pow_ne_zero 2 hv.1.ne')).mp huv
    exact (mul_left_cancel₀ ha.ne' hcross).symm
  nlinarith [hu.1, hv.1]

private theorem hasDerivAt_tau {a u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (tau a) (-2 * a / u ^ 3) u := by
  unfold tau
  have h := (hasDerivAt_const u a).div ((hasDerivAt_id' u).pow 2)
    (pow_ne_zero 2 hu)
  apply h.congr_deriv
  simp only [Pi.pow_apply]
  field_simp [hu]
  ring

/-- Raw one-dimensional Jacobian formula before simplifying its integrand. -/
private theorem integral_tau {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (g : ℝ → ℂ) :
    (∫ t in Set.Ioi δ, g t) =
      ∫ u in Set.Ioo 0 (Real.sqrt (a / δ)),
        |-2 * a / u ^ 3| • g (tau a u) := by
  have hchange := integral_image_eq_integral_abs_deriv_smul
    (f := tau a) (f' := fun u : ℝ => -2 * a / u ^ 3)
    measurableSet_Ioo
    (fun u hu => (hasDerivAt_tau hu.1.ne').hasDerivWithinAt)
    (tau_injOn (δ := δ) ha) g
  rw [image_tau_Ioo ha hδ] at hchange
  exact hchange

private theorem tau_pos {a u : ℝ} (ha : 0 < a) (hu : 0 < u) :
    0 < tau a u := by
  exact div_pos ha (sq_pos_of_pos hu)

/-- Positive-real normalization of the `t^(-3/2)` factor after substituting
`t = a/u^2`. -/
private theorem tau_rpow_neg_three_halves {a u : ℝ} (ha : 0 < a) (hu : 0 < u) :
    tau a u ^ (-(3 : ℝ) / 2) = u ^ 3 / (a * Real.sqrt a) := by
  have ht : 0 < tau a u := tau_pos ha hu
  rw [show -(3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring,
    Real.rpow_neg ht.le]
  have hthreehalf :
      tau a u ^ ((3 : ℝ) / 2) =
        tau a u * Real.sqrt (tau a u) := by
    rw [show (3 : ℝ) / 2 = 1 + (1 : ℝ) / 2 by ring,
      Real.rpow_add ht 1 ((1 : ℝ) / 2), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  rw [hthreehalf, tau, Real.sqrt_div ha.le, Real.sqrt_sq_eq_abs,
    abs_of_pos hu]
  field_simp [ha.ne', hu.ne', (Real.sqrt_ne_zero'.2 ha)]

private theorem jacobian_mul_tau_rpow {a u : ℝ} (ha : 0 < a) (hu : 0 < u) :
    |-2 * a / u ^ 3| * tau a u ^ (-(3 : ℝ) / 2) =
      2 / Real.sqrt a := by
  rw [show -2 * a / u ^ 3 = -(2 * a / u ^ 3) by ring,
    abs_neg, abs_of_pos (div_pos (mul_pos (by norm_num) ha) (pow_pos hu 3)),
    tau_rpow_neg_three_halves ha hu]
  field_simp [ha.ne', hu.ne', (Real.sqrt_ne_zero'.2 ha)]

private theorem sqrt_mul_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a * b) ^ 2 = a * b :=
  Real.sq_sqrt (mul_pos ha hb).le

/-- Algebraic completion of the square in the oscillatory phase. -/
private theorem tau_phase {a b u : ℝ} (ha : 0 < a) (hb : 0 < b) (hu : 0 < u) :
    -a / tau a u - b * tau a u =
      -2 * Real.sqrt (a * b) -
        (u - Real.sqrt (a * b) / u) ^ 2 := by
  have hsqrt := sqrt_mul_sq ha hb
  unfold tau
  field_simp [ha.ne', hu.ne']
  nlinarith

/-- Pointwise simplification of the Jacobian-weighted integrand. -/
private theorem tau_integrand {a b u : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hu : 0 < u) :
    |-2 * a / u ^ 3| •
        (((tau a u ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) *
          e (-a / tau a u - b * tau a u)) =
      (((2 / Real.sqrt a : ℝ) : ℂ) * e (-2 * Real.sqrt (a * b))) *
        e (-((u - Real.sqrt (a * b) / u) ^ 2)) := by
  rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    jacobian_mul_tau_rpow ha hu, tau_phase ha hb hu, sub_eq_add_neg, KL.e_add]
  ring

/-- The exact finite-truncation change of variables isolated by the Fresnel
module holds unconditionally. -/
theorem iwaniecMozzochi_eq115_truncatedChangeOfVariables_holds :
    IwaniecMozzochiEq115TruncatedChangeOfVariables := by
  intro a b δ ha hb hδ
  let g : ℝ → ℂ := fun t =>
    ((t ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * e (-a / t - b * t)
  have hraw := integral_tau ha hδ g
  change (∫ t in Set.Ioi δ, g t) = _
  rw [hraw]
  let K : ℂ :=
    ((2 / Real.sqrt a : ℝ) : ℂ) * e (-2 * Real.sqrt (a * b))
  calc
    (∫ u in Set.Ioo 0 (Real.sqrt (a / δ)),
        |-2 * a / u ^ 3| • g (tau a u)) =
        ∫ u in Set.Ioo 0 (Real.sqrt (a / δ)),
          K * e (-((u - Real.sqrt (a * b) / u) ^ 2)) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      dsimp only [g, K]
      exact tau_integrand ha hb hu.1
    _ = K * (∫ u in Set.Ioo 0 (Real.sqrt (a / δ)),
          e (-((u - Real.sqrt (a * b) / u) ^ 2))) := by
      rw [MeasureTheory.integral_const_mul]
    _ = K * (∫ u in (0 : ℝ)..Real.sqrt (a / δ),
          e (-((u - Real.sqrt (a * b) / u) ^ 2))) := by
      rw [intervalIntegral.integral_of_le (upper_pos ha hδ).le,
        integral_Ioc_eq_integral_Ioo]

/-! Before specializing the sign of the linear frequency, the same
substitution gives a reciprocal-quadratic phase.  This normalized form is the
one used by the uniform oscillatory estimate in Lemma 11.1. -/

private theorem tau_phase_reciprocal {a c u : ℝ} (ha : 0 < a) (hu : 0 < u) :
    -a / tau a u - c * tau a u =
      -(u ^ 2) - (a * c) / u ^ 2 := by
  unfold tau
  field_simp [ha.ne', hu.ne']

private theorem tau_integrand_reciprocal {a c u : ℝ}
    (ha : 0 < a) (hu : 0 < u) :
    |-2 * a / u ^ 3| •
        (((tau a u ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) *
          e (-a / tau a u - c * tau a u)) =
      (((2 / Real.sqrt a : ℝ) : ℂ) *
        e (-(u ^ 2) - (a * c) / u ^ 2)) := by
  rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    jacobian_mul_tau_rpow ha hu, tau_phase_reciprocal ha hu]

/-- Exact finite-cutoff normalization at an arbitrary real linear frequency:

`integral_delta^infinity t^(-3/2) e(-a/t-c*t) dt`
is `2/sqrt(a)` times the partial integral of
`e(-u^2-(a*c)/u^2)` from zero to `sqrt(a/delta)`. -/
theorem iwaniecMozzochi_eq112_truncatedChangeOfVariables
    {a c δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    (∫ t in Set.Ioi δ,
      ((t ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * e (-a / t - c * t)) =
      (((2 / Real.sqrt a : ℝ) : ℂ) *
        (∫ u in (0 : ℝ)..Real.sqrt (a / δ),
          e (-(u ^ 2) - (a * c) / u ^ 2))) := by
  let g : ℝ → ℂ := fun t =>
    ((t ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * e (-a / t - c * t)
  have hraw := integral_tau ha hδ g
  change (∫ t in Set.Ioi δ, g t) = _
  rw [hraw]
  let K : ℂ := ((2 / Real.sqrt a : ℝ) : ℂ)
  calc
    (∫ u in Set.Ioo 0 (Real.sqrt (a / δ)),
        |-2 * a / u ^ 3| • g (tau a u)) =
        ∫ u in Set.Ioo 0 (Real.sqrt (a / δ)),
          K * e (-(u ^ 2) - (a * c) / u ^ 2) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      dsimp only [g, K]
      exact tau_integrand_reciprocal ha hu.1
    _ = K * (∫ u in Set.Ioo 0 (Real.sqrt (a / δ)),
          e (-(u ^ 2) - (a * c) / u ^ 2)) := by
      rw [MeasureTheory.integral_const_mul]
    _ = K * (∫ u in (0 : ℝ)..Real.sqrt (a / δ),
          e (-(u ^ 2) - (a * c) / u ^ 2)) := by
      rw [intervalIntegral.integral_of_le (upper_pos ha hδ).le,
        integral_Ioc_eq_integral_Ioo]

/-! The zero linear-frequency endpoint, used by the generalized transform in
Lemma 11.1, needs no reciprocal-phase straightening. -/

private theorem tau_phase_zero {a u : ℝ} (ha : 0 < a) (hu : 0 < u) :
    -a / tau a u = -(u ^ 2) := by
  unfold tau
  field_simp [ha.ne', hu.ne']

private theorem tau_integrand_zero {a u : ℝ} (ha : 0 < a) (hu : 0 < u) :
    |-2 * a / u ^ 3| •
        (((tau a u ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) *
          e (-a / tau a u)) =
      (((2 / Real.sqrt a : ℝ) : ℂ) * e (-(u ^ 2))) := by
  rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    jacobian_mul_tau_rpow ha hu, tau_phase_zero ha hu]

/-- Exact finite-cutoff substitution at zero linear frequency:

`integral_delta^infinity t^(-3/2) e(-a/t) dt`
is `2/sqrt(a)` times the negative half-Fresnel partial integral. -/
theorem iwaniecMozzochi_eq115_truncatedChangeOfVariables_zero
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    (∫ t in Set.Ioi δ,
      ((t ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * e (-a / t)) =
      (((2 / Real.sqrt a : ℝ) : ℂ) *
        (∫ u in Set.Ioc 0 (Real.sqrt (a / δ)), e (-(u ^ 2)))) := by
  let g : ℝ → ℂ := fun t =>
    ((t ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * e (-a / t)
  have hraw := integral_tau ha hδ g
  change (∫ t in Set.Ioi δ, g t) = _
  rw [hraw]
  let K : ℂ := ((2 / Real.sqrt a : ℝ) : ℂ)
  calc
    (∫ u in Set.Ioo 0 (Real.sqrt (a / δ)),
        |-2 * a / u ^ 3| • g (tau a u))
        = ∫ u in Set.Ioo 0 (Real.sqrt (a / δ)), K * e (-(u ^ 2)) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      dsimp only [g, K]
      exact tau_integrand_zero ha hu.1
    _ = K * (∫ u in Set.Ioo 0 (Real.sqrt (a / δ)), e (-(u ^ 2))) := by
      rw [MeasureTheory.integral_const_mul]
    _ = K * (∫ u in Set.Ioc 0 (Real.sqrt (a / δ)), e (-(u ^ 2))) := by
      rw [integral_Ioc_eq_integral_Ioo]

end Eq115Change

end LeanProofs.IntegerPoints
