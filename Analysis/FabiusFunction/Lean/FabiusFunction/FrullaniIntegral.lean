import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The Frullani integral for exponentials

The classical Frullani evaluation

`∫₀^∞ (e^(-pt) - e^(-qt))/t dt = log (q/p)`  (`p, q > 0`),

which is not in Mathlib.  The proof differentiates under the integral
sign in the parameter `q`: the `1/t` singularity cancels *exactly*
against the derivative of the exponential, leaving
`d/dq ∫ = ∫ e^(-qt) dt = 1/q`, and the fundamental theorem of calculus
along the segment from `p` to `q` integrates `1/u` back to the
logarithm.  The integral vanishes at `q = p`, which fixes the constant.

This is the analytic engine behind the atlas's derivative bridge
`log G(a,b) = D'(0,b) - D'(0,a)`: each term of the master log-series
`ε(n)·log((n+a)/(n+b))` is a Frullani integral with parameters
`n + b`, `n + a`.

* `frullani_integrand_abs_le` — the uniform domination
  `|(e^(-pt) - e^(-qt))/t| ≤ |q - p|·e^(-min p q·t)`.
* `frullani_integrableOn` — integrability on `(0,∞)`.
* `hasDerivAt_frullani` — differentiation under the integral sign.
* `frullani_exp` — **the Frullani integral**.
-/

set_option autoImplicit false

open Filter MeasureTheory Set Topology

namespace Fabius

/-- For `p ≤ q` the Frullani integrand is nonnegative. -/
private theorem frullani_aux_nonneg {p q t : ℝ} (ht : 0 < t)
    (hpq : p ≤ q) :
    0 ≤ (Real.exp (-(p * t)) - Real.exp (-(q * t))) / t := by
  apply div_nonneg _ ht.le
  have h : -(q * t) ≤ -(p * t) := by nlinarith
  linarith [Real.exp_le_exp.mpr h]

/-- The Frullani integrand is at most `(q-p)·e^(-pt)`: the convexity
bound `1 - e^(-x) ≤ x` cancels the `1/t`.  (True for all parameter
orders, though only the case `p ≤ q` is used.) -/
private theorem frullani_aux_le {p q t : ℝ} (ht : 0 < t) :
    (Real.exp (-(p * t)) - Real.exp (-(q * t))) / t ≤
      (q - p) * Real.exp (-(p * t)) := by
  rw [div_le_iff₀ ht]
  have he : Real.exp (-(q * t)) =
      Real.exp (-(p * t)) * Real.exp (-((q - p) * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h1 : 1 - Real.exp (-((q - p) * t)) ≤ (q - p) * t := by
    have := Real.add_one_le_exp (-((q - p) * t))
    linarith
  have hep : (0 : ℝ) < Real.exp (-(p * t)) := Real.exp_pos _
  calc Real.exp (-(p * t)) - Real.exp (-(q * t))
      = Real.exp (-(p * t)) * (1 - Real.exp (-((q - p) * t))) := by
        rw [he]; ring
    _ ≤ Real.exp (-(p * t)) * ((q - p) * t) :=
        mul_le_mul_of_nonneg_left h1 hep.le
    _ = (q - p) * Real.exp (-(p * t)) * t := by ring

/-- **Uniform domination of the Frullani integrand**: for `t > 0`,
`|(e^(-pt) - e^(-qt))/t| ≤ |q - p|·e^(-min p q·t)`.  No sign or
positivity hypotheses on the parameters are needed. -/
theorem frullani_integrand_abs_le (p q t : ℝ) (ht : 0 < t) :
    |(Real.exp (-(p * t)) - Real.exp (-(q * t))) / t| ≤
      |q - p| * Real.exp (-(min p q * t)) := by
  rcases le_total p q with hpq | hqp
  · rw [abs_of_nonneg (frullani_aux_nonneg ht hpq), min_eq_left hpq,
      abs_of_nonneg (sub_nonneg.mpr hpq)]
    exact frullani_aux_le ht
  · rw [show (Real.exp (-(p * t)) - Real.exp (-(q * t))) / t =
        -((Real.exp (-(q * t)) - Real.exp (-(p * t))) / t) by ring,
      abs_neg, abs_of_nonneg (frullani_aux_nonneg ht hqp),
      min_eq_right hqp, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr hqp)]
    exact frullani_aux_le ht

/-- The Frullani integrand is continuous on `(0,∞)`. -/
theorem frullani_continuousOn (p q : ℝ) :
    ContinuousOn
      (fun t : ℝ => (Real.exp (-(p * t)) - Real.exp (-(q * t))) / t)
      (Ioi 0) := by
  refine ContinuousOn.div ?_ continuous_id.continuousOn
    fun t ht => ne_of_gt ht
  exact ((Real.continuous_exp.comp
      (continuous_const.mul continuous_id).neg).sub
    (Real.continuous_exp.comp
      (continuous_const.mul continuous_id).neg)).continuousOn

/-- The Frullani integrand is integrable on `(0,∞)` for positive
parameters. -/
theorem frullani_integrableOn {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    IntegrableOn
      (fun t => (Real.exp (-(p * t)) - Real.exp (-(q * t))) / t)
      (Ioi (0 : ℝ)) := by
  have hmin : 0 < min p q := lt_min hp hq
  have hdom : IntegrableOn
      (fun t => |q - p| * Real.exp (-min p q * t)) (Ioi (0 : ℝ)) :=
    (exp_neg_integrableOn_Ioi 0 hmin).const_mul _
  refine Integrable.mono hdom
    ((frullani_continuousOn p q).aestronglyMeasurable measurableSet_Ioi)
    ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr
    (Filter.Eventually.of_forall fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ |q - p| *
      Real.exp (-min p q * t)),
    show -min p q * t = -(min p q * t) by ring]
  exact frullani_integrand_abs_le p q t ht0

/-- **Differentiation under the integral sign** for the Frullani
integral: as a function of the second parameter, its derivative at
`q₀ > 0` is `1/q₀` — the `1/t` cancels exactly against the derivative
of the exponential. -/
theorem hasDerivAt_frullani {p : ℝ} (hp : 0 < p) (q₀ : ℝ)
    (hq₀ : 0 < q₀) :
    HasDerivAt (fun q => ∫ t in Ioi (0 : ℝ),
      (Real.exp (-(p * t)) - Real.exp (-(q * t))) / t) q₀⁻¹ q₀ := by
  have hs : Ioi (q₀ / 2) ∈ 𝓝 q₀ := Ioi_mem_nhds (by linarith)
  have hmeas : ∀ᶠ q in 𝓝 q₀, AEStronglyMeasurable
      (fun t => (Real.exp (-(p * t)) - Real.exp (-(q * t))) / t)
      (volume.restrict (Ioi 0)) :=
    Filter.Eventually.of_forall fun q =>
      (frullani_continuousOn p q).aestronglyMeasurable measurableSet_Ioi
  have hint : Integrable
      (fun t => (Real.exp (-(p * t)) - Real.exp (-(q₀ * t))) / t)
      (volume.restrict (Ioi 0)) := frullani_integrableOn hp hq₀
  have hmeas' : AEStronglyMeasurable
      (fun t : ℝ => Real.exp (-(q₀ * t))) (volume.restrict (Ioi 0)) :=
    (Real.continuous_exp.comp
      (continuous_const.mul continuous_id).neg).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ q ∈ Ioi (q₀ / 2), ‖Real.exp (-(q * t))‖ ≤
        Real.exp (-(q₀ / 2) * t) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun t ht q hq => ?_)
    have ht0 : (0 : ℝ) < t := ht
    have hq' : q₀ / 2 < q := hq
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hboundint : Integrable
      (fun t : ℝ => Real.exp (-(q₀ / 2) * t))
      (volume.restrict (Ioi 0)) :=
    exp_neg_integrableOn_Ioi 0 (by linarith)
  have hdiff : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ q ∈ Ioi (q₀ / 2), HasDerivAt
        (fun q => (Real.exp (-(p * t)) - Real.exp (-(q * t))) / t)
        (Real.exp (-(q * t))) q := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun t ht q _ => ?_)
    have ht0 : (0 : ℝ) < t := ht
    have h3 : HasDerivAt (fun q : ℝ => Real.exp (-(q * t)))
        (Real.exp (-(q * t)) * (-t)) q :=
      ((hasDerivAt_mul_const t).neg).exp
    have hsub : HasDerivAt
        (fun q : ℝ => Real.exp (-(p * t)) - Real.exp (-(q * t)))
        (0 - Real.exp (-(q * t)) * (-t)) q :=
      (hasDerivAt_const q _).sub h3
    have hdiv := hsub.div_const t
    have hv : (0 - Real.exp (-(q * t)) * (-t)) / t =
        Real.exp (-(q * t)) := by
      rw [zero_sub, mul_neg, neg_neg]
      exact mul_div_cancel_right₀ _ (ne_of_gt ht0)
    exact hv ▸ hdiv
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun q t =>
      (Real.exp (-(p * t)) - Real.exp (-(q * t))) / t)
    (F' := fun q t => Real.exp (-(q * t)))
    (bound := fun t => Real.exp (-(q₀ / 2) * t))
    hs hmeas hint hmeas' hbound hboundint hdiff).2
  have hval : (∫ t in Ioi (0 : ℝ), Real.exp (-(q₀ * t))) = q₀⁻¹ := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := 1) one_pos hq₀
    simp only [sub_self, Real.rpow_zero, one_mul, Real.rpow_one,
      Real.Gamma_one, mul_one, one_div] at h
    exact h
  rw [← hval]
  exact key

/-- **The Frullani integral for exponentials**:
`∫₀^∞ (e^(-pt) - e^(-qt))/t dt = log (q/p)` for `p, q > 0`. -/
theorem frullani_exp {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∫ t in Ioi (0 : ℝ),
      (Real.exp (-(p * t)) - Real.exp (-(q * t))) / t =
      Real.log (q / p) := by
  have hderiv : ∀ u ∈ uIcc p q, HasDerivAt
      (fun r => ∫ t in Ioi (0 : ℝ),
        (Real.exp (-(p * t)) - Real.exp (-(r * t))) / t) u⁻¹ u := by
    intro u hu
    rw [Set.mem_uIcc] at hu
    have hu0 : 0 < u := by
      rcases hu with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
    exact hasDerivAt_frullani hp u hu0
  have hint : IntervalIntegrable (fun u : ℝ => u⁻¹) volume p q := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.mono continuousOn_inv₀ fun x hx => ?_
    rw [Set.mem_uIcc] at hx
    have hx0 : 0 < x := by
      rcases hx with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
    simpa using hx0.ne'
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [integral_inv_of_pos hp hq] at hFTC
  have hGp : (∫ t in Ioi (0 : ℝ),
      (Real.exp (-(p * t)) - Real.exp (-(p * t))) / t) = 0 := by
    simp
  linarith [hFTC, hGp]
