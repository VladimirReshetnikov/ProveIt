import FabiusFunction.ProbabilityLaplaceMoments
import FabiusFunction.FractionalVolterra

/-!
# The incomplete-beta master formula for weighted fractional integrals

The integration volume's *special-function layer* obligation: introduce
incomplete beta integrals and prove the weighted fractional master
theorem for positive real parameters.  This module does both for the
survival display: for `α > 0`, `p ≥ 0`, and `0 < x ≤ 1`,

`I₀₊^α [t^p·up(t)](x) = x^{p+α}/Γ(α) · E[B_{min(X/x,1)}(p+1, α)]`,

where `B_z(a,b) = ∫₀ᶻ u^{a-1}(1-u)^{b-1} du` is the incomplete beta
integral and `X` is the weighted-sum random variable, whose survival
function on `[0,1]` is Rvachev's `up`.

The proof composes three reusable steps:

* `incompleteBeta` — the incomplete beta integral;
* `integral_rpow_mul_rpow_eq_incompleteBeta` — **the scaling
  identity** `∫₀ᶜ (x-t)^{α-1} t^p dt = x^{p+α}·B_{c/x}(p+1, α)` for
  `0 ≤ c ≤ x`, by the substitution `t = x·u`;
* the Rvachev survival layer cake
  (`intervalIntegral_rvachevUp_smul_eq_integral_min`), which converts
  the up-weighted kernel integral into the expectation of stopped
  kernel primitives.

The clamp `min(X/x, 1)` implements the stopping: samples above `x`
contribute the complete beta value, samples inside `[0,x]` an
incomplete one.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace Fabius

open ProbabilityRepresentation

/-- **The incomplete beta integral**
`B_z(a,b) = ∫₀ᶻ u^{a-1}(1-u)^{b-1} du` (real powers). -/
noncomputable def incompleteBeta (z a b : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..z, u ^ (a - 1) * (1 - u) ^ (b - 1)

@[simp] theorem incompleteBeta_zero (a b : ℝ) :
    incompleteBeta 0 a b = 0 := by
  simp [incompleteBeta]

/-- **The scaling identity**: for `0 < x`, `0 ≤ c ≤ x`,
`∫₀ᶜ (x-t)^{α-1} t^p dt = x^{p+α}·B_{c/x}(p+1, α)`, by the
substitution `t = x·u`. -/
theorem integral_rpow_mul_rpow_eq_incompleteBeta
    {x c α p : ℝ} (hx : 0 < x) (hc0 : 0 ≤ c) (hcx : c ≤ x) :
    ∫ t in (0 : ℝ)..c, (x - t) ^ (α - 1) * t ^ p =
      x ^ (p + α) * incompleteBeta (c / x) (p + 1) α := by
  have hcx1 : c / x ≤ 1 := by
    rw [div_le_one hx]
    exact hcx
  have hsub := intervalIntegral.integral_comp_mul_left
    (f := fun t => (x - t) ^ (α - 1) * t ^ p) (a := (0 : ℝ))
    (b := c / x) hx.ne'
  rw [mul_zero, show x * (c / x) = c from by field_simp,
    smul_eq_mul] at hsub
  have h1 : ∫ t in (0 : ℝ)..c, (x - t) ^ (α - 1) * t ^ p =
      x * ∫ u in (0 : ℝ)..(c / x),
        (x - x * u) ^ (α - 1) * (x * u) ^ p := by
    rw [hsub, ← mul_assoc, mul_inv_cancel₀ hx.ne', one_mul]
  have h2 : ∫ u in (0 : ℝ)..(c / x),
      (x - x * u) ^ (α - 1) * (x * u) ^ p =
      x ^ (p + α - 1) *
        ∫ u in (0 : ℝ)..(c / x), u ^ p * (1 - u) ^ (α - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ c / x)] at hu
    have hu0 : 0 ≤ u := hu.1
    have hu1 : u ≤ 1 := hu.2.trans hcx1
    rw [show x - x * u = x * (1 - u) from by ring,
      Real.mul_rpow hx.le (by linarith : (0 : ℝ) ≤ 1 - u),
      Real.mul_rpow hx.le hu0,
      show p + α - 1 = (α - 1) + p from by ring, Real.rpow_add hx]
    ring
  have h3 : x * x ^ (p + α - 1) = x ^ (p + α) := by
    have hstep := Real.rpow_add_one hx.ne' (p + α - 1)
    rw [show p + α - 1 + 1 = p + α from by ring] at hstep
    rw [hstep, mul_comm]
  rw [h1, h2, ← mul_assoc, h3, incompleteBeta]
  congr 1
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [show p + 1 - 1 = p from by ring]

/-- The weighted fractional kernel is interval integrable for `p ≥ 0`. -/
theorem intervalIntegrable_rpow_kernel {x α p : ℝ} (hα : 0 < α)
    (hp : 0 ≤ p) (hx : 0 ≤ x) :
    IntervalIntegrable
      (fun t => (x - t) ^ (α - 1) / Real.Gamma α * t ^ p)
      volume 0 x := by
  have h := intervalIntegrable_fractionalVolterra_kernel
    (E := ℝ) hα hx (f := fun t : ℝ => t ^ p)
    (fun t _ =>
      (Real.continuousAt_rpow_const t p (Or.inr hp)).continuousWithinAt)
  simpa only [smul_eq_mul] using h

/-- **The incomplete-beta master formula** (survival display, positive
real parameters): for `α > 0`, `p ≥ 0`, and `0 < x ≤ 1`,
`I₀₊^α [t^p·up(t)](x) = x^{p+α}/Γ(α) · E[B_{min(X/x,1)}(p+1, α)]`
for the weighted-sum random variable `X`. -/
theorem fractionalVolterra_rpow_mul_rvachevUp
    (F : BoundedFabius) (hF : IsFabius F) {α p x : ℝ}
    (hα : 0 < α) (hp : 0 ≤ p) (hx : 0 < x) (hx1 : x ≤ 1) :
    fractionalVolterra α 0 (fun t => t ^ p * rvachevUp F t) x =
      x ^ (p + α) / Real.Gamma α *
        ∫ z, incompleteBeta (min (z / x) 1) (p + 1) α
          ∂weightedSumDistribution := by
  calc fractionalVolterra α 0 (fun t => t ^ p * rvachevUp F t) x
      = ∫ t in (0 : ℝ)..x, rvachevUp F t •
          ((x - t) ^ (α - 1) / Real.Gamma α * t ^ p) := by
        rw [fractionalVolterra]
        refine intervalIntegral.integral_congr fun t _ => ?_
        simp only [smul_eq_mul]
        ring
    _ = ∫ z, (∫ t in (0 : ℝ)..min z x,
          (x - t) ^ (α - 1) / Real.Gamma α * t ^ p)
          ∂weightedSumDistribution :=
        intervalIntegral_rvachevUp_smul_eq_integral_min F hF
          ⟨hx.le, hx1⟩ _ (intervalIntegrable_rpow_kernel hα hp hx.le)
    _ = ∫ z, x ^ (p + α) / Real.Gamma α *
          incompleteBeta (min (z / x) 1) (p + 1) α
          ∂weightedSumDistribution := by
        refine integral_congr_ae
          (ae_weightedSumDistribution_mem_Icc.mono fun z hz => ?_)
        have hc0 : (0 : ℝ) ≤ min z x := le_min hz.1 hx.le
        have hcx : min z x ≤ x := min_le_right z x
        have hker : ∀ t : ℝ,
            (x - t) ^ (α - 1) / Real.Gamma α * t ^ p =
            (Real.Gamma α)⁻¹ * ((x - t) ^ (α - 1) * t ^ p) := by
          intro t
          ring
        simp_rw [hker]
        rw [intervalIntegral.integral_const_mul,
          integral_rpow_mul_rpow_eq_incompleteBeta hx hc0 hcx]
        have hmin : min z x / x = min (z / x) 1 := by
          rw [← min_div_div_right hx.le, div_self hx.ne']
        rw [hmin]
        ring
    _ = x ^ (p + α) / Real.Gamma α *
          ∫ z, incompleteBeta (min (z / x) 1) (p + 1) α
            ∂weightedSumDistribution :=
        integral_const_mul _ _

/-- **The reflected scaling identity**: for `0 < x`, `0 ≤ c ≤ x`,
`∫_c^x (x-t)^{α-1} t^p dt = x^{p+α}·B_{1-c/x}(α, p+1)` — the `t ↦ x-t`
reflection of the scaling identity, with the beta parameters
swapped. -/
theorem integral_rpow_mul_rpow_eq_incompleteBeta_reflected
    {x c α p : ℝ} (hx : 0 < x) (hc0 : 0 ≤ c) (hcx : c ≤ x) :
    ∫ t in c..x, (x - t) ^ (α - 1) * t ^ p =
      x ^ (p + α) * incompleteBeta (1 - c / x) α (p + 1) := by
  have hrefl : ∫ t in c..x, (x - t) ^ (α - 1) * t ^ p =
      ∫ s in (0 : ℝ)..(x - c), (x - s) ^ p * s ^ (α - 1) := by
    have hcomp := intervalIntegral.integral_comp_sub_left
      (f := fun s => (x - s) ^ p * s ^ (α - 1)) (a := c) (b := x) x
    rw [sub_self] at hcomp
    rw [← hcomp]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [show x - (x - t) = t from by ring]
    ring
  rw [hrefl]
  have h := integral_rpow_mul_rpow_eq_incompleteBeta
    (x := x) (c := x - c) (α := p + 1) (p := α - 1) hx
    (by linarith) (by linarith)
  rw [show p + 1 - 1 = p from by ring] at h
  rw [h, show α - 1 + (p + 1) = p + α from by ring,
    show α - 1 + 1 = α from by ring,
    show (x - c) / x = 1 - c / x from by
      rw [sub_div, div_self hx.ne']]

/-- The weighted-sum law's lower CDF is the Fabius function. -/
theorem weightedSumDistribution_real_Iic_eq_fabiusReal
    (F : BoundedFabius) (hF : IsFabius F) (t : ℝ) :
    weightedSumDistribution.real (Iic t) = fabiusReal F t := by
  have h1 : weightedSumCDF t = weightedSumDistribution.real (Iic t) := by
    rw [weightedSumCDF, ProbabilityTheory.cdf_eq_real]
  rw [← h1, weightedSumCDF_eq_fabiusReal F hF t]

/-- **The incomplete-beta master formula** (CDF display, positive real
parameters): for `α > 0`, `p ≥ 0`, and `0 < x ≤ 1`,
`I₀₊^α [t^p·F(t)](x) = x^{p+α}/Γ(α) · E[B_{1-min(X/x,1)}(α, p+1)]`.
Samples at or above `x` contribute `B_0 = 0`, so the clamp implements
the indicator `1_{X<x}` of the report's display. -/
theorem fractionalVolterra_rpow_mul_fabiusReal
    (F : BoundedFabius) (hF : IsFabius F) {α p x : ℝ}
    (hα : 0 < α) (hp : 0 ≤ p) (hx : 0 < x) (hx1 : x ≤ 1) :
    fractionalVolterra α 0 (fun t => t ^ p * fabiusReal F t) x =
      x ^ (p + α) / Real.Gamma α *
        ∫ z, incompleteBeta (1 - min (z / x) 1) α (p + 1)
          ∂weightedSumDistribution := by
  calc fractionalVolterra α 0 (fun t => t ^ p * fabiusReal F t) x
      = ∫ t in (0 : ℝ)..x, weightedSumDistribution.real (Iic t) •
          ((x - t) ^ (α - 1) / Real.Gamma α * t ^ p) := by
        rw [fractionalVolterra]
        refine intervalIntegral.integral_congr fun t _ => ?_
        simp only [smul_eq_mul]
        rw [weightedSumDistribution_real_Iic_eq_fabiusReal F hF t]
        ring
    _ = ∫ z, (∫ t in min (max z 0) x..x,
          (x - t) ^ (α - 1) / Real.Gamma α * t ^ p)
          ∂weightedSumDistribution :=
        intervalIntegral_cdf_smul_eq_integral_clamp
          weightedSumDistribution hx.le _
          (intervalIntegrable_rpow_kernel hα hp hx.le)
    _ = ∫ z, x ^ (p + α) / Real.Gamma α *
          incompleteBeta (1 - min (z / x) 1) α (p + 1)
          ∂weightedSumDistribution := by
        refine integral_congr_ae
          (ae_weightedSumDistribution_mem_Icc.mono fun z hz => ?_)
        rw [max_eq_left hz.1]
        have hc0 : (0 : ℝ) ≤ min z x := le_min hz.1 hx.le
        have hcx : min z x ≤ x := min_le_right z x
        have hker : ∀ t : ℝ,
            (x - t) ^ (α - 1) / Real.Gamma α * t ^ p =
            (Real.Gamma α)⁻¹ * ((x - t) ^ (α - 1) * t ^ p) := by
          intro t
          ring
        simp_rw [hker]
        rw [intervalIntegral.integral_const_mul,
          integral_rpow_mul_rpow_eq_incompleteBeta_reflected hx hc0 hcx]
        have hmin : min z x / x = min (z / x) 1 := by
          rw [← min_div_div_right hx.le, div_self hx.ne']
        rw [hmin]
        ring
    _ = x ^ (p + α) / Real.Gamma α *
          ∫ z, incompleteBeta (1 - min (z / x) 1) α (p + 1)
            ∂weightedSumDistribution :=
        integral_const_mul _ _

end Fabius
