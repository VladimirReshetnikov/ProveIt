import FabiusFunction.CDFLayerCake
import FabiusFunction.FractionalVolterraSemigroup
import Mathlib.Probability.CDF

/-!
# Fractional lower-CDF layer-cake formulas

This module combines the atom-preserving lower-CDF layer cake with the exact
positive real-order Volterra kernel.  For an arbitrary finite measure, the
fractional integral of its cumulative mass is a Gamma-normalized stopped
power moment.  No probability normalization or atomlessness is required.

The first theorem has no support hypothesis and clamps every sample to the
integration interval.  A one-sided support hypothesis gives the familiar
positive-part formula, while compact interval support gives the corresponding
endpoint moment.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped Interval Real

namespace Fabius

/-- **Fractional lower-CDF layer cake without a support hypothesis.**  For a
finite measure `μ`, positive order `α`, and `a ≤ x`,

`I^α_a (t ↦ μ.real (Iic t)) x
  = Γ(α+1)⁻¹ ∫ (x - min (max z a) x)^α dμ(z)`.

Mass below `a` contributes the full power, mass between `a` and `x` is
stopped at its location, and mass above `x` contributes zero. -/
theorem fractionalVolterra_measureReal_Iic_eq_integral_clamp
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {α a x : ℝ} (hα : 0 < α) (hax : a ≤ x) :
    fractionalVolterra α a (fun t => μ.real (Iic t)) x =
      (∫ z : ℝ, (x - min (max z a) x) ^ α ∂μ) /
        Real.Gamma (α + 1) := by
  let k : ℝ → ℝ :=
    fun t => (x - t) ^ (α - 1) / Real.Gamma α
  have hk : IntervalIntegrable k volume a x := by
    have hkernel := intervalIntegrable_fractionalVolterra_kernel
      (E := ℝ) hα hax (f := fun _ => (1 : ℝ)) continuousOn_const
    simpa only [k, smul_eq_mul, mul_one] using hkernel
  have hlayer :=
    intervalIntegral_cdf_smul_eq_integral_clamp μ hax k hk
  have hleft :
      fractionalVolterra α a (fun t => μ.real (Iic t)) x =
        ∫ t in a..x, μ.real (Iic t) • k t := by
    rw [fractionalVolterra]
    apply intervalIntegral.integral_congr
    intro t _ht
    simp only [k, smul_eq_mul]
    ring
  have hinner (z : ℝ) :
      (∫ t in min (max z a) x..x, k t) =
        (x - min (max z a) x) ^ α / Real.Gamma (α + 1) := by
    have hclamp : min (max z a) x ≤ x := min_le_right _ _
    simpa only [fractionalVolterra, k, smul_eq_mul, mul_one] using
      (fractionalVolterra_const (E := ℝ) hα hclamp (1 : ℝ))
  calc
    fractionalVolterra α a (fun t => μ.real (Iic t)) x =
        ∫ t in a..x, μ.real (Iic t) • k t := hleft
    _ = ∫ z : ℝ, (∫ t in min (max z a) x..x, k t) ∂μ :=
      hlayer
    _ = ∫ z : ℝ,
        (x - min (max z a) x) ^ α / Real.Gamma (α + 1) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hinner)
    _ = (∫ z : ℝ, (x - min (max z a) x) ^ α ∂μ) /
        Real.Gamma (α + 1) := by
      rw [integral_div]

/-- **Positive-part fractional lower-CDF formula.**  If `μ` is almost
surely supported to the right of `a`, then for every `a ≤ x`,

`I^α_a (t ↦ μ.real (Iic t)) x
  = Γ(α+1)⁻¹ ∫ max (x-z) 0 ^ α dμ(z)`.

Only the lower support bound is needed; the measure may be unbounded above
and may have atoms. -/
theorem fractionalVolterra_measureReal_Iic_eq_integral_posPart
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {α a x : ℝ} (hα : 0 < α) (hax : a ≤ x)
    (hμ : ∀ᵐ z ∂μ, a ≤ z) :
    fractionalVolterra α a (fun t => μ.real (Iic t)) x =
      (∫ z : ℝ, (max (x - z) 0) ^ α ∂μ) /
        Real.Gamma (α + 1) := by
  rw [fractionalVolterra_measureReal_Iic_eq_integral_clamp μ hα hax]
  congr 1
  apply integral_congr_ae
  filter_upwards [hμ] with z hz
  rw [max_eq_left hz, ← max_sub_sub_left, sub_self]

/-- Probability-CDF form of the positive-part identity.  For a probability
measure almost surely supported to the right of `a`, its Mathlib CDF has the
same Gamma-normalized stopped-power fractional integral. -/
theorem fractionalVolterra_cdf_eq_integral_posPart
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {α a x : ℝ} (hα : 0 < α) (hax : a ≤ x)
    (hμ : ∀ᵐ z ∂μ, a ≤ z) :
    fractionalVolterra α a (ProbabilityTheory.cdf μ) x =
      (∫ z : ℝ, (max (x - z) 0) ^ α ∂μ) /
        Real.Gamma (α + 1) := by
  calc
    fractionalVolterra α a (ProbabilityTheory.cdf μ) x =
        fractionalVolterra α a (fun t => μ.real (Iic t)) x := by
      apply fractionalVolterra_congr
      intro t _ht
      rw [ProbabilityTheory.cdf_eq_real]
    _ = (∫ z : ℝ, (max (x - z) 0) ^ α ∂μ) /
        Real.Gamma (α + 1) :=
      fractionalVolterra_measureReal_Iic_eq_integral_posPart
        μ hα hax hμ

/-- **Endpoint fractional moment for an interval-supported measure.**  If
`μ` is almost surely supported on `[a,b]`, then

`I^α_a (t ↦ μ.real (Iic t)) b
  = Γ(α+1)⁻¹ ∫ (b-z)^α dμ(z)`.

This includes atomic finite measures and does not assume total mass one. -/
theorem fractionalVolterra_measureReal_Iic_eq_integral_rpow_of_ae_mem_Icc
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {α a b : ℝ} (hα : 0 < α) (hab : a ≤ b)
    (hμ : ∀ᵐ z ∂μ, z ∈ Icc a b) :
    fractionalVolterra α a (fun t => μ.real (Iic t)) b =
      (∫ z : ℝ, (b - z) ^ α ∂μ) / Real.Gamma (α + 1) := by
  calc
    fractionalVolterra α a (fun t => μ.real (Iic t)) b =
        (∫ z : ℝ, (max (b - z) 0) ^ α ∂μ) /
          Real.Gamma (α + 1) :=
      fractionalVolterra_measureReal_Iic_eq_integral_posPart
        μ hα hab (hμ.mono fun _ hz => hz.1)
    _ = (∫ z : ℝ, (b - z) ^ α ∂μ) /
        Real.Gamma (α + 1) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hμ] with z hz
      rw [max_eq_left (sub_nonneg.mpr hz.2)]

end Fabius
