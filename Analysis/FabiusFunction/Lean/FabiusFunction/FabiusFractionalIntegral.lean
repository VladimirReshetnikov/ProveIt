import FabiusFunction.FractionalCDFLayerCake
import FabiusFunction.ProbabilityRepresentation

/-!
# Fractional integrals of the Fabius distribution function

The bounded Fabius function is the cumulative distribution function of the
dyadic weighted-uniform random series.  Combining that identification with
the fractional lower-CDF layer cake gives the exact positive-real-order
Riemann--Liouville formula

`I^α_0 F(x) = Γ(α+1)⁻¹ E[(x-X)₊^α]`

for every real endpoint `x`.  Both the pushforward-law and the underlying
product-space expectation are exposed.  At `x = 1`, reflection of the law
turns the stopped power into the ordinary real moment of `X`.
-/

set_option autoImplicit false

open Filter MeasureTheory ProbabilityTheory Set
open scoped Interval Real

namespace Fabius
namespace ProbabilityRepresentation

private lemma weightedSumDistribution_real_Iic_eq_fabiusReal
    (F : BoundedFabius) (hF : IsFabius F) (t : ℝ) :
    weightedSumDistribution.real (Iic t) = fabiusReal F t := by
  rw [← weightedSumCDF_eq_fabiusReal F hF t,
    weightedSumCDF, ProbabilityTheory.cdf_eq_real]

/-- **Fractional truncated-power formula for the Fabius CDF.**  For every
positive real order and every real endpoint,

`I^α_0 F(x) = Γ(α+1)⁻¹ ∫ max (x-z) 0 ^ α dμ(z)`,

where `μ` is `weightedSumDistribution`.  The theorem includes `x ≤ 0`,
where both sides vanish, and requires neither a density nor atomlessness. -/
theorem fractionalVolterra_fabiusReal_eq_integral_posPart
    (F : BoundedFabius) (hF : IsFabius F)
    (α x : ℝ) (hα : 0 < α) :
    fractionalVolterra α 0 (fabiusReal F) x =
      (∫ z : ℝ, (max (x - z) 0) ^ α ∂weightedSumDistribution) /
        Real.Gamma (α + 1) := by
  have hsupport := ae_weightedSumDistribution_mem_Icc
  have hnonneg : ∀ᵐ z ∂weightedSumDistribution, 0 ≤ z :=
    hsupport.mono fun _ hz => hz.1
  by_cases hx : 0 ≤ x
  · calc
      fractionalVolterra α 0 (fabiusReal F) x =
          fractionalVolterra α 0
            (fun t => weightedSumDistribution.real (Iic t)) x := by
        apply fractionalVolterra_congr
        intro t _ht
        exact (weightedSumDistribution_real_Iic_eq_fabiusReal F hF t).symm
      _ = (∫ z : ℝ, (max (x - z) 0) ^ α
            ∂weightedSumDistribution) / Real.Gamma (α + 1) :=
        fractionalVolterra_measureReal_Iic_eq_integral_posPart
          weightedSumDistribution hα hx hnonneg
  · have hxlt : x < 0 := lt_of_not_ge hx
    have hleft : fractionalVolterra α 0 (fabiusReal F) x = 0 := by
      calc
        fractionalVolterra α 0 (fabiusReal F) x =
            fractionalVolterra α 0 (fun _ : ℝ => (0 : ℝ)) x := by
          apply fractionalVolterra_congr
          intro t ht
          rw [uIcc_of_ge hxlt.le] at ht
          exact hF.zero_of_nonpos t ht.2
        _ = 0 := by simp [fractionalVolterra]
    have hmoment :
        (∫ z : ℝ, (max (x - z) 0) ^ α
          ∂weightedSumDistribution) = 0 := by
      calc
        (∫ z : ℝ, (max (x - z) 0) ^ α
            ∂weightedSumDistribution) =
            ∫ _z : ℝ, (0 : ℝ) ∂weightedSumDistribution := by
          apply integral_congr_ae
          filter_upwards [hnonneg] with z hz
          rw [max_eq_right (by linarith : x - z ≤ 0),
            Real.zero_rpow hα.ne']
        _ = 0 := by simp
    rw [hleft, hmoment, zero_div]

/-- Product-space form of
`fractionalVolterra_fabiusReal_eq_integral_posPart`.  It identifies the same
fractional integral with the expectation of the stopped power of the explicit
dyadic coordinate series. -/
theorem fractionalVolterra_fabiusReal_eq_uniformProduct_integral_posPart
    (F : BoundedFabius) (hF : IsFabius F)
    (α x : ℝ) (hα : 0 < α) :
    fractionalVolterra α 0 (fabiusReal F) x =
      (∫ ω : SampleSpace,
          (max (x - weightedCoordinateSum ω) 0) ^ α ∂uniformProduct) /
        Real.Gamma (α + 1) := by
  rw [fractionalVolterra_fabiusReal_eq_integral_posPart F hF α x hα,
    weightedSumDistribution,
    integral_map_of_stronglyMeasurable measurable_weightedCoordinateSum]
  exact ((Real.continuous_rpow_const hα.le).comp
    ((continuous_const.sub continuous_id).max continuous_const)).stronglyMeasurable

/-- At the unit endpoint, the fractional integral of the Fabius CDF is the
ordinary positive real moment of its weighted-sum law divided by
`Gamma (α + 1)`.  Reflection of the law is what removes `1 - z`. -/
theorem fractionalVolterra_fabiusReal_one_eq_integral_rpow
    (F : BoundedFabius) (hF : IsFabius F)
    (α : ℝ) (hα : 0 < α) :
    fractionalVolterra α 0 (fabiusReal F) 1 =
      (∫ z : ℝ, z ^ α ∂weightedSumDistribution) /
        Real.Gamma (α + 1) := by
  have hsupport := ae_weightedSumDistribution_mem_Icc
  rw [fractionalVolterra_fabiusReal_eq_integral_posPart F hF α 1 hα]
  congr 1
  calc
    (∫ z : ℝ, (max (1 - z) 0) ^ α ∂weightedSumDistribution) =
        ∫ z : ℝ, (1 - z) ^ α ∂weightedSumDistribution := by
      apply integral_congr_ae
      filter_upwards [hsupport] with z hz
      rw [max_eq_left (sub_nonneg.mpr hz.2)]
    (∫ z : ℝ, (1 - z) ^ α ∂weightedSumDistribution) =
        ∫ z : ℝ, z ^ α
          ∂(weightedSumDistribution.map (fun z : ℝ => 1 - z)) := by
      symm
      rw [integral_map_of_stronglyMeasurable (by fun_prop)
        (Real.continuous_rpow_const hα.le).stronglyMeasurable]
    _ = ∫ z : ℝ, z ^ α ∂weightedSumDistribution := by
      rw [weightedSumDistribution_reflection]

/-- Product-space form of the endpoint moment identity. -/
theorem fractionalVolterra_fabiusReal_one_eq_uniformProduct_integral_rpow
    (F : BoundedFabius) (hF : IsFabius F)
    (α : ℝ) (hα : 0 < α) :
    fractionalVolterra α 0 (fabiusReal F) 1 =
      (∫ ω : SampleSpace, (weightedCoordinateSum ω) ^ α
        ∂uniformProduct) / Real.Gamma (α + 1) := by
  rw [fractionalVolterra_fabiusReal_one_eq_integral_rpow F hF α hα,
    weightedSumDistribution,
    integral_map_of_stronglyMeasurable measurable_weightedCoordinateSum
      (Real.continuous_rpow_const hα.le).stronglyMeasurable]

end ProbabilityRepresentation
end Fabius
