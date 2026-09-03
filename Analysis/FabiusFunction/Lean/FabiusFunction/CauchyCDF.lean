import FabiusFunction.CDFLayerCake
import FabiusFunction.CauchyTransform
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Cauchy transforms through compactly supported CDFs

This module gives an atom-exact integration-by-parts formula for the oriented
Cauchy kernel.  If a finite measure `μ` is almost everywhere supported on
`[a,b]`, then its transform is the endpoint kernel weighted by the total mass,
minus the squared kernel integrated against the closed CDF
`t ↦ μ.real (Set.Iic t)`.

The probability version replaces the total mass by one and exposes Mathlib's
`ProbabilityTheory.cdf`.  The final theorem identifies that CDF with a bounded
Fabius function for the dyadic weighted-sum law.  Closed lower rays are used
throughout, so atoms are retained rather than discarded at their locations.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace Fabius

open ProbabilityRepresentation

/-- **Compact-support Cauchy--CDF integration by parts.**  Let `μ` be a
finite measure supported almost everywhere on `[a,b]`.  Off the complexified
support interval,

`∫ (z-x)⁻¹ dμ(x) = μ(ℝ) (z-b)⁻¹
  - ∫ₐᵇ μ((- ∞,t]) (z-t)⁻² dt`.

The closed CDF `μ.real (Iic t)` makes the formula exact for measures with
atoms.  Only almost-everywhere support is required. -/
theorem integral_inv_sub_eq_mass_smul_sub_intervalIntegral_measureReal_Iic
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b : ℝ} (hab : a ≤ b)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b)
    {z : ℂ} (hz : z ∉ algebraMap ℝ ℂ '' Icc a b) :
    (∫ x : ℝ, (z - (x : ℂ))⁻¹ ∂μ) =
      μ.real univ • (z - (b : ℂ))⁻¹ -
        ∫ t in a..b,
          μ.real (Iic t) • ((z - (t : ℂ))⁻¹ ^ 2) := by
  let r : ℝ → ℂ := fun t => (z - (t : ℂ))⁻¹
  let k : ℝ → ℂ := fun t => r t ^ 2
  have hne (t : ℝ) (ht : t ∈ Icc a b) : z - (t : ℂ) ≠ 0 := by
    intro hzero
    apply hz
    refine ⟨t, ht, ?_⟩
    simpa only [Complex.coe_algebraMap] using (sub_eq_zero.mp hzero).symm
  have hrcont : ContinuousOn r (Icc a b) := by
    dsimp only [r]
    exact
      (by fun_prop : ContinuousOn (fun t : ℝ => z - (t : ℂ)) (Icc a b)).inv₀
        hne
  have hkcont : ContinuousOn k (Icc a b) := by
    exact hrcont.pow 2
  have hk : IntervalIntegrable k volume a b :=
    hkcont.intervalIntegrable_of_Icc hab
  have hderiv (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt r (k t) t := by
    have hsub : HasDerivAt (fun w : ℂ => z - w) (-1) (t : ℂ) := by
      simpa only [id_eq] using (hasDerivAt_id (t : ℂ)).const_sub z
    have hinv := hsub.inv (hne t ht)
    simpa [r, k] using hinv.comp_ofReal
  have hprimitive (x : ℝ) (hx : x ∈ Icc a b) :
      (∫ t in x..b, k t) = r b - r x := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [uIcc_of_le hx.2] at ht
      exact hderiv t ⟨hx.1.trans ht.1, ht.2⟩
    · exact
        (hkcont.mono (Icc_subset_Icc hx.1 le_rfl)).intervalIntegrable_of_Icc hx.2
  have hrestrict : μ.restrict (Icc a b) = μ :=
    Measure.restrict_eq_self_of_ae_mem hμ
  have hrμ : Integrable r μ := by
    rw [← hrestrict]
    exact hrcont.integrableOn_Icc
  have hlayer :=
    intervalIntegral_cdf_smul_eq_integral_of_ae_mem_Icc
      μ hab hμ k hk
  have hinner :
      (∫ x : ℝ, (∫ t in x..b, k t) ∂μ) =
        μ.real univ • r b - ∫ x : ℝ, r x ∂μ := by
    calc
      (∫ x : ℝ, (∫ t in x..b, k t) ∂μ) =
          ∫ x : ℝ, (r b - r x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hμ] with x hx
        exact hprimitive x hx
      _ = (∫ _ : ℝ, r b ∂μ) - ∫ x : ℝ, r x ∂μ := by
        rw [integral_sub (integrable_const _) hrμ]
      _ = μ.real univ • r b - ∫ x : ℝ, r x ∂μ := by
        rw [integral_const]
  change (∫ x : ℝ, r x ∂μ) =
    μ.real univ • r b - ∫ t in a..b, μ.real (Iic t) • k t
  rw [hlayer, hinner]
  abel

/-- Probability normalization of
`integral_inv_sub_eq_mass_smul_sub_intervalIntegral_measureReal_Iic`.
The total-mass term is one and the cumulative mass is exposed as
`ProbabilityTheory.cdf`. -/
theorem integral_inv_sub_eq_sub_intervalIntegral_cdf
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a b : ℝ} (hab : a ≤ b)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b)
    {z : ℂ} (hz : z ∉ algebraMap ℝ ℂ '' Icc a b) :
    (∫ x : ℝ, (z - (x : ℂ))⁻¹ ∂μ) =
      (z - (b : ℂ))⁻¹ -
        ∫ t in a..b,
          ProbabilityTheory.cdf μ t • ((z - (t : ℂ))⁻¹ ^ 2) := by
  simpa only [ProbabilityTheory.cdf_eq_real, probReal_univ, one_smul] using
    (integral_inv_sub_eq_mass_smul_sub_intervalIntegral_measureReal_Iic
      μ hab hμ hz)

/-- The Stieltjes transform of the dyadic Fabius law written directly through
its CDF.  This is the compact-support integration-by-parts formula

`S(z) = (z-1)⁻¹ - ∫₀¹ F(t) (z-t)⁻² dt`

on the natural domain `fabiusStieltjesDomain`. -/
theorem fabiusStieltjesTransform_eq_inv_sub_one_sub_intervalIntegral_fabiusReal
    (F : BoundedFabius) (hF : IsFabius F)
    {z : ℂ} (hz : z ∈ fabiusStieltjesDomain) :
    fabiusStieltjesTransform z =
      (z - (1 : ℂ))⁻¹ -
        ∫ t in (0 : ℝ)..1,
          fabiusReal F t • ((z - (t : ℂ))⁻¹ ^ 2) := by
  have hz' : z ∉ algebraMap ℝ ℂ '' Icc (0 : ℝ) 1 := by
    simpa only [fabiusStieltjesDomain, mem_compl_iff] using hz
  calc
    fabiusStieltjesTransform z =
        ∫ x : ℝ, (z - (x : ℂ))⁻¹ ∂weightedSumDistribution :=
      fabiusStieltjesTransform_apply z
    _ = (z - (1 : ℂ))⁻¹ -
        ∫ t in (0 : ℝ)..1,
          weightedSumCDF t • ((z - (t : ℂ))⁻¹ ^ 2) := by
      simpa [weightedSumCDF] using
        (integral_inv_sub_eq_sub_intervalIntegral_cdf
          weightedSumDistribution (by norm_num)
            ae_weightedSumDistribution_mem_Icc hz')
    _ = (z - (1 : ℂ))⁻¹ -
        ∫ t in (0 : ℝ)..1,
          fabiusReal F t • ((z - (t : ℂ))⁻¹ ^ 2) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro t _
      change weightedSumCDF t • ((z - (t : ℂ))⁻¹ ^ 2) =
        fabiusReal F t • ((z - (t : ℂ))⁻¹ ^ 2)
      rw [weightedSumCDF_eq_fabiusReal F hF t]

end Fabius
