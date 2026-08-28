import FabiusFunction.FabiusInverse
import FabiusFunction.ProbabilityRepresentation

/-!
# Quantile transport for the Fabius distribution

This module isolates the measure-theoretic content of inverse-CDF
substitution.  The generic theorem says that a unit-interval-valued quantile
whose order sublevel sets are described by the CDF pushes uniform Lebesgue
measure forward to the original probability law.  Its specialization
identifies the pushforward by `fabiusInv` with the weighted-sum distribution.

The measure equality is stronger than any individual change-of-variables
formula: it transports every measurable statistic for which the relevant
integral is defined.
-/

set_option autoImplicit false

open Set MeasureTheory

namespace Fabius

/-- **Probability-quantile pushforward from sublevel events.**  A measurable
map from the unit interval has law `μ` as soon as, for every threshold `x`,
its sublevel event agrees almost everywhere with
`{y | y ≤ cdf μ x}`.

This support-free form applies to arbitrary real probability measures.  The
almost-everywhere hypothesis is intentionally sharp: it ignores the harmless
choice of quantile value at the zero endpoint and other null-set conventions. -/
theorem map_quantile_eq
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (Q : ℝ → ℝ)
    (hQm : AEMeasurable Q (volume.restrict (Icc (0 : ℝ) 1)))
    (hinv : ∀ x : ℝ, ∀ᵐ y ∂volume.restrict (Icc (0 : ℝ) 1),
      (Q y ≤ x ↔ y ≤ ProbabilityTheory.cdf μ x)) :
    Measure.map Q (volume.restrict (Icc (0 : ℝ) 1)) = μ := by
  letI : IsFiniteMeasure
      (Measure.map Q (volume.restrict (Icc (0 : ℝ) 1))) :=
    (volume.restrict (Icc (0 : ℝ) 1)).isFiniteMeasure_map Q
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply_of_aemeasurable hQm measurableSet_Iic]
  calc
    (volume.restrict (Icc (0 : ℝ) 1)) (Q ⁻¹' Iic x) =
        (volume.restrict (Icc (0 : ℝ) 1))
          (Iic (ProbabilityTheory.cdf μ x)) := by
      apply measure_congr
      filter_upwards [hinv x] with y hy
      change (Q y ≤ x) = (y ≤ ProbabilityTheory.cdf μ x)
      exact propext hy
    _ = volume
        (Iic (ProbabilityTheory.cdf μ x) ∩ Icc (0 : ℝ) 1) :=
      Measure.restrict_apply measurableSet_Iic
    _ = volume (Icc 0 (ProbabilityTheory.cdf μ x)) := by
      congr 1
      ext y
      simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨hycdf, hy₀, _hy₁⟩
        exact ⟨hy₀, hycdf⟩
      · rintro ⟨hy₀, hycdf⟩
        exact ⟨hycdf, hy₀, hycdf.trans (ProbabilityTheory.cdf_le_one μ x)⟩
    _ = ENNReal.ofReal (ProbabilityTheory.cdf μ x) := by
      rw [Real.volume_Icc, sub_zero]
    _ = μ (Iic x) := ProbabilityTheory.ofReal_cdf μ x

/-- **Compact inverse-CDF pushforward.**  Let `μ` be a probability measure
supported on `[0,1]`.  If `Q` takes `[0,1]` to itself and its sublevel sets
satisfy

`Q y ≤ x ↔ y ≤ cdf μ x`

for `x,y ∈ [0,1]`, then pushing uniform Lebesgue measure on `[0,1]`
through `Q` recovers `μ`.

Only almost-everywhere measurability of `Q` with respect to the source
measure is needed.  The order hypothesis also permits atoms: it is the exact
property of the chosen quantile that the proof uses. -/
theorem map_inverseCDF_volume_restrict_Icc
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (Q : ℝ → ℝ)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) 1)
    (hQm : AEMeasurable Q (volume.restrict (Icc (0 : ℝ) 1)))
    (hQ : MapsTo Q (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hinv : ∀ ⦃x y : ℝ⦄, x ∈ Icc (0 : ℝ) 1 → y ∈ Icc (0 : ℝ) 1 →
      (Q y ≤ x ↔ y ≤ ProbabilityTheory.cdf μ x)) :
    Measure.map Q (volume.restrict (Icc (0 : ℝ) 1)) = μ := by
  have hμ_restrict : μ.restrict (Icc (0 : ℝ) 1) = μ :=
    Measure.restrict_eq_self_of_ae_mem hμ
  have hμ_Icc : μ (Icc (0 : ℝ) 1) = 1 := by
    calc
      μ (Icc (0 : ℝ) 1) =
          (μ.restrict (Icc (0 : ℝ) 1)) Set.univ :=
        (Measure.restrict_apply_univ _).symm
      _ = μ Set.univ := by rw [hμ_restrict]
      _ = 1 := measure_univ
  letI : IsFiniteMeasure
      (Measure.map Q (volume.restrict (Icc (0 : ℝ) 1))) :=
    (volume.restrict (Icc (0 : ℝ) 1)).isFiniteMeasure_map Q
  apply MeasureTheory.Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply_of_aemeasurable hQm measurableSet_Iic,
    Measure.restrict_apply₀
      (hQm.nullMeasurableSet_preimage measurableSet_Iic)]
  by_cases hx₀ : x < 0
  · have hsource :
        (Q ⁻¹' Iic x) ∩ Icc (0 : ℝ) 1 = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      rintro y ⟨hyQx, hy⟩
      exact (not_lt_of_ge (hQ hy).1) (hyQx.trans_lt hx₀)
    have htarget : Iic x ∩ Icc (0 : ℝ) 1 = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      rintro y ⟨hyx, hy⟩
      exact (not_lt_of_ge hy.1) (hyx.trans_lt hx₀)
    have hμ_Iic : μ (Iic x) = 0 := by
      calc
        μ (Iic x) = (μ.restrict (Icc (0 : ℝ) 1)) (Iic x) := by
          rw [hμ_restrict]
        _ = μ (Iic x ∩ Icc (0 : ℝ) 1) :=
          Measure.restrict_apply measurableSet_Iic
        _ = 0 := by rw [htarget, measure_empty]
    calc
      volume ((Q ⁻¹' Iic x) ∩ Icc (0 : ℝ) 1) = 0 := by
        rw [hsource, measure_empty]
      _ = μ (Iic x) := hμ_Iic.symm
  by_cases hx₁ : 1 ≤ x
  · have hsource :
        (Q ⁻¹' Iic x) ∩ Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := by
      apply Set.Subset.antisymm inter_subset_right
      intro y hy
      exact ⟨(hQ hy).2.trans hx₁, hy⟩
    have htarget : Iic x ∩ Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := by
      apply Set.Subset.antisymm inter_subset_right
      intro y hy
      exact ⟨hy.2.trans hx₁, hy⟩
    have hμ_Iic : μ (Iic x) = 1 := by
      calc
        μ (Iic x) = (μ.restrict (Icc (0 : ℝ) 1)) (Iic x) := by
          rw [hμ_restrict]
        _ = μ (Iic x ∩ Icc (0 : ℝ) 1) :=
          Measure.restrict_apply measurableSet_Iic
        _ = μ (Icc (0 : ℝ) 1) := by rw [htarget]
        _ = 1 := hμ_Icc
    calc
      volume ((Q ⁻¹' Iic x) ∩ Icc (0 : ℝ) 1) =
          volume (Icc (0 : ℝ) 1) := by rw [hsource]
      _ = 1 := by simp [Real.volume_Icc]
      _ = μ (Iic x) := hμ_Iic.symm
  · have hx : x ∈ Icc (0 : ℝ) 1 :=
      ⟨le_of_not_gt hx₀, (lt_of_not_ge hx₁).le⟩
    have hsource :
        (Q ⁻¹' Iic x) ∩ Icc (0 : ℝ) 1 =
          Icc 0 (ProbabilityTheory.cdf μ x) := by
      apply Set.Subset.antisymm
      · rintro y ⟨hyQx, hy⟩
        exact ⟨hy.1, (hinv hx hy).mp hyQx⟩
      · rintro y ⟨hy₀, hycdf⟩
        have hy : y ∈ Icc (0 : ℝ) 1 :=
          ⟨hy₀, hycdf.trans (ProbabilityTheory.cdf_le_one μ x)⟩
        exact ⟨(hinv hx hy).mpr hycdf, hy⟩
    calc
      volume ((Q ⁻¹' Iic x) ∩ Icc (0 : ℝ) 1) =
          volume (Icc 0 (ProbabilityTheory.cdf μ x)) := by rw [hsource]
      _ = ENNReal.ofReal (ProbabilityTheory.cdf μ x) := by
        rw [Real.volume_Icc, sub_zero]
      _ = μ (Iic x) := ProbabilityTheory.ofReal_cdf μ x

/-- Uniform measure transported by the clamped inverse Fabius function is
exactly the law of the binary weighted sum.  This is the measure-level form of
quantile substitution for the Fabius distribution. -/
theorem map_fabiusInv_restrict_Icc_eq_weightedSumDistribution
    (F : BoundedFabius) (hF : IsFabius F) :
    Measure.map (fabiusInv F hF)
        (volume.restrict (Icc (0 : ℝ) 1)) =
      ProbabilityRepresentation.weightedSumDistribution := by
  apply map_inverseCDF_volume_restrict_Icc
  · exact (ae_mem_iff_measure_eq measurableSet_Icc.nullMeasurableSet).2 (by
      simpa using ProbabilityRepresentation.weightedSumDistribution_Icc)
  · exact (continuous_fabiusInv F hF).measurable.aemeasurable
  · intro y _hy
    exact fabiusInv_mem_Icc F hF y
  · intro x y hx hy
    change fabiusInv F hF y ≤ x ↔
      y ≤ ProbabilityRepresentation.weightedSumCDF x
    rw [ProbabilityRepresentation.weightedSumCDF_eq_fabiusReal F hF x]
    exact fabiusInv_le_iff_le_fabiusReal F hF hy hx

/-- Banach-valued quantile substitution for the Fabius law.  No separate
integrability assumption is needed: `integral_map_of_stronglyMeasurable`
identifies both integrals also in the non-integrable case, where the Bochner
integral is defined to be zero. -/
theorem integral_comp_fabiusInv_restrict_Icc_eq_weightedSumDistribution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : BoundedFabius) (hF : IsFabius F)
    (Φ : ℝ → E) (hΦ : StronglyMeasurable Φ) :
    (∫ y in Icc (0 : ℝ) 1, Φ (fabiusInv F hF y)) =
      ∫ x, Φ x ∂ProbabilityRepresentation.weightedSumDistribution := by
  rw [← map_fabiusInv_restrict_Icc_eq_weightedSumDistribution F hF]
  exact (MeasureTheory.integral_map_of_stronglyMeasurable
    (continuous_fabiusInv F hF).measurable hΦ).symm

end Fabius
