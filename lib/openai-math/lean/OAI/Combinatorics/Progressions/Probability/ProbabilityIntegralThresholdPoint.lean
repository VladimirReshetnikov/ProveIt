import Mathlib.MeasureTheory.Integral.Average

namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {Λ : Type*} [MeasurableSpace Λ]

theorem probabilityIntegralThresholdPoint (μ : Measure Λ) [IsProbabilityMeasure μ]
    {m : Λ → ℝ} (hm : Integrable m μ) {c : ℝ} (hc : c ≤ ∫ l, m l ∂μ) :
    ∃ l, c ≤ m l := by
  obtain ⟨l, hl⟩ := exists_integral_le hm
  exact ⟨l, hc.trans hl⟩

theorem probabilityIntegralThresholdPoint_notMem_null
    (μ : Measure Λ) [IsProbabilityMeasure μ]
    {m : Λ → ℝ} (hm : Integrable m μ) {c : ℝ} (hc : c ≤ ∫ l, m l ∂μ)
    {Z : Set Λ} (hZ : μ Z = 0) : ∃ l, l ∉ Z ∧ c ≤ m l := by
  obtain ⟨l, hlZ, hl⟩ := exists_notMem_null_integral_le hm hZ
  exact ⟨l, hlZ, hc.trans hl⟩

end Erdos3

end

end OAI
