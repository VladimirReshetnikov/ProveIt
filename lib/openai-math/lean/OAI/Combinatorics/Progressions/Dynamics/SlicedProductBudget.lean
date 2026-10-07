import OAI.Combinatorics.Progressions.Estimates.FourSlicedProductSmoothing

namespace OAI

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory
open scoped NNReal

variable {ι : Type*} [Fintype ι]

theorem uniformCap_log (r : ℝ) (hr : 0 < r) :
    Real.log (uniformCap ι r hr : ℝ) = (Fintype.card ι : ℝ) * Real.log 4 - Real.log r := by
  change Real.log (r⁻¹ * 4 ^ Fintype.card ι) = _
  rw [Real.log_mul (inv_ne_zero hr.ne') (pow_ne_zero _ (by norm_num)), Real.log_inv, Real.log_pow]
  ring

theorem uniformCap_slice_log (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    Real.log (uniformCap ι (c * δ ^ (Fintype.card ι + 1)) (mul_pos hc (pow_pos hδ _)) : ℝ) =
      (Fintype.card ι : ℝ) * Real.log 4 - Real.log c -
        (Fintype.card ι + 1 : ℕ) * Real.log δ := by
  rw [uniformCap_log, Real.log_mul hc.ne' (pow_ne_zero _ hδ.ne'), Real.log_pow]
  ring

theorem fourDensity_with_independent_remainder {T : Type*} [MeasurableSpace T]
    (μ : Measure T) [IsProbabilityMeasure μ] {z : T → ℝ} (hz : Measurable z)
    {A B C D : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) (hC : C.Admissible) (hD : D.Admissible) :
    let f := independentShiftDensity μ z (fourDensity A B C D)
    (∀ x, f x ∈ Set.Icc (0 : ℝ) (pairCap C D)) ∧
      LipschitzWith (pairCapNN hC hD * (2 * pairCapNN hA hB)) f ∧
      Integrable f ∧ (∫ x, f x) = 1 := by
  have hLip := fourDensity_lipschitz hA hB hC hD
  have hm := hLip.continuous.measurable
  have hp := fourDensity_probability_density hA hB hC hD
  have hb := fourDensity_cap hA hB hC hD
  have hn (x : ℝ) : ‖fourDensity A B C D x‖ ≤ pairCap C D := by
    rw [Real.norm_of_nonneg (hb x).1]
    exact (hb x).2
  have hmix := independentShiftDensity_probability_density μ hz hm hp.2.1 hp.1 hp.2.2
  exact ⟨independentShiftDensity_cap μ hz hm hb,
    independentShiftDensity_lipschitz μ hz _ hLip hn, hmix.2.1, hmix.2.2⟩

end Erdos3.SlicedProductBlock

end

end OAI
