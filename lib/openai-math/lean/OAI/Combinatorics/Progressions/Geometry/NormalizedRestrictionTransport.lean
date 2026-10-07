import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Restrict

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ENNReal

theorem normalizedRestriction_map_equiv {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (e : X ≃ᵐ Y)
    (μ : Measure X) (ν : Measure Y) {c : ℝ≥0∞} (hc : c ≠ 0) (hcfin : c ≠ ⊤)
    (hmap : μ.map e = c • ν) (s : Set X) :
    ((μ s)⁻¹ • μ.restrict s).map e =
      (ν (e '' s))⁻¹ • ν.restrict (e '' s) := by
  have hm : μ s = c * ν (e '' s) := by
    have h := congrArg (fun m : Measure Y => m (e '' s)) hmap
    simpa only [e.map_apply, Set.preimage_image_eq _ e.injective,
      Measure.smul_apply, smul_eq_mul] using h
  have hr : (μ.restrict s).map e = c • ν.restrict (e '' s) := by
    have h := e.restrict_map μ (e '' s)
    rw [hmap, Measure.restrict_smul, Set.preimage_image_eq _ e.injective] at h
    exact h.symm
  rw [Measure.map_smul _ e.measurable.aemeasurable, hr, hm, smul_smul,
    ENNReal.mul_inv (Or.inl hc) (Or.inl hcfin), mul_right_comm,
    ENNReal.inv_mul_cancel hc hcfin, one_mul]

end Erdos3

end

end OAI
