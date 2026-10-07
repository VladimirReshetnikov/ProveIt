import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real

namespace OAI

section

namespace Erdos3

open MeasureTheory Module

theorem euclidean_closedBall_volume_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (B : ℝ) (hB : 0 ≤ B) :
    volume.real (Metric.closedBall (0 : E) B) ≤ (2 * B) ^ finrank ℝ E := by
  let b := stdOrthonormalBasis ℝ E
  let e : E ≃ᵐ (Fin (finrank ℝ E) → ℝ) :=
    b.repr.toMeasurableEquiv.trans (MeasurableEquiv.toLp 2 _).symm
  have he : MeasurePreserving e :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).comp b.measurePreserving_repr
  let C : Set (Fin (finrank ℝ E) → ℝ) := Set.Icc (fun _ => -B) (fun _ => B)
  have hsub : Metric.closedBall (0 : E) B ⊆ e ⁻¹' C := by
    intro x hx
    have hxnorm : ‖x‖ ≤ B := mem_closedBall_zero_iff.mp hx
    have hi : ∀ i, |e x i| ≤ B := by
      intro i
      change |b.repr x i| ≤ B
      rw [← Real.norm_eq_abs]
      exact (PiLp.norm_apply_le (b.repr x) i).trans ((b.repr.norm_map x).le.trans hxnorm)
    exact ⟨fun i => (abs_le.mp (hi i)).1, fun i => (abs_le.mp (hi i)).2⟩
  have hmeas : MeasurableSet C := measurableSet_Icc
  have hfinite : volume C ≠ ⊤ := by
    simp only [C, Real.volume_Icc_pi]
    exact ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top)
  have hvolume : volume.real (e ⁻¹' C) = (2 * B) ^ finrank ℝ E := by
    rw [measureReal_def, he.measure_preimage hmeas.nullMeasurableSet]
    have horder : (fun _ : Fin (finrank ℝ E) => -B) ≤ (fun _ => B) := fun _ => by linarith
    simp only [C, Real.volume_Icc_pi_toReal horder, sub_neg_eq_add, ← two_mul,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← hvolume]
  exact measureReal_mono hsub (by rw [he.measure_preimage hmeas.nullMeasurableSet]; exact hfinite)

end Erdos3

end

end OAI
