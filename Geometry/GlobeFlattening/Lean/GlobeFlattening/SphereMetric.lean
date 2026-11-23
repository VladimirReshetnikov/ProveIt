import GlobeFlattening.SphereFrame
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Comparison of Euclidean and coordinate geometry

The coordinate identification preserves planar area and horizontal
distances. The spherical parametrization is Lipschitz, so a Lipschitz
patch of a spherical map pulls back to a Lipschitz patch in the rectangle.
-/

namespace GlobeFlattening

open MeasureTheory Set

noncomputable section

theorem volume_planarEuclideanEquiv_image (s : Set (ℝ × ℝ)) :
    volume (planarEuclideanEquiv '' s) = volume s := by
  have hmeasure : MeasurePreserving planarEuclideanEquiv volume volume :=
    (PiLp.volume_preserving_toLp (Fin 2)).comp (volume_preserving_finTwoArrow ℝ).symm
  rw [← hmeasure.measure_preimage_emb planarEuclideanEquiv.toHomeomorph.measurableEmbedding,
    preimage_image_eq _ planarEuclideanEquiv.injective]

/-- With latitude fixed, the two planar metrics give the same distance. -/
theorem dist_planarEuclideanEquiv_of_snd_eq {a b : ℝ × ℝ} (hy : a.2 = b.2) :
    dist (planarEuclideanEquiv a) (planarEuclideanEquiv b) = dist a b := by
  change dist !₂[a.1, a.2] !₂[b.1, b.2] = dist a b
  simp [PiLp.dist_eq_of_L2, Fin.sum_univ_two, Prod.dist_eq, hy, Real.sqrt_sq dist_nonneg]

theorem lipschitzWith_spherePoint : LipschitzWith 2 spherePoint := by
  refine lipschitzWith_of_nnnorm_fderiv_le (fun p => (hasFDerivAt_spherePoint p).differentiableAt) ?_
  intro p
  rw [(hasFDerivAt_spherePoint p).fderiv, ← NNReal.coe_le_coe]
  change ‖sphereDerivative p‖ ≤ 2
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun v => ?_
  simp only [sphereDerivative, ContinuousLinearMap.comp_apply, norm_sphereTangentLift]
  change ‖!₂[Real.cos p.2 * v.1, v.2]‖ ≤ _
  simp only [PiLp.norm_eq_of_L2, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Real.norm_eq_abs, abs_mul, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hLon := (mul_le_of_le_one_left (abs_nonneg v.1) (Real.abs_cos_le_one p.2)).trans (norm_fst_le v)
  grw [hLon, show |v.2| ≤ ‖v‖ from norm_snd_le v]
  nlinarith only [sq_nonneg ‖v‖]

end

end GlobeFlattening
