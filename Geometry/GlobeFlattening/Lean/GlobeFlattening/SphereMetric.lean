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
  have he : MeasurableEmbedding planarEuclideanEquiv := planarEuclideanEquiv.toHomeomorph.measurableEmbedding
  rw [← hmeasure.map_eq, he.map_apply, preimage_image_eq s he.injective]

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
  rw [sphereDerivative_apply]
  refine (norm_add_le _ _).trans ?_
  have hframe := orthonormal_sphereFrame p
  have heast : ‖sphereEast p‖ = 1 := hframe.norm_eq_one (0 : Fin 3)
  have hnorth : ‖sphereNorth p‖ = 1 := hframe.norm_eq_one (1 : Fin 3)
  simp only [norm_smul, heast, hnorth, mul_one, Real.norm_eq_abs, abs_mul]
  have hLon := (mul_le_of_le_one_left (abs_nonneg v.1) (Real.abs_cos_le_one p.2)).trans (norm_fst_le v)
  rw [two_mul]
  exact add_le_add hLon (norm_snd_le v)

end

end GlobeFlattening
