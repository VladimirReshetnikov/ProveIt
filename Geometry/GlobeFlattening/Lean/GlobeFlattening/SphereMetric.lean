import GlobeFlattening.SphereDifferential
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

/-- The coordinate identification preserves the usual Lebesgue measures. -/
theorem measurePreserving_planarEuclideanEquiv :
    MeasurePreserving planarEuclideanEquiv volume volume := by
  exact (PiLp.volume_preserving_toLp (Fin 2)).comp (volume_preserving_finTwoArrow ℝ).symm

theorem volume_planarEuclideanEquiv_image (s : Set (ℝ × ℝ)) :
    volume (planarEuclideanEquiv '' s) = volume s := by
  simpa only [preimage_image_eq s planarEuclideanEquiv.injective] using
    (measurePreserving_planarEuclideanEquiv.measure_preimage_emb
      planarEuclideanEquiv.toHomeomorph.measurableEmbedding (planarEuclideanEquiv '' s)).symm

/-- With latitude fixed, the two planar metrics give the same distance. -/
theorem dist_planarEuclideanEquiv_of_snd_eq {a b : ℝ × ℝ} (hy : a.2 = b.2) :
    dist (planarEuclideanEquiv a) (planarEuclideanEquiv b) = dist a b := by
  rw [PiLp.dist_eq_of_L2, Fin.sum_univ_two, Prod.dist_eq]
  change Real.sqrt (dist a.1 b.1 ^ 2 + dist a.2 b.2 ^ 2) = _
  simp [hy, Real.sqrt_sq dist_nonneg]

theorem norm_sphereDerivative_le (p : ℝ × ℝ) : ‖sphereDerivative p‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun v => ?_
  have hLon : |Real.cos p.2 * v.1| ≤ ‖v‖ := by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)).trans (norm_fst_le v)
  have hLat : |v.2| ≤ ‖v‖ := norm_snd_le v
  rw [← abs_of_nonneg (norm_nonneg v)] at hLon hLat
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), sq_norm_sphereDerivative]
  nlinarith [sq_le_sq.2 hLon, sq_le_sq.2 hLat]

theorem lipschitzWith_spherePoint : LipschitzWith 2 spherePoint := by
  apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · exact fun p => (hasFDerivAt_spherePoint p).differentiableAt
  · intro p
    rw [(hasFDerivAt_spherePoint p).fderiv]
    exact_mod_cast norm_sphereDerivative_le p

end

end GlobeFlattening
