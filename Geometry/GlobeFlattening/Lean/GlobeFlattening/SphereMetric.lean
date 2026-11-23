import GlobeFlattening.SphereDifferential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.Prod
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
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  change dist a.1 b.1 ^ 2 + dist a.2 b.2 ^ 2 = dist a b ^ 2
  rw [Prod.dist_eq, hy, dist_self, max_eq_left dist_nonneg]
  simp

theorem norm_sphereDerivative_le (p : ℝ × ℝ) : ‖sphereDerivative p‖ ≤ 2 := by
  have he : ‖sphereEast p‖ = 1 := (orthonormal_sphereFrame p).norm_eq_one (0 : Fin 3)
  have hn : ‖sphereNorth p‖ = 1 := (orthonormal_sphereFrame p).norm_eq_one (1 : Fin 3)
  rw [sphereDerivative, ← (one_add_one_eq_two : (1 : ℝ) + 1 = 2)]
  refine (norm_add_le _ _).trans ?_
  simp only [ContinuousLinearMap.norm_smulRight_apply, norm_smul, he, hn,
    ContinuousLinearMap.norm_fst, ContinuousLinearMap.norm_snd, mul_one, Real.norm_eq_abs]
  exact add_le_add (Real.abs_cos_le_one _) le_rfl

theorem lipschitzWith_spherePoint : LipschitzWith 2 spherePoint := by
  apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · exact fun p => (hasFDerivAt_spherePoint p).differentiableAt
  · intro p
    rw [(hasFDerivAt_spherePoint p).fderiv]
    exact_mod_cast norm_sphereDerivative_le p

end

end GlobeFlattening
