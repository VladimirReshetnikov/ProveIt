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
  have he : MeasurableEmbedding planarEuclideanEquiv := planarEuclideanEquiv.toHomeomorph.measurableEmbedding
  rw [← measurePreserving_planarEuclideanEquiv.map_eq, he.map_apply, preimage_image_eq s he.injective]

/-- With latitude fixed, the two planar metrics give the same distance. -/
theorem dist_planarEuclideanEquiv_of_snd_eq {a b : ℝ × ℝ} (hy : a.2 = b.2) :
    dist (planarEuclideanEquiv a) (planarEuclideanEquiv b) = dist a b := by
  change dist !₂[a.1, a.2] !₂[b.1, b.2] = dist a b
  simp [PiLp.dist_eq_of_L2, Fin.sum_univ_two, Prod.dist_eq, hy, Real.sqrt_sq dist_nonneg]

theorem norm_sphereDerivative_le (p : ℝ × ℝ) : ‖sphereDerivative p‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun v => ?_
  have hLon : |Real.cos p.2 * v.1| ≤ ‖v‖ := by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)).trans (norm_fst_le v)
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), sq_norm_sphereDerivative]
  nlinarith only [sq_le_sq.2 (hLon.trans (le_abs_self _)),
    sq_le_sq.2 ((norm_snd_le v).trans (le_abs_self _)), sq_nonneg ‖v‖]

theorem lipschitzWith_spherePoint : LipschitzWith 2 spherePoint := by
  rw [← lipschitzOnWith_univ]
  exact convex_univ.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun p _ => (hasFDerivAt_spherePoint p).hasFDerivWithinAt)
    (fun p _ => by exact_mod_cast norm_sphereDerivative_le p)

end

end GlobeFlattening
