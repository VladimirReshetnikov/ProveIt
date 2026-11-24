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
  rw [planarEuclideanEquiv.image_eq_preimage_symm]
  exact ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).trans
    (volume_preserving_finTwoArrow ℝ)).measure_preimage_equiv s

/-- With latitude fixed, the two planar metrics give the same distance. -/
theorem dist_planarEuclideanEquiv_of_snd_eq {a b : ℝ × ℝ} (hy : a.2 = b.2) :
    dist (planarEuclideanEquiv a) (planarEuclideanEquiv b) = dist a b := by
  refine (Complex.orthonormalBasisOneI.repr.isometry.dist_eq ⟨a.1, a.2⟩ ⟨b.1, b.2⟩).trans ?_
  exact (Complex.dist_of_im_eq hy).trans (by simp [Prod.dist_eq, hy])

theorem lipschitzWith_spherePoint : LipschitzWith 2 spherePoint := by
  refine lipschitzWith_of_nnnorm_fderiv_le (fun p => (hasFDerivAt_spherePoint p).differentiableAt) ?_
  intro p
  rw [(hasFDerivAt_spherePoint p).fderiv, ← NNReal.coe_le_coe]
  change ‖sphereDerivative p‖ ≤ 2
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun v => ?_
  have h := orthonormal_sphereFrame p
  rw [sphereDerivative_apply, two_mul]
  refine norm_add_le_of_le ?_ ?_
  · simpa only [norm_smul, show ‖sphereEast p‖ = 1 from h.norm_eq_one 0, mul_one, one_mul]
      using norm_mul_le_of_le (a₁ := Real.cos p.2) (Real.abs_cos_le_one p.2) (norm_fst_le v)
  · simpa [norm_smul, show ‖sphereNorth p‖ = 1 from h.norm_eq_one 1] using norm_snd_le v

end

end GlobeFlattening
