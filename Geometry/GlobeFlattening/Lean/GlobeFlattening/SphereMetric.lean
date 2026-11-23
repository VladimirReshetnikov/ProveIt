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
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  change dist a.1 b.1 ^ 2 + dist a.2 b.2 ^ 2 = dist a b ^ 2
  rw [Prod.dist_eq, hy, dist_self, max_eq_left dist_nonneg]
  simp

theorem norm_sphereDerivative_le (p : ℝ × ℝ) : ‖sphereDerivative p‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  have hx : (Real.cos p.2 * v.1)^2 ≤ ‖v‖ ^ 2 := by
    rw [sq_le_sq, abs_mul, abs_of_nonneg (norm_nonneg _)]
    exact (mul_le_of_le_one_left (abs_nonneg _)
      (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)).trans
      (by simpa [Real.norm_eq_abs] using norm_fst_le v)
  have hy : v.2^2 ≤ ‖v‖ ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg (norm_nonneg _)]
    simpa [Real.norm_eq_abs] using norm_snd_le v
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg _))).mp
  rw [sq_norm_sphereDerivative]
  nlinarith [sq_nonneg ‖v‖]

theorem lipschitzWith_spherePoint : LipschitzWith 2 spherePoint := by
  apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · exact fun p => (hasFDerivAt_spherePoint p).differentiableAt
  · intro p
    rw [(hasFDerivAt_spherePoint p).fderiv]
    exact_mod_cast norm_sphereDerivative_le p

/-- Pulling a Lipschitz estimate back to longitude and latitude changes the
constant by at most a factor of two. -/
theorem lipschitzOnWith_spherePoint_pullback {F : Type*} [PseudoMetricSpace F]
    {f : EuclideanSpace ℝ (Fin 3) → F} {s : Set (EuclideanSpace ℝ (Fin 3))}
    {K : NNReal} (hf : LipschitzOnWith K f s) :
    LipschitzOnWith (K * 2) (f ∘ spherePoint) (spherePoint ⁻¹' s) :=
  hf.comp lipschitzWith_spherePoint.lipschitzOnWith (mapsTo_preimage _ _)

end

end GlobeFlattening
