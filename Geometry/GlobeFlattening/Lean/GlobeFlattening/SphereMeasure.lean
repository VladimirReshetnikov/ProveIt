import GlobeFlattening.SphereChart
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Surface area on the cut sphere

In the longitude chart the spherical area element is
`cos latitude` times planar Lebesgue area. The measure is pushed forward
along the parametrization to Borel sets of the ambient Euclidean space.
-/

namespace GlobeFlattening

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Borel subsets of the longitude rectangle remain Borel in the ambient
space when mapped to the cut sphere. -/
theorem measurableSet_spherePoint_image {s : Set (ℝ × ℝ)} (hs : MeasurableSet s)
    (hsub : s ⊆ sphereLongitudeDomain) : MeasurableSet (spherePoint '' s) :=
  hs.image_of_continuousOn_injOn continuous_spherePoint.continuousOn
    (spherePoint_bijOn.injOn.mono hsub)

theorem measurableSet_cutSphere : MeasurableSet cutSphere :=
  spherePoint_bijOn.image_eq ▸
    measurableSet_spherePoint_image isOpen_sphereLongitudeDomain.measurableSet Subset.rfl

/-- Spherical area of subsets of the cut unit sphere, using its longitude chart. -/
def sphericalArea : Measure (EuclideanSpace ℝ (Fin 3)) :=
  Measure.map spherePoint
    ((volume.restrict sphereLongitudeDomain).withDensity
      (fun p => ENNReal.ofReal (Real.cos p.2)))

theorem sphericalArea_spherePoint_image {s : Set (ℝ × ℝ)} (hs : MeasurableSet s)
    (hsub : s ⊆ sphereLongitudeDomain) :
    sphericalArea (spherePoint '' s) = ∫⁻ p in s, ENNReal.ofReal (Real.cos p.2) := by
  rw [sphericalArea, Measure.map_apply continuous_spherePoint.measurable
    (measurableSet_spherePoint_image hs hsub), withDensity_apply',
    Measure.restrict_restrict' isOpen_sphereLongitudeDomain.measurableSet,
    spherePoint_bijOn.injOn.preimage_image_inter hsub]

/-- The spherical exceptional set corresponding to the complement of the
good set in the rectangle. -/
def sphereExceptional (good : Set (ℝ × ℝ)) : Set (EuclideanSpace ℝ (Fin 3)) :=
  cutSphere \ (spherePoint '' good)

theorem sphereExceptional_eq_image {good : Set (ℝ × ℝ)} (hsub : good ⊆ sphereLongitudeDomain) :
    sphereExceptional good = spherePoint '' (sphereLongitudeDomain \ good) := by
  rw [sphereExceptional, ← spherePoint_bijOn.image_eq, spherePoint_bijOn.injOn.image_sdiff_subset hsub]

/-- The exceptional set is Borel and has spherical area zero. -/
theorem sphereExceptional_measurable_null {good : Set (ℝ × ℝ)} (hgood : MeasurableSet good)
    (hsub : good ⊆ sphereLongitudeDomain) (hnull : volume (sphereLongitudeDomain \ good) = 0) :
    MeasurableSet (sphereExceptional good) ∧ sphericalArea (sphereExceptional good) = 0 := by
  rw [sphereExceptional_eq_image hsub]
  have hdiff := isOpen_sphereLongitudeDomain.measurableSet.diff hgood
  refine ⟨measurableSet_spherePoint_image hdiff sdiff_subset, ?_⟩
  rw [sphericalArea_spherePoint_image hdiff sdiff_subset,
    Measure.restrict_eq_zero.mpr hnull, lintegral_zero_measure]

end

end GlobeFlattening
