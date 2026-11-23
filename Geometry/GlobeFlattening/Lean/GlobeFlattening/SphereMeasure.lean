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

theorem measurableSet_cutSphere : MeasurableSet cutSphere :=
  (isClosed_eq continuous_norm continuous_const).measurableSet.inter
    (Complex.isOpen_slitPlane.preimage continuous_horizontalComplex).measurableSet

/-- Borel subsets of the longitude rectangle remain Borel in the ambient
space when mapped to the cut sphere. -/
theorem measurableSet_spherePoint_image {s : Set (ℝ × ℝ)} (hs : MeasurableSet s)
    (hsub : s ⊆ sphereLongitudeDomain) : MeasurableSet (spherePoint '' s) :=
  hs.image_of_continuousOn_injOn continuous_spherePoint.continuousOn
    (spherePoint_bijOn.injOn.mono hsub)

/-- Spherical area of subsets of the cut unit sphere, using its longitude chart. -/
def sphericalArea : Measure (EuclideanSpace ℝ (Fin 3)) :=
  Measure.map spherePoint
    ((volume.restrict sphereLongitudeDomain).withDensity
      (fun p => ENNReal.ofReal (Real.cos p.2)))

theorem sphericalArea_spherePoint_image {s : Set (ℝ × ℝ)} (hs : MeasurableSet s)
    (hsub : s ⊆ sphereLongitudeDomain) :
    sphericalArea (spherePoint '' s) = ∫⁻ p in s, ENNReal.ofReal (Real.cos p.2) := by
  have hBorel := measurableSet_spherePoint_image hs hsub
  unfold sphericalArea
  rw [Measure.map_apply continuous_spherePoint.measurable hBorel,
    withDensity_apply _ (hBorel.preimage continuous_spherePoint.measurable),
    Measure.restrict_restrict (hBorel.preimage continuous_spherePoint.measurable),
    spherePoint_bijOn.injOn.preimage_image_inter hsub]

theorem spherePoint_image_domain : spherePoint '' sphereLongitudeDomain = cutSphere :=
  spherePoint_bijOn.image_eq

/-- The spherical exceptional set corresponding to the complement of the
good set in the rectangle. -/
def sphereExceptional (good : Set (ℝ × ℝ)) : Set (EuclideanSpace ℝ (Fin 3)) :=
  cutSphere \ (spherePoint '' good)

theorem measurableSet_sphereExceptional {good : Set (ℝ × ℝ)} (hgood : MeasurableSet good)
    (hsub : good ⊆ sphereLongitudeDomain) : MeasurableSet (sphereExceptional good) :=
  measurableSet_cutSphere.diff (measurableSet_spherePoint_image hgood hsub)

theorem sphereExceptional_eq_image {good : Set (ℝ × ℝ)} (hsub : good ⊆ sphereLongitudeDomain) :
    sphereExceptional good = spherePoint '' (sphereLongitudeDomain \ good) := by
  rw [sphereExceptional, ← spherePoint_image_domain, spherePoint_bijOn.injOn.image_sdiff,
    inter_eq_right.mpr hsub]

theorem measure_sphereExceptional_eq_zero {good : Set (ℝ × ℝ)} (hgood : MeasurableSet good)
    (hsub : good ⊆ sphereLongitudeDomain) (hnull : volume (sphereLongitudeDomain \ good) = 0) :
    sphericalArea (sphereExceptional good) = 0 := by
  rw [sphereExceptional_eq_image hsub, sphericalArea_spherePoint_image
    (isOpen_sphereLongitudeDomain.measurableSet.diff hgood) sdiff_subset,
    Measure.restrict_eq_zero.mpr hnull, lintegral_zero_measure]

end

end GlobeFlattening
