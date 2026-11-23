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

theorem continuous_spherePoint : Continuous spherePoint :=
  continuous_iff_continuousAt.2 fun p => (hasFDerivAt_spherePoint p).continuousAt

/-- Borel subsets of the longitude rectangle remain Borel in the ambient
space when mapped to the cut sphere. -/
theorem measurableSet_spherePoint_image {s : Set (ℝ × ℝ)} (hs : MeasurableSet s)
    (hsub : s ⊆ sphereLongitudeDomain) : MeasurableSet (spherePoint '' s) := by
  let inverseOn : cutSphere → ℝ × ℝ := fun w => sphereChartInverse w
  have hinv : Measurable inverseOn :=
    (continuousOn_iff_continuous_restrict.1 continuousOn_sphereChartInverse).measurable
  let t := inverseOn ⁻¹' s
  have ht : MeasurableSet t := hs.preimage hinv
  have heq : Subtype.val '' t = spherePoint '' s := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨inverseOn z, hz, spherePoint_sphereChartInverse z.2⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨spherePoint z, spherePoint_mapsTo (hsub hz)⟩,
        by simpa [t, inverseOn, sphereChartInverse_spherePoint (hsub hz)] using hz, rfl⟩
  rw [← heq]
  exact (MeasurableEmbedding.subtype_coe measurableSet_cutSphere).measurableSet_image.mpr ht

/-- Spherical area of subsets of the cut unit sphere, using its longitude chart. -/
def sphericalArea : Measure (EuclideanSpace ℝ (Fin 3)) :=
  Measure.map spherePoint
    ((volume.restrict sphereLongitudeDomain).withDensity
      (fun p => ENNReal.ofReal (Real.cos p.2)))

theorem sphericalArea_spherePoint_image {s : Set (ℝ × ℝ)} (hs : MeasurableSet s)
    (hsub : s ⊆ sphereLongitudeDomain) :
    sphericalArea (spherePoint '' s) = ∫⁻ p in s, ENNReal.ofReal (Real.cos p.2) := by
  have hBorel := measurableSet_spherePoint_image hs hsub
  have hinj : InjOn spherePoint sphereLongitudeDomain := by
    intro x hx y hy h
    simpa [sphereChartInverse_spherePoint hx, sphereChartInverse_spherePoint hy] using
      congrArg sphereChartInverse h
  have hpull : spherePoint ⁻¹' (spherePoint '' s) ∩ sphereLongitudeDomain = s := by
    ext p
    constructor
    · rintro ⟨⟨x, hx, he⟩, hp⟩
      rwa [← hinj (hsub hx) hp he]
    · intro hp
      exact ⟨mem_image_of_mem spherePoint hp, hsub hp⟩
  unfold sphericalArea
  rw [Measure.map_apply continuous_spherePoint.measurable hBorel,
    withDensity_apply _ (hBorel.preimage continuous_spherePoint.measurable),
    Measure.restrict_restrict (hBorel.preimage continuous_spherePoint.measurable), hpull]

theorem spherePoint_image_domain : spherePoint '' sphereLongitudeDomain = cutSphere := by
  ext w
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact spherePoint_mapsTo hp
  · intro hw
    exact ⟨sphereChartInverse w, sphereChartInverse_mapsTo hw, spherePoint_sphereChartInverse hw⟩

/-- The spherical exceptional set corresponding to the complement of the
good set in the rectangle. -/
def sphereExceptional (good : Set (ℝ × ℝ)) : Set (EuclideanSpace ℝ (Fin 3)) :=
  cutSphere \ (spherePoint '' good)

theorem measurableSet_sphereExceptional {good : Set (ℝ × ℝ)} (hgood : MeasurableSet good)
    (hsub : good ⊆ sphereLongitudeDomain) : MeasurableSet (sphereExceptional good) :=
  measurableSet_cutSphere.diff (measurableSet_spherePoint_image hgood hsub)

theorem sphereExceptional_eq_image {good : Set (ℝ × ℝ)} (hsub : good ⊆ sphereLongitudeDomain) :
    sphereExceptional good = spherePoint '' (sphereLongitudeDomain \ good) := by
  ext w
  constructor
  · intro hw
    have hw' : w ∈ cutSphere := hw.1
    refine ⟨sphereChartInverse w, ⟨sphereChartInverse_mapsTo hw', ?_⟩,
      spherePoint_sphereChartInverse hw'⟩
    intro hg
    exact hw.2 ⟨sphereChartInverse w, hg, spherePoint_sphereChartInverse hw'⟩
  · rintro ⟨p, ⟨hp, hpg⟩, rfl⟩
    refine ⟨spherePoint_mapsTo hp, ?_⟩
    rintro ⟨q, hq, he⟩
    have hpq : q = p := by
      simpa [sphereChartInverse_spherePoint (hsub hq), sphereChartInverse_spherePoint hp]
        using congrArg sphereChartInverse he
    exact hpg (hpq ▸ hq)

theorem measure_sphereExceptional_eq_zero {good : Set (ℝ × ℝ)} (hgood : MeasurableSet good)
    (hsub : good ⊆ sphereLongitudeDomain) (hnull : volume (sphereLongitudeDomain \ good) = 0) :
    sphericalArea (sphereExceptional good) = 0 := by
  rw [sphereExceptional_eq_image hsub, sphericalArea_spherePoint_image
    (isOpen_sphereLongitudeDomain.measurableSet.diff hgood) sdiff_subset,
    Measure.restrict_eq_zero.mpr hnull, lintegral_zero_measure]

end

end GlobeFlattening
