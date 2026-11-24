import GlobeFlattening.CoordinateRectangles
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# The longitude chart on the cut unit sphere

Longitude is the argument of the horizontal projection and latitude is
the arcsine of the vertical coordinate.
-/

namespace GlobeFlattening

open Set
open scoped Real

noncomputable section

/-- The spherical parametrization at a longitude-latitude pair. -/
def spherePoint (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[Real.cos p.2 * Real.cos p.1, Real.cos p.2 * Real.sin p.1, Real.sin p.2]

theorem continuous_spherePoint : Continuous spherePoint := by
  fun_prop [spherePoint]

/-- The projection to the equatorial plane, identified with the complex plane. -/
def horizontalComplex (w : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  Complex.equivRealProdCLM.symm (w 0, w 1)

@[simp] theorem horizontalComplex_re (w : EuclideanSpace ℝ (Fin 3)) :
    (horizontalComplex w).re = w 0 := rfl

@[simp] theorem horizontalComplex_im (w : EuclideanSpace ℝ (Fin 3)) :
    (horizontalComplex w).im = w 1 := rfl

private theorem norm_sq_eq_horizontal (w : EuclideanSpace ℝ (Fin 3)) :
    ‖w‖ ^ 2 = ‖horizontalComplex w‖ ^ 2 + (w 2)^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Complex.sq_norm,
    Complex.normSq_apply, horizontalComplex_re, horizontalComplex_im, ← pow_two]

@[simp] theorem norm_spherePoint (p : ℝ × ℝ) : ‖spherePoint p‖ = 1 := by
  rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, norm_sq_eq_horizontal]
  change ‖Complex.polarCoord.symm (Real.cos p.2, p.1)‖ ^ 2 + Real.sin p.2 ^ 2 = 1
  simp only [Complex.norm_polarCoord_symm, sq_abs, Real.cos_sq_add_sin_sq]

/-- The unit sphere minus the negative-real equatorial ray's meridian,
including both poles in the removed meridian. -/
def cutSphere : Set (EuclideanSpace ℝ (Fin 3)) :=
  {w | ‖w‖ = 1 ∧ horizontalComplex w ∈ Complex.slitPlane}

theorem cutSphere_eq_sphere_sdiff_meridian :
    cutSphere = Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 \
      {w | w 1 = 0 ∧ w 0 ≤ 0} := by
  ext w
  simp only [cutSphere, mem_setOf_eq, mem_sdiff, Metric.mem_sphere, dist_zero_right,
    Complex.mem_slitPlane_iff, horizontalComplex_re, horizontalComplex_im, not_and_or, not_le, or_comm]

private theorem spherePoint_polar_target {p : ℝ × ℝ} (hp : p ∈ sphereLongitudeDomain) :
    (Real.cos p.2, p.1) ∈ Complex.polarCoord.target :=
  ⟨Real.cos_pos_of_mem_Ioo hp.2, hp.1⟩

theorem spherePoint_mapsTo : MapsTo spherePoint sphereLongitudeDomain cutSphere :=
  fun p hp => ⟨norm_spherePoint p, Complex.polarCoord.map_target (spherePoint_polar_target hp)⟩

/-- Longitude and latitude computed directly from an ambient point. -/
def sphereChartInverse (w : EuclideanSpace ℝ (Fin 3)) : ℝ × ℝ :=
  ((horizontalComplex w).arg, Real.arcsin (w 2))

theorem sphereChartInverse_spherePoint {p : ℝ × ℝ} (hp : p ∈ sphereLongitudeDomain) :
    sphereChartInverse (spherePoint p) = p :=
  Prod.ext (congrArg Prod.snd (Complex.polarCoord.right_inv (spherePoint_polar_target hp)))
    (Real.sinPartialHomeomorph.left_inv hp.2)

private theorem cutSphere_horizontal_norm_sq {w : EuclideanSpace ℝ (Fin 3)}
    (hw : w ∈ cutSphere) : ‖horizontalComplex w‖ ^ 2 = 1 - (w 2)^2 := by
  rw [eq_sub_iff_add_eq, ← norm_sq_eq_horizontal, hw.1, one_pow]

theorem cutSphere_vertical_bounds {w : EuclideanSpace ℝ (Fin 3)} (hw : w ∈ cutSphere) :
    w 2 ∈ Ioo (-1 : ℝ) 1 := by
  rw [mem_Ioo, ← abs_lt, ← sq_lt_one_iff_abs_lt_one, ← sub_pos, ← cutSphere_horizontal_norm_sq hw]
  exact sq_pos_of_pos (norm_pos_iff.mpr (Complex.slitPlane_ne_zero hw.2))

theorem sphereChartInverse_mapsTo : MapsTo sphereChartInverse cutSphere sphereLongitudeDomain :=
  fun _ hw => ⟨(Complex.polarCoord.map_source hw.2).2,
    Real.sinPartialHomeomorph.map_target (cutSphere_vertical_bounds hw)⟩

theorem spherePoint_sphereChartInverse {w : EuclideanSpace ℝ (Fin 3)} (hw : w ∈ cutSphere) :
    spherePoint (sphereChartInverse w) = w := by
  have hxy : horizontalComplex (spherePoint (sphereChartInverse w)) = horizontalComplex w := by
    change Complex.polarCoord.symm (Real.cos (Real.arcsin (w 2)), (horizontalComplex w).arg) = _
    rw [Real.cos_arcsin, ← cutSphere_horizontal_norm_sq hw, Real.sqrt_sq (norm_nonneg _),
      ← Complex.polarCoord_apply, Complex.polarCoord.left_inv hw.2]
  apply PiLp.ext
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
  exact ⟨congrArg Complex.re hxy, congrArg Complex.im hxy,
    Real.sinPartialHomeomorph.right_inv (cutSphere_vertical_bounds hw)⟩

private def sphereLongitudeEquiv : PartialEquiv (ℝ × ℝ) (EuclideanSpace ℝ (Fin 3)) :=
  ⟨spherePoint, sphereChartInverse, sphereLongitudeDomain, cutSphere,
    spherePoint_mapsTo, sphereChartInverse_mapsTo,
    (fun _ => sphereChartInverse_spherePoint), (fun _ => spherePoint_sphereChartInverse)⟩

theorem spherePoint_bijOn : BijOn spherePoint sphereLongitudeDomain cutSphere :=
  sphereLongitudeEquiv.bijOn

/-- The coordinates of the report give a homeomorphism onto the cut sphere. -/
def sphereLongitudeChart : sphereLongitudeDomain ≃ₜ cutSphere where
  toEquiv := sphereLongitudeEquiv.toEquiv
  continuous_toFun := (continuous_spherePoint.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((Complex.continuousOn_arg.comp (f := horizontalComplex) (by fun_prop [horizontalComplex])
      (fun _ hw => hw.2)).prodMk
      (by fun_prop : ContinuousOn (fun w => Real.arcsin (w 2)) cutSphere)).restrict.subtype_mk _

end

end GlobeFlattening
