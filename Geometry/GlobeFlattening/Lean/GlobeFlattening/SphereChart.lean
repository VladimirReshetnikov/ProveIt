import GlobeFlattening.CoordinateRectangles
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

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

@[simp] theorem norm_spherePoint (p : ℝ × ℝ) : ‖spherePoint p‖ = 1 := by
  have hLon := Real.sin_sq_add_cos_sq p.1
  have hLat := Real.sin_sq_add_cos_sq p.2
  simp [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_three, spherePoint, mul_pow]
  grind only

theorem continuous_spherePoint : Continuous spherePoint := by
  fun_prop [spherePoint]

/-- The projection to the equatorial plane, identified with the complex plane. -/
def horizontalComplex (w : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  Complex.equivRealProdCLM.symm (w 0, w 1)

@[simp] theorem horizontalComplex_re (w : EuclideanSpace ℝ (Fin 3)) :
    (horizontalComplex w).re = w 0 := rfl

@[simp] theorem horizontalComplex_im (w : EuclideanSpace ℝ (Fin 3)) :
    (horizontalComplex w).im = w 1 := rfl

theorem horizontalComplex_spherePoint (p : ℝ × ℝ) :
    horizontalComplex (spherePoint p) =
      (Real.cos p.2 : ℂ) * (Complex.cos p.1 + Complex.sin p.1 * Complex.I) := by
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, horizontalComplex, spherePoint,
    Complex.equivRealProdCLM_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.ofReal_mul, mul_add, mul_assoc]

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

private theorem polar_spherePoint {p : ℝ × ℝ} (hp : p ∈ sphereLongitudeDomain) :
    0 < ‖horizontalComplex (spherePoint p)‖ ∧
      (horizontalComplex (spherePoint p)).arg = p.1 := by
  have hcos := Real.cos_pos_of_mem_Ioo hp.2
  simpa only [horizontalComplex_spherePoint, Complex.arg_mul_cos_add_sin_mul_I hcos
    ⟨hp.1.1, hp.1.2.le⟩, norm_mul, Complex.norm_cos_add_sin_mul_I,
    Complex.norm_of_nonneg hcos.le, mul_one, and_true] using hcos

theorem spherePoint_mapsTo : MapsTo spherePoint sphereLongitudeDomain cutSphere := by
  intro p hp
  obtain ⟨hrad, harg⟩ := polar_spherePoint hp
  exact ⟨norm_spherePoint p, Complex.mem_slitPlane_iff_arg.2
    ⟨harg ▸ hp.1.2.ne, norm_ne_zero_iff.1 hrad.ne'⟩⟩

/-- Longitude and latitude computed directly from an ambient point. -/
def sphereChartInverse (w : EuclideanSpace ℝ (Fin 3)) : ℝ × ℝ :=
  ((horizontalComplex w).arg, Real.arcsin (w 2))

theorem sphereChartInverse_spherePoint {p : ℝ × ℝ} (hp : p ∈ sphereLongitudeDomain) :
    sphereChartInverse (spherePoint p) = p :=
  Prod.ext (polar_spherePoint hp).2 (Real.sinPartialHomeomorph.left_inv hp.2)

private theorem cutSphere_horizontal_norm_sq {w : EuclideanSpace ℝ (Fin 3)}
    (hw : w ∈ cutSphere) : ‖horizontalComplex w‖ ^ 2 = 1 - (w 2)^2 := by
  apply eq_sub_of_add_eq
  simpa only [Complex.sq_norm, Complex.normSq_apply, horizontalComplex_re, horizontalComplex_im,
    ← pow_two, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, one_pow] using
    congrArg (· ^ (2 : ℕ)) hw.1

theorem cutSphere_vertical_bounds {w : EuclideanSpace ℝ (Fin 3)} (hw : w ∈ cutSphere) :
    w 2 ∈ Ioo (-1 : ℝ) 1 := by
  apply abs_lt.mp
  rw [← abs_one, ← sq_lt_sq, one_pow, ← sub_pos, ← cutSphere_horizontal_norm_sq hw]
  exact sq_pos_of_pos (norm_pos_iff.mpr (Complex.slitPlane_ne_zero hw.2))

theorem sphereChartInverse_mapsTo : MapsTo sphereChartInverse cutSphere sphereLongitudeDomain := by
  intro w hw
  exact ⟨⟨Complex.neg_pi_lt_arg _, (Complex.arg_le_pi _).lt_of_ne (Complex.slitPlane_arg_ne_pi hw.2)⟩,
    Real.sinPartialHomeomorph.map_target (cutSphere_vertical_bounds hw)⟩

theorem spherePoint_sphereChartInverse {w : EuclideanSpace ℝ (Fin 3)} (hw : w ∈ cutSphere) :
    spherePoint (sphereChartInverse w) = w := by
  have hr : Real.cos (Real.arcsin (w 2)) = ‖horizontalComplex w‖ := by
    rw [Real.cos_arcsin, ← cutSphere_horizontal_norm_sq hw, Real.sqrt_sq (norm_nonneg _)]
  apply PiLp.ext
  simpa [Fin.forall_fin_succ, spherePoint, sphereChartInverse, hr] using
    And.intro (Complex.norm_mul_cos_arg (horizontalComplex w))
      (And.intro (Complex.norm_mul_sin_arg (horizontalComplex w))
        (Real.sinPartialHomeomorph.right_inv (cutSphere_vertical_bounds hw)))

theorem spherePoint_bijOn : BijOn spherePoint sphereLongitudeDomain cutSphere :=
  (show InvOn sphereChartInverse spherePoint sphereLongitudeDomain cutSphere from
    ⟨fun _ => sphereChartInverse_spherePoint, fun _ => spherePoint_sphereChartInverse⟩).bijOn
    spherePoint_mapsTo sphereChartInverse_mapsTo

/-- The coordinates of the report give a homeomorphism onto the cut sphere. -/
def sphereLongitudeChart : sphereLongitudeDomain ≃ₜ cutSphere where
  toFun p := ⟨spherePoint p, spherePoint_mapsTo p.2⟩
  invFun w := ⟨sphereChartInverse w, sphereChartInverse_mapsTo w.2⟩
  left_inv p := Subtype.ext (sphereChartInverse_spherePoint p.2)
  right_inv w := Subtype.ext (spherePoint_sphereChartInverse w.2)
  continuous_toFun := (continuous_spherePoint.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((Complex.continuousOn_arg.comp (f := horizontalComplex) (by fun_prop [horizontalComplex])
      (fun _ hw => hw.2)).prodMk
      (by fun_prop : ContinuousOn (fun w => Real.arcsin (w 2)) cutSphere)).restrict.subtype_mk _

end

end GlobeFlattening
