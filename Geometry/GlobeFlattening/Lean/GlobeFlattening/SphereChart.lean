import GlobeFlattening.CoordinateRectangles
import GlobeFlattening.SphereFrame
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

/-- The projection to the equatorial plane, identified with the complex plane. -/
def horizontalComplex (w : EuclideanSpace ℝ (Fin 3)) : ℂ := ⟨w 0, w 1⟩

@[simp] theorem horizontalComplex_re (w : EuclideanSpace ℝ (Fin 3)) :
    (horizontalComplex w).re = w 0 := rfl

@[simp] theorem horizontalComplex_im (w : EuclideanSpace ℝ (Fin 3)) :
    (horizontalComplex w).im = w 1 := rfl

theorem continuous_horizontalComplex : Continuous horizontalComplex := by
  exact Complex.equivRealProdCLM.symm.continuous.comp
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).continuous.prodMk
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).continuous)

theorem horizontalComplex_spherePoint (p : ℝ × ℝ) :
    horizontalComplex (spherePoint p) =
      (Real.cos p.2 : ℂ) * (Complex.cos p.1 + Complex.sin p.1 * Complex.I) := by
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  apply Complex.ext <;>
    simp [spherePoint, Complex.mul_re, Complex.mul_im, -Complex.ofReal_cos, -Complex.ofReal_sin]

/-- The unit sphere minus the negative-real equatorial ray's meridian,
including both poles in the removed meridian. -/
def cutSphere : Set (EuclideanSpace ℝ (Fin 3)) :=
  {w | ‖w‖ = 1 ∧ horizontalComplex w ∈ Complex.slitPlane}

theorem cutSphere_eq_sphere_sdiff_meridian :
    cutSphere = Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 \
      {w | w 1 = 0 ∧ w 0 ≤ 0} := by
  ext w
  simp only [cutSphere, mem_setOf_eq, mem_sdiff, Metric.mem_sphere, dist_zero_right,
    Complex.mem_slitPlane_iff, horizontalComplex_re, horizontalComplex_im, not_and_or, not_le]
  rw [or_comm]

private theorem longitude_spherePoint {p : ℝ × ℝ} (hp : p ∈ sphereLongitudeDomain) :
    (horizontalComplex (spherePoint p)).arg = p.1 := by
  rw [horizontalComplex_spherePoint, Complex.arg_mul_cos_add_sin_mul_I
    (Real.cos_pos_of_mem_Ioo hp.2) ⟨hp.1.1, hp.1.2.le⟩]

theorem spherePoint_mapsTo : MapsTo spherePoint sphereLongitudeDomain cutSphere := by
  intro p hp
  have hcos := Real.cos_pos_of_mem_Ioo hp.2
  refine ⟨norm_spherePoint p, Complex.mem_slitPlane_iff_arg.2 ⟨?_, norm_ne_zero_iff.1 ?_⟩⟩
  · rw [longitude_spherePoint hp]
    exact hp.1.2.ne
  · rw [horizontalComplex_spherePoint, norm_mul, Complex.norm_cos_add_sin_mul_I,
      Complex.norm_of_nonneg hcos.le, mul_one]
    exact hcos.ne'

/-- Longitude and latitude computed directly from an ambient point. -/
def sphereChartInverse (w : EuclideanSpace ℝ (Fin 3)) : ℝ × ℝ :=
  ((horizontalComplex w).arg, Real.arcsin (w 2))

theorem sphereChartInverse_spherePoint {p : ℝ × ℝ} (hp : p ∈ sphereLongitudeDomain) :
    sphereChartInverse (spherePoint p) = p := by
  exact Prod.ext (longitude_spherePoint hp) (Real.arcsin_sin hp.2.1.le hp.2.2.le)

private theorem cutSphere_horizontal_norm_sq {w : EuclideanSpace ℝ (Fin 3)}
    (hw : w ∈ cutSphere) : ‖horizontalComplex w‖ ^ 2 = 1 - (w 2)^2 := by
  apply eq_sub_iff_add_eq.mpr
  calc
    _ = ‖w‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
      simp only [horizontalComplex_re, horizontalComplex_im, pow_two]
    _ = 1 := by simp [hw.1]

theorem cutSphere_vertical_bounds {w : EuclideanSpace ℝ (Fin 3)} (hw : w ∈ cutSphere) :
    w 2 ∈ Ioo (-1 : ℝ) 1 := by
  have hrad := sq_pos_of_pos (norm_pos_iff.mpr (Complex.slitPlane_ne_zero hw.2))
  rw [cutSphere_horizontal_norm_sq hw] at hrad
  have hlt : (w 2)^2 < (1 : ℝ)^2 := by simpa using sub_pos.mp hrad
  exact abs_lt.mp (by simpa using sq_lt_sq.mp hlt)

theorem sphereChartInverse_mapsTo : MapsTo sphereChartInverse cutSphere sphereLongitudeDomain := by
  intro w hw
  have hz := cutSphere_vertical_bounds hw
  exact ⟨⟨Complex.neg_pi_lt_arg _, lt_of_le_of_ne (Complex.arg_le_pi _)
    (Complex.slitPlane_arg_ne_pi hw.2)⟩,
    ⟨Real.neg_pi_div_two_lt_arcsin.mpr hz.1, Real.arcsin_lt_pi_div_two.mpr hz.2⟩⟩

theorem spherePoint_sphereChartInverse {w : EuclideanSpace ℝ (Fin 3)} (hw : w ∈ cutSphere) :
    spherePoint (sphereChartInverse w) = w := by
  have hz := cutSphere_vertical_bounds hw
  have hrad : Real.cos (Real.arcsin (w 2)) = ‖horizontalComplex w‖ := by
    rw [Real.cos_arcsin, ← cutSphere_horizontal_norm_sq hw, Real.sqrt_sq (norm_nonneg _)]
  have hh : horizontalComplex (spherePoint (sphereChartInverse w)) = horizontalComplex w := by
    rw [horizontalComplex_spherePoint]
    simpa only [sphereChartInverse, hrad] using
      Complex.norm_mul_cos_add_sin_mul_I (horizontalComplex w)
  ext i
  fin_cases i
  · exact congrArg Complex.re hh
  · exact congrArg Complex.im hh
  · exact Real.sin_arcsin hz.1.le hz.2.le

theorem spherePoint_bijOn : BijOn spherePoint sphereLongitudeDomain cutSphere :=
  ⟨spherePoint_mapsTo,
    (show LeftInvOn sphereChartInverse spherePoint sphereLongitudeDomain from
      fun _ hp => sphereChartInverse_spherePoint hp).injOn,
    (show RightInvOn sphereChartInverse spherePoint cutSphere from
      fun _ hw => spherePoint_sphereChartInverse hw).surjOn sphereChartInverse_mapsTo⟩

/-- The coordinates of the report give a homeomorphism onto the cut sphere. -/
def sphereLongitudeChart : sphereLongitudeDomain ≃ₜ cutSphere where
  toFun p := ⟨spherePoint p, spherePoint_mapsTo p.2⟩
  invFun w := ⟨sphereChartInverse w, sphereChartInverse_mapsTo w.2⟩
  left_inv p := Subtype.ext (sphereChartInverse_spherePoint p.2)
  right_inv w := Subtype.ext (spherePoint_sphereChartInverse w.2)
  continuous_toFun := (continuous_spherePoint.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    change Continuous (cutSphere.restrict sphereChartInverse)
    apply continuousOn_iff_continuous_restrict.1
    exact (Complex.continuousOn_arg.comp continuous_horizontalComplex.continuousOn
      (fun _ hw => hw.2)).prodMk
      (Real.continuous_arcsin.comp (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous).continuousOn

end

end GlobeFlattening
