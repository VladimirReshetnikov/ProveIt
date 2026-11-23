import GlobeFlattening.SphereFrame
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic.Linarith

/-!
# The longitude chart on the cut unit sphere

Longitude is the argument of the horizontal projection and latitude is
the arcsine of the vertical coordinate.
-/

namespace GlobeFlattening

open Set
open scoped Real

noncomputable section

/-- The closed rectangle of longitude-latitude parameters from the report. -/
def sphereClosedBox : Set (ℝ × ℝ) :=
  Icc (-Real.pi) Real.pi ×ˢ Icc (-(Real.pi / 2)) (Real.pi / 2)

/-- The open rectangle of longitude-latitude parameters from the report. -/
def sphereLongitudeDomain : Set (ℝ × ℝ) :=
  Ioo (-Real.pi) Real.pi ×ˢ Ioo (-(Real.pi / 2)) (Real.pi / 2)

theorem isOpen_sphereLongitudeDomain : IsOpen sphereLongitudeDomain :=
  isOpen_Ioo.prod isOpen_Ioo

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

theorem horizontalComplex_norm_sq (w : EuclideanSpace ℝ (Fin 3)) :
    ‖horizontalComplex w‖ ^ 2 = (w 0)^2 + (w 1)^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [horizontalComplex_re, horizontalComplex_im, pow_two]

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

private theorem cutSphere_sq_identity {w : EuclideanSpace ℝ (Fin 3)} (hw : w ∈ cutSphere) :
    ‖horizontalComplex w‖ ^ 2 + (w 2)^2 = 1 := by
  have hn := EuclideanSpace.real_norm_sq_eq w
  have hr : ‖w‖ = 1 := hw.1
  rw [hr, one_pow, Fin.sum_univ_three] at hn
  rw [horizontalComplex_norm_sq]
  exact hn.symm

theorem cutSphere_vertical_bounds {w : EuclideanSpace ℝ (Fin 3)} (hw : w ∈ cutSphere) :
    w 2 ∈ Ioo (-1 : ℝ) 1 := by
  have hrad : 0 < ‖horizontalComplex w‖ :=
    norm_pos_iff.mpr (Complex.slitPlane_ne_zero hw.2)
  have hlt : (w 2)^2 < (1 : ℝ)^2 := by
    nlinarith [cutSphere_sq_identity hw, sq_pos_of_pos hrad]
  simpa using abs_lt.mp (by simpa using sq_lt_sq.mp hlt : |w 2| < (1 : ℝ))

theorem sphereChartInverse_mapsTo : MapsTo sphereChartInverse cutSphere sphereLongitudeDomain := by
  intro w hw
  have hz := cutSphere_vertical_bounds hw
  exact ⟨⟨Complex.neg_pi_lt_arg _, lt_of_le_of_ne (Complex.arg_le_pi _)
    (Complex.slitPlane_arg_ne_pi hw.2)⟩,
    ⟨Real.neg_pi_div_two_lt_arcsin.mpr hz.1, Real.arcsin_lt_pi_div_two.mpr hz.2⟩⟩

theorem spherePoint_sphereChartInverse {w : EuclideanSpace ℝ (Fin 3)} (hw : w ∈ cutSphere) :
    spherePoint (sphereChartInverse w) = w := by
  have hz := cutSphere_vertical_bounds hw
  have hsin := Real.sin_arcsin hz.1.le hz.2.le
  have hcos := Real.sin_sq_add_cos_sq (Real.arcsin (w 2))
  rw [hsin] at hcos
  have hrad : Real.cos (Real.arcsin (w 2)) = ‖horizontalComplex w‖ :=
    (sq_eq_sq₀ (Real.cos_arcsin_nonneg _) (norm_nonneg _)).mp
      (by linarith [cutSphere_sq_identity hw])
  ext i
  fin_cases i
  · change Real.cos (Real.arcsin (w 2)) * Real.cos (horizontalComplex w).arg = w 0
    rw [hrad, Complex.norm_mul_cos_arg, horizontalComplex_re]
  · change Real.cos (Real.arcsin (w 2)) * Real.sin (horizontalComplex w).arg = w 1
    rw [hrad, Complex.norm_mul_sin_arg, horizontalComplex_im]
  · exact hsin

theorem continuousOn_sphereChartInverse : ContinuousOn sphereChartInverse cutSphere := by
  exact (Complex.continuousOn_arg.comp continuous_horizontalComplex.continuousOn
    (fun _ hw => hw.2)).prodMk
    (Real.continuous_arcsin.comp (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous).continuousOn

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
  continuous_invFun := (continuousOn_iff_continuous_restrict.1
    continuousOn_sphereChartInverse).subtype_mk _

end

end GlobeFlattening
