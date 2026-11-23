import GlobeFlattening.SphereChart
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

/-!
# Spherical coordinates and the tangent frame

The input pair consists of longitude and latitude. The ambient sphere and
planar target use Euclidean norms.
-/

namespace GlobeFlattening

open scoped RealInnerProductSpace

noncomputable section

/-- Unit tangent in the direction of increasing longitude. -/
def sphereEast (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[-Real.sin p.1, Real.cos p.1, 0]

/-- Unit tangent in the direction of increasing latitude. -/
def sphereNorth (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[-Real.sin p.2 * Real.cos p.1, -Real.sin p.2 * Real.sin p.1, Real.cos p.2]

/-- The first two vectors are the tangent frame. The last is the radial normal. -/
def sphereFrame (p : ℝ × ℝ) : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![sphereEast p, sphereNorth p, spherePoint p]

theorem orthonormal_sphereFrame (p : ℝ × ℝ) : Orthonormal ℝ (sphereFrame p) := by
  have hLon := Real.sin_sq_add_cos_sq p.1
  have hLat := Real.sin_sq_add_cos_sq p.2
  simp [sphereFrame, Fin.forall_fin_succ, norm_spherePoint]
  simp [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero,
    EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
    sphereEast, sphereNorth, spherePoint, mul_pow]
  grind only

private def sphereTangentPlane (p : ℝ × ℝ) : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) :=
  (ℝ ∙ spherePoint p)ᗮ

private theorem mem_sphereTangentPlane {p : ℝ × ℝ} {w : EuclideanSpace ℝ (Fin 3)} :
    w ∈ sphereTangentPlane p ↔ ⟪spherePoint p, w⟫ = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right

private def sphereTangentBasis (p : ℝ × ℝ) : OrthonormalBasis (Fin 2) ℝ (sphereTangentPlane p) := by
  have h := orthonormal_sphereFrame p
  have hon := (h.comp Fin.castSucc (Fin.castSucc_injective 2)).codRestrict (sphereTangentPlane p)
    (fun i => mem_sphereTangentPlane.2 (h.inner_eq_zero (Fin.castSucc_ne_last i).symm))
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  exact OrthonormalBasis.mk hon (hon.linearIndependent.span_eq_top_of_card_eq_finrank
    (Submodule.finrank_orthogonal_span_singleton (n := 2) (h.ne_zero (2 : Fin 3))).symm).ge

/-- East and north coordinates of the orthogonal projection onto the tangent plane. -/
def sphereFlattenDerivative (p : ℝ × ℝ) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (sphereTangentBasis p).repr.toContinuousLinearMap ∘L (sphereTangentPlane p).orthogonalProjectionOnto

/-- The inverse isometry sends a planar vector into the tangent plane. -/
def sphereTangentLift (p : ℝ × ℝ) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (sphereTangentPlane p).subtypeL ∘L (sphereTangentBasis p).repr.symm.toContinuousLinearMap

theorem norm_sphereTangentLift (p : ℝ × ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    ‖sphereTangentLift p v‖ = ‖v‖ :=
  (sphereTangentBasis p).repr.symm.norm_map v

theorem sphereFlattenDerivative_leftInverse (p : ℝ × ℝ) :
    Function.LeftInverse (sphereFlattenDerivative p) (sphereTangentLift p) := fun v => by
  simp [sphereFlattenDerivative, sphereTangentLift, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

theorem tangent_sphereTangentLift (p : ℝ × ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    ⟪spherePoint p, sphereTangentLift p v⟫ = 0 :=
  mem_sphereTangentPlane.1 ((sphereTangentBasis p).repr.symm v).2

/-- Zero radial component is exactly what is needed to recover the original
vector from its two tangent coordinates. -/
theorem sphereTangentLift_sphereFlattenDerivative_of_tangent (p : ℝ × ℝ)
    {w : EuclideanSpace ℝ (Fin 3)} (h : ⟪spherePoint p, w⟫ = 0) :
    sphereTangentLift p (sphereFlattenDerivative p w) = w := by
  simpa [sphereTangentLift, sphereFlattenDerivative] using
    (sphereTangentPlane p).starProjection_eq_self_iff.2 (mem_sphereTangentPlane.2 h)

theorem norm_sphereFlattenDerivative_of_tangent (p : ℝ × ℝ) {w : EuclideanSpace ℝ (Fin 3)}
    (hw : ⟪spherePoint p, w⟫ = 0) : ‖sphereFlattenDerivative p w‖ = ‖w‖ := by
  simpa [sphereFlattenDerivative] using
    (sphereTangentPlane p).norm_orthogonalProjectionOnto_apply (mem_sphereTangentPlane.2 hw)

/-- The usual coordinate identification of the real plane with Euclidean space.
The pair carries the product norm for the analytic construction. -/
def planarEuclideanEquiv : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm

/-- The differential of the spherical parametrization is the tangent lift
with longitude scaled by the cosine of latitude. -/
def sphereDerivative (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  sphereTangentLift p ∘L planarEuclideanEquiv.toContinuousLinearMap ∘L
    coordinateDerivative (Real.cos p.2)

theorem sphereDerivative_apply (p v : ℝ × ℝ) :
    sphereDerivative p v = (Real.cos p.2 * v.1) • sphereEast p + v.2 • sphereNorth p := by
  change ((sphereTangentBasis p).repr.symm !₂[Real.cos p.2 * v.1, v.2]).1 = _
  rw [← (sphereTangentBasis p).sum_repr_symm, Fin.sum_univ_two]
  simp [sphereTangentBasis, sphereFrame]

theorem hasFDerivAt_spherePoint (p : ℝ × ℝ) :
    HasFDerivAt spherePoint (sphereDerivative p) p := by
  rw [← (PiLp.continuousLinearEquiv 2 ℝ _).comp_hasFDerivAt_iff, hasFDerivAt_pi']
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
  have hfst := hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := p)
  have hsnd := hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := p)
  refine ⟨(hsnd.cos.mul hfst.cos).congr_fderiv ?_, (hsnd.cos.mul hfst.sin).congr_fderiv ?_,
    hsnd.sin.congr_fderiv ?_⟩
  all_goals
    apply ContinuousLinearMap.ext
    intro v
    simp [sphereDerivative_apply, sphereEast, sphereNorth]
    ring

end

end GlobeFlattening
