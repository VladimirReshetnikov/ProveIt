import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Spherical coordinates and the tangent frame

The input pair consists of longitude and latitude. The ambient sphere and
planar target use Euclidean norms.
-/

namespace GlobeFlattening

open scoped RealInnerProductSpace

noncomputable section

/-- The spherical parametrization at a longitude-latitude pair. -/
def spherePoint (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[Real.cos p.2 * Real.cos p.1, Real.cos p.2 * Real.sin p.1, Real.sin p.2]

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
  refine orthonormal_iff_ite.2 fun i j => ?_
  have hLon := Real.sin_sq_add_cos_sq p.1
  have hLat := Real.sin_sq_add_cos_sq p.2
  fin_cases i <;> fin_cases j <;>
    rw [PiLp.inner_apply, Fin.sum_univ_three] <;>
    simp [RCLike.inner_apply, sphereFrame, sphereEast, sphereNorth, spherePoint, mul_pow, sq_abs] <;>
    grind only

@[simp] theorem norm_spherePoint (p : ℝ × ℝ) : ‖spherePoint p‖ = 1 :=
  (orthonormal_sphereFrame p).norm_eq_one (2 : Fin 3)

private def sphereTangentPlane (p : ℝ × ℝ) : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) :=
  (ℝ ∙ spherePoint p)ᗮ

private theorem mem_sphereTangentPlane {p : ℝ × ℝ} {w : EuclideanSpace ℝ (Fin 3)} :
    w ∈ sphereTangentPlane p ↔ ⟪spherePoint p, w⟫ = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right

private def sphereTangentFrame (p : ℝ × ℝ) (i : Fin 2) : sphereTangentPlane p :=
  ⟨sphereFrame p i.castSucc, mem_sphereTangentPlane.2
    ((orthonormal_sphereFrame p).inner_eq_zero (Fin.castSucc_ne_last i).symm)⟩

private def sphereTangentBasis (p : ℝ × ℝ) : OrthonormalBasis (Fin 2) ℝ (sphereTangentPlane p) := by
  have hon : Orthonormal ℝ (sphereTangentFrame p) :=
    (sphereTangentPlane p).subtypeₗᵢ.orthonormal_comp_iff.mp <|
      (orthonormal_sphereFrame p).comp Fin.castSucc (Fin.castSucc_injective 2)
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  refine OrthonormalBasis.mk hon (hon.linearIndependent.span_eq_top_of_card_eq_finrank ?_).ge
  have hp : spherePoint p ≠ 0 := (orthonormal_sphereFrame p).ne_zero (2 : Fin 3)
  rw [Fintype.card_fin, sphereTangentPlane, Submodule.finrank_orthogonal_span_singleton (n := 2) hp]

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
  exact (congrArg Subtype.val ((sphereTangentBasis p).repr.symm_apply_apply
    ((sphereTangentPlane p).orthogonalProjectionOnto w))).trans
      ((sphereTangentPlane p).starProjection_eq_self_iff.2 (mem_sphereTangentPlane.2 h))

theorem norm_sphereFlattenDerivative_of_tangent (p : ℝ × ℝ) {w : EuclideanSpace ℝ (Fin 3)}
    (hw : ⟪spherePoint p, w⟫ = 0) : ‖sphereFlattenDerivative p w‖ = ‖w‖ := by
  rw [← norm_sphereTangentLift p (sphereFlattenDerivative p w),
    sphereTangentLift_sphereFlattenDerivative_of_tangent p hw]

/-- The usual coordinate identification of the real plane with Euclidean space.
The pair carries the product norm for the analytic construction. -/
def planarEuclideanEquiv : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm

/-- The differential of the spherical parametrization is the tangent lift
with longitude scaled by the cosine of latitude. -/
def sphereDerivative (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  sphereTangentLift p ∘L planarEuclideanEquiv.toContinuousLinearMap ∘L
    (Real.cos p.2 • ContinuousLinearMap.id ℝ ℝ).prodMap (ContinuousLinearMap.id ℝ ℝ)

theorem sphereDerivative_apply (p v : ℝ × ℝ) :
    sphereDerivative p v = (Real.cos p.2 * v.1) • sphereEast p + v.2 • sphereNorth p := by
  change ((sphereTangentBasis p).repr.symm !₂[Real.cos p.2 * v.1, v.2]).1 = _
  rw [← (sphereTangentBasis p).sum_repr_symm, Fin.sum_univ_two]
  simp [sphereTangentBasis, sphereTangentFrame, sphereFrame]

theorem hasFDerivAt_spherePoint (p : ℝ × ℝ) :
    HasFDerivAt spherePoint (sphereDerivative p) p := by
  rw [← (PiLp.continuousLinearEquiv 2 ℝ _).comp_hasFDerivAt_iff, hasFDerivAt_pi']
  intro i
  have hfst := hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := p)
  have hsnd := hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := p)
  fin_cases i
  case' «0» => apply (hsnd.cos.mul hfst.cos).congr_fderiv
  case' «1» => apply (hsnd.cos.mul hfst.sin).congr_fderiv
  case' «2» => apply hsnd.sin.congr_fderiv
  all_goals
    apply ContinuousLinearMap.ext
    intro v
    simp [sphereDerivative_apply, sphereEast, sphereNorth]
    ring

theorem continuous_spherePoint : Continuous spherePoint :=
  continuous_iff_continuousAt.2 fun p => (hasFDerivAt_spherePoint p).continuousAt

end

end GlobeFlattening
