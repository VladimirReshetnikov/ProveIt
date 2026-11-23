import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
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
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    rw [PiLp.inner_apply, Fin.sum_univ_three] <;>
    simp only [RCLike.inner_apply, RCLike.conj_to_real] <;>
    simp [sphereFrame, sphereEast, sphereNorth, spherePoint] <;>
    first
    | (ring; done)
    | linear_combination Real.sin_sq_add_cos_sq p.1
    | linear_combination
        (Real.sin p.2)^2 * Real.sin_sq_add_cos_sq p.1 + Real.sin_sq_add_cos_sq p.2
    | linear_combination
        (Real.cos p.2)^2 * Real.sin_sq_add_cos_sq p.1 + Real.sin_sq_add_cos_sq p.2
    | linear_combination
        -(Real.sin p.2 * Real.cos p.2) * Real.sin_sq_add_cos_sq p.1

@[simp] theorem norm_spherePoint (p : ℝ × ℝ) : ‖spherePoint p‖ = 1 :=
  (orthonormal_sphereFrame p).norm_eq_one (2 : Fin 3)

/-- The differential of the spherical parametrization. -/
def sphereDerivative (p : ℝ × ℝ) :
    ℝ × ℝ →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (Real.cos p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (sphereEast p) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (sphereNorth p)

theorem sphereDerivative_apply (p v : ℝ × ℝ) :
    sphereDerivative p v = (Real.cos p.2 * v.1) • sphereEast p + v.2 • sphereNorth p :=
  rfl

theorem hasFDerivAt_spherePoint (p : ℝ × ℝ) :
    HasFDerivAt spherePoint (sphereDerivative p) p := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_piLp]
  intro i
  rw [hasFDerivWithinAt_univ]
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

/-- Euclidean tangent coordinates in the orthonormal east-north frame. -/
def sphereFlattenDerivative (p : ℝ × ℝ) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![innerSL ℝ (sphereEast p), innerSL ℝ (sphereNorth p)])

theorem sphereFlattenDerivative_apply (p : ℝ × ℝ) (w : EuclideanSpace ℝ (Fin 3)) :
    sphereFlattenDerivative p w =
      !₂[⟪sphereEast p, w⟫, ⟪sphereNorth p, w⟫] := by
  ext i
  fin_cases i <;> rfl

/-- The inverse isometry sends a planar vector into the tangent plane. -/
def sphereTangentLift (p : ℝ × ℝ) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.proj 0).smulRight (sphereEast p) +
    (EuclideanSpace.proj 1).smulRight (sphereNorth p)

theorem sphereTangentLift_apply (p : ℝ × ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    sphereTangentLift p v = v 0 • sphereEast p + v 1 • sphereNorth p :=
  rfl

private def sphereFrameBasis (p : ℝ × ℝ) : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) :=
  let h := orthonormal_sphereFrame p
  let b := basisOfOrthonormalOfCardEqFinrank h (by simp [finrank_euclideanSpace])
  b.toOrthonormalBasis (by simpa [b] using h)

private theorem sphereFrameBasis_apply (p : ℝ × ℝ) (i : Fin 3) :
    sphereFrameBasis p i = sphereFrame p i := by
  simp [sphereFrameBasis]

private theorem sphereFrameBasis_repr (p : ℝ × ℝ) (w : EuclideanSpace ℝ (Fin 3)) :
    (sphereFrameBasis p).repr w =
      !₂[(sphereFlattenDerivative p w) 0, (sphereFlattenDerivative p w) 1, ⟪spherePoint p, w⟫] := by
  rw [sphereFlattenDerivative_apply]
  ext i
  rw [OrthonormalBasis.repr_apply_apply, sphereFrameBasis_apply]
  fin_cases i <;> rfl

private theorem sphereFrameBasis_repr_tangentLift (p : ℝ × ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    (sphereFrameBasis p).repr (sphereTangentLift p v) = !₂[v 0, v 1, 0] := by
  apply (sphereFrameBasis p).repr.symm.injective
  rw [LinearIsometryEquiv.symm_apply_apply, ← (sphereFrameBasis p).sum_repr_symm,
    Fin.sum_univ_three, sphereTangentLift_apply]
  simp [sphereFrameBasis_apply, sphereFrame]

theorem norm_sphereTangentLift (p : ℝ × ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    ‖sphereTangentLift p v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← (sphereFrameBasis p).repr.norm_map (sphereTangentLift p v),
    sphereFrameBasis_repr_tangentLift,
    EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three,
    Fin.sum_univ_two]
  change v 0 ^ 2 + v 1 ^ 2 + 0 ^ 2 = _
  simp

theorem sphereFlattenDerivative_leftInverse (p : ℝ × ℝ) :
    Function.LeftInverse (sphereFlattenDerivative p) (sphereTangentLift p) := by
  intro v
  have h := sphereFrameBasis_repr_tangentLift p v
  rw [sphereFrameBasis_repr] at h
  ext i
  have hi := congrArg (fun x : EuclideanSpace ℝ (Fin 3) => x i.castSucc) h
  fin_cases i <;> exact hi

theorem tangent_sphereTangentLift (p : ℝ × ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    ⟪spherePoint p, sphereTangentLift p v⟫ = 0 := by
  have h := sphereFrameBasis_repr_tangentLift p v
  rw [sphereFrameBasis_repr] at h
  exact congrArg (fun x : EuclideanSpace ℝ (Fin 3) => x 2) h

/-- Zero radial component is exactly what is needed to recover the original
vector from its two tangent coordinates. -/
theorem sphereTangentLift_sphereFlattenDerivative_of_tangent (p : ℝ × ℝ)
    {w : EuclideanSpace ℝ (Fin 3)} (h : ⟪spherePoint p, w⟫ = 0) :
    sphereTangentLift p (sphereFlattenDerivative p w) = w := by
  apply (sphereFrameBasis p).repr.injective
  rw [sphereFrameBasis_repr_tangentLift, sphereFrameBasis_repr, h]

theorem norm_sphereFlattenDerivative_of_tangent (p : ℝ × ℝ) {w : EuclideanSpace ℝ (Fin 3)}
    (hw : ⟪spherePoint p, w⟫ = 0) : ‖sphereFlattenDerivative p w‖ = ‖w‖ := by
  rw [← norm_sphereTangentLift p (sphereFlattenDerivative p w),
    sphereTangentLift_sphereFlattenDerivative_of_tangent p hw]

end

end GlobeFlattening
