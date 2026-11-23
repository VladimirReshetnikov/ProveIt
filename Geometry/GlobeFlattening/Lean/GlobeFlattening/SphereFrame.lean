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

open scoped RealInnerProductSpace BigOperators

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
  · convert hsnd.cos.mul hfst.cos using 1 <;> try rfl
    apply ContinuousLinearMap.ext
    intro v
    simp [sphereDerivative_apply, sphereEast, sphereNorth]
    ring
  · convert hsnd.cos.mul hfst.sin using 1 <;> try rfl
    apply ContinuousLinearMap.ext
    intro v
    simp [sphereDerivative_apply, sphereEast, sphereNorth]
    ring
  · convert hsnd.sin using 1 <;> try rfl
    apply ContinuousLinearMap.ext
    intro v
    simp [sphereDerivative_apply, sphereEast, sphereNorth, mul_comm]

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

private def tangentFrame (p : ℝ × ℝ) : Fin 2 → EuclideanSpace ℝ (Fin 3) :=
  sphereFrame p ∘ Fin.castSucc

private theorem orthonormal_tangentFrame (p : ℝ × ℝ) : Orthonormal ℝ (tangentFrame p) :=
  (orthonormal_sphereFrame p).comp _ (Fin.castSucc_injective _)

private theorem sphereTangentLift_eq_sum (p : ℝ × ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    sphereTangentLift p v = ∑ i, v i • tangentFrame p i := by
  rw [Fin.sum_univ_two]
  rfl

theorem norm_sphereTangentLift (p : ℝ × ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    ‖sphereTangentLift p v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, sphereTangentLift_eq_sum,
    (orthonormal_tangentFrame p).inner_sum, EuclideanSpace.real_norm_sq_eq]
  simp [pow_two]

theorem sphereFlattenDerivative_leftInverse (p : ℝ × ℝ) :
    Function.LeftInverse (sphereFlattenDerivative p) (sphereTangentLift p) := by
  intro v
  rw [sphereFlattenDerivative_apply, sphereTangentLift_eq_sum]
  ext i
  change (!₂[⟪sphereEast p, ∑ j, v j • tangentFrame p j⟫,
    ⟪sphereNorth p, ∑ j, v j • tangentFrame p j⟫] : EuclideanSpace ℝ (Fin 2)) i = v i
  have hi := (orthonormal_tangentFrame p).inner_right_fintype (fun j => v j) i
  fin_cases i <;> exact hi

/-- The projection of the spherical coordinate differential has precisely
the two coefficients of the planar triangular derivative. -/
theorem sphereFlattenDerivative_sphereDerivative (p v : ℝ × ℝ) :
    sphereFlattenDerivative p (sphereDerivative p v) = !₂[Real.cos p.2 * v.1, v.2] := by
  calc
    _ = sphereFlattenDerivative p (sphereTangentLift p !₂[Real.cos p.2 * v.1, v.2]) := rfl
    _ = _ := sphereFlattenDerivative_leftInverse p _

end

end GlobeFlattening
