import Surreal.Algebra.ProjectiveCircle
import Surreal.Surcomplex.AngleGroup
import Surreal.Surcomplex.FiniteTrigonometryIdentities
import Surreal.Foundations.SignSequenceFiniteUnits

/-!
# Projective half-angle coordinates on the actual surreal circle

The algebraic chart specializes to the actual sign field and Mathlib's
unitary group. Its trigonometric interpretation and infinite-parameter
behavior complete `trigonometry:thm:cayley`.
-/

universe u

namespace Surreal.Surcomplex

open Foundations OnePoint
open scoped LinearAlgebra.Projectivization

noncomputable section

local instance : DecidableEq SignSequence.{u} := Classical.decEq _

/-- The affine Cayley chart, defined for every actual surreal parameter. -/
def cayley (t : SignSequence.{u}) : Surcomplex.{u} := Complexify.circleParam t

/-- The inverse affine coordinate of a surcomplex direction. -/
def cayleyCoord (z : Surcomplex.{u}) : SignSequence.{u} := z.im / (1 + z.re)

@[simp] theorem cayley_re (t : SignSequence.{u}) :
    (cayley t).re = (1 - t ^ 2) / (1 + t ^ 2) := rfl

@[simp] theorem cayley_im (t : SignSequence.{u}) :
    (cayley t).im = 2 * t / (1 + t ^ 2) := rfl

/-- The source's fractional and coordinate expressions give the same actual point. -/
theorem cayley_eq_fraction (t : SignSequence.{u}) :
    cayley t = (1 + I * ofReal t) / (1 - I * ofReal t) :=
  Complexify.circleParam_eq_fraction t

@[simp] theorem modulus_cayley (t : SignSequence.{u}) : modulus (cayley t) = 1 := by
  apply modulus_eq_of_nonneg_sq (by norm_num)
  simpa only [one_pow, cayley, normSq] using (Complexify.normSq_circleParam t).symm

/-- No actual affine parameter, including an infinite one, gives the omitted point exactly. -/
theorem cayley_ne_neg_one (t : SignSequence.{u}) : cayley t ≠ -1 :=
  Complexify.circleParam_ne_neg_one t

@[simp] theorem cayleyCoord_cayley (t : SignSequence.{u}) : cayleyCoord (cayley t) = t :=
  Complexify.circleCoord_circleParam t

/-- Substitution of the inverse coordinate recovers every direction except the omitted point. -/
theorem cayley_cayleyCoord (z : UnitCircle.{u}) (hz : z.val ≠ -1) :
    cayley (cayleyCoord z.val) = z.val := by
  apply Complexify.circleParam_circleCoord _ hz
  change normSq z.val = 1
  rw [← modulus_sq, modulus_unitCircle, one_pow]

/-- The full affine chart is a bijection onto the actual circle punctured at `-1`. -/
def cayleyEquiv : SignSequence.{u} ≃ {z : UnitCircle.{u} // z.val ≠ -1} where
  toFun t := ⟨⟨cayley t, (mem_unitCircle_iff _).mpr (modulus_cayley t)⟩, cayley_ne_neg_one t⟩
  invFun z := cayleyCoord z.val.val
  left_inv := cayleyCoord_cayley
  right_inv z := Subtype.ext (Subtype.ext (cayley_cayleyCoord z.val z.property))

private def normCircleEquiv : {z : Surcomplex.{u} // normSq z = 1} ≃ UnitCircle.{u} where
  toFun z := ⟨z.val, (mem_unitCircle_iff _).mpr
    (modulus_eq_of_nonneg_sq (by norm_num) (by simpa only [one_pow] using z.property.symm))⟩
  invFun z := ⟨z.val, by rw [← modulus_sq, modulus_unitCircle, one_pow]⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Mathlib's actual projective line is in bijection with the full actual unit circle. -/
def projectiveCayleyEquiv :
    ℙ SignSequence.{u} (Fin 2 → SignSequence.{u}) ≃ UnitCircle.{u} :=
  Complexify.projectiveCircleEquiv.trans normCircleEquiv

/-- Homogeneous coordinates evaluate by the prescribed rational formula. -/
theorem projectiveCayleyEquiv_mk (p q : SignSequence.{u})
    (h : ![p, q] ≠ (0 : Fin 2 → SignSequence.{u})) :
    (projectiveCayleyEquiv (Projectivization.mk SignSequence.{u} ![p, q] h)).val =
      Complexify.homogeneousCircle p q :=
  Complexify.projectiveCircleEquiv_mk p q h

/-- The projective point at infinity is exactly the omitted half-turn direction. -/
@[simp] theorem projectiveCayleyEquiv_infty :
    (projectiveCayleyEquiv ((OnePoint.equivProjectivization SignSequence.{u}) ∞)).val = -1 := by
  change (Complexify.projectiveCircleEquiv
    ((OnePoint.equivProjectivization SignSequence.{u}) ∞)).val = _
  simp only [Complexify.projectiveCircleEquiv_onePoint, Complexify.onePointCircleEquiv_infty]

/-- The projective chart restricts to the affine chart at every surreal scalar. -/
@[simp] theorem projectiveCayleyEquiv_coe (t : SignSequence.{u}) :
    (projectiveCayleyEquiv ((OnePoint.equivProjectivization SignSequence.{u})
      (t : OnePoint SignSequence.{u}))).val = cayley t := by
  change (Complexify.projectiveCircleEquiv
    ((OnePoint.equivProjectivization SignSequence.{u}) (t : OnePoint SignSequence.{u}))).val = _
  simp only [Complexify.projectiveCircleEquiv_onePoint, Complexify.onePointCircleEquiv_coe, cayley]

/-- The already proved homogeneous addition rule becomes multiplication of actual directions. -/
theorem projectiveCayleyEquiv_add
    (p q : ℙ SignSequence.{u} (Fin 2 → SignSequence.{u})) :
    projectiveCayleyEquiv (Complexify.projectiveAdd p q) =
      projectiveCayleyEquiv p * projectiveCayleyEquiv q := by
  apply Subtype.ext
  exact Complexify.projectiveCircleEquiv_projectiveAdd p q

/-- The affine product law, retaining its exact denominator restriction. -/
theorem cayley_mul (t s : SignSequence.{u}) (h : 1 - t * s ≠ 0) :
    cayley t * cayley s = cayley ((t + s) / (1 - t * s)) :=
  Complexify.circleParam_mul t s h

/-- Vanishing affine denominator gives exactly the projective half-turn. -/
theorem cayley_mul_eq_neg_one_iff (t s : SignSequence.{u}) :
    cayley t * cayley s = -1 ↔ 1 - t * s = 0 :=
  Complexify.circleParam_mul_eq_neg_one_iff t s

/-- The affine coordinate of a finite phase is its half-angle tangent. -/
theorem cayleyCoord_finitePhase (θ : SignSequence.FiniteElement.{u}) :
    cayleyCoord (finitePhase θ) = finiteTan (finiteHalf θ) :=
  (finiteTan_finiteHalf_eq_finiteSin_div θ).symm

/-- Half-angle tangent reconstructs every finite phase other than the projective half-turn. -/
theorem cayley_finiteTan_half (θ : SignSequence.FiniteElement.{u}) (hθ : finitePhase θ ≠ -1) :
    cayley (finiteTan (finiteHalf θ)) = finitePhase θ := by
  rw [← cayleyCoord_finitePhase]
  exact cayley_cayleyCoord (finitePhaseHom (Multiplicative.ofAdd θ)) hθ

end
end Surreal.Surcomplex
