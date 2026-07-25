import JacobianConjecture.Scaling

/-!
# A one-parameter family of collisions, as a torus orbit

The parameter-`t` member of the rational family is the weighted scaling by
`t⁻¹` of the mirrored integral collision.  Once that identification is made
(`collisionFamily*_eq_scale` below, the only computations in this file),
every property of the family — the common values, the collision itself, and
the closure under the mirror symmetry with parameter action `t ↦ -t` —
follows by rewriting from the torus action of `Scaling` and the single
integral collision of `Counterexample`.  The integral collision used by the
main proof is the `t = -1` member of the family.
-/

namespace LeanProofs.JacobianCounterexample

open Matrix MvPolynomial PolynomialMap

def collisionFamily₀ (R : Type*) [Field R] (t : R) : I → R :=
  ![t, -1 / t, 5 / t ^ 2]

def collisionFamily₁ (R : Type*) [Field R] (t : R) : I → R :=
  ![0, 2 / t, -16 / t ^ 2]

def collisionFamilyValue (R : Type*) [Field R] (t : R) : I → R :=
  ![0, 2 / t, 0]

/-!
## The orbit identifications

These three lemmas are the only computations in this file.
-/

theorem collisionFamily₀_eq_scale (R : Type*) [Field R] (t : R) (ht : t ≠ 0) :
    collisionFamily₀ R t = scaleSource t⁻¹ (flipSource (collision₀ R)) := by
  funext i
  fin_cases i <;>
    simp [collisionFamily₀, scaleSource, flipSource, collision₀] <;>
    field_simp

theorem collisionFamily₁_eq_scale (R : Type*) [Field R] (t : R) (ht : t ≠ 0) :
    collisionFamily₁ R t = scaleSource t⁻¹ (flipSource (collision₁ R)) := by
  funext i
  fin_cases i <;>
    simp [collisionFamily₁, scaleSource, flipSource, collision₁] <;>
    field_simp

theorem collisionFamilyValue_eq_scale
    (R : Type*) [Field R] (t : R) (ht : t ≠ 0) :
    collisionFamilyValue R t = scaleTarget t⁻¹ (flipTarget (collisionValue R)) := by
  funext i
  fin_cases i <;>
    simp [collisionFamilyValue, scaleTarget, flipTarget, collisionValue]
  field_simp

/-!
## The family, by rewriting alone
-/

theorem collisionFamily₀_value (R : Type*) [Field R] (t : R) (ht : t ≠ 0) :
    evalMap (counterexample R) (collisionFamily₀ R t) =
      collisionFamilyValue R t := by
  rw [collisionFamily₀_eq_scale R t ht,
    counterexample_scaling _ (inv_ne_zero ht),
    counterexample_equivariant, collision₀_value]
  exact (collisionFamilyValue_eq_scale R t ht).symm

theorem collisionFamily₁_value (R : Type*) [Field R] (t : R) (ht : t ≠ 0) :
    evalMap (counterexample R) (collisionFamily₁ R t) =
      collisionFamilyValue R t := by
  rw [collisionFamily₁_eq_scale R t ht,
    counterexample_scaling _ (inv_ne_zero ht),
    counterexample_equivariant, collision₁_value]
  exact (collisionFamilyValue_eq_scale R t ht).symm

theorem collisionFamily (R : Type*) [Field R] (t : R) (ht : t ≠ 0) :
    evalMap (counterexample R) (collisionFamily₀ R t) =
      evalMap (counterexample R) (collisionFamily₁ R t) :=
  (collisionFamily₀_value R t ht).trans (collisionFamily₁_value R t ht).symm

theorem collisionFamily_points_distinct
    (R : Type*) [Field R] (t : R) (ht : t ≠ 0) :
    collisionFamily₀ R t ≠ collisionFamily₁ R t := by
  intro h
  have hx := congrFun h 0
  apply ht
  simpa [collisionFamily₀, collisionFamily₁] using hx

/-!
## Equivariance of the family

The source involution is the `s = -1` slice of the action, so composing it
with the orbit parametrization sends the parameter-`t` member to the
parameter-`-t` member.
-/

theorem collisionFamily₀_mirror (R : Type*) [Field R] (t : R) (ht : t ≠ 0) :
    flipSource (collisionFamily₀ R t) = collisionFamily₀ R (-t) := by
  rw [collisionFamily₀_eq_scale R t ht, flipSource_eq_scale, scaleSource_comp,
    show (-1 : R) * t⁻¹ = (-t)⁻¹ by rw [inv_neg, neg_one_mul],
    ← collisionFamily₀_eq_scale R (-t) (neg_ne_zero.mpr ht)]

theorem collisionFamily₁_mirror (R : Type*) [Field R] (t : R) (ht : t ≠ 0) :
    flipSource (collisionFamily₁ R t) = collisionFamily₁ R (-t) := by
  rw [collisionFamily₁_eq_scale R t ht, flipSource_eq_scale, scaleSource_comp,
    show (-1 : R) * t⁻¹ = (-t)⁻¹ by rw [inv_neg, neg_one_mul],
    ← collisionFamily₁_eq_scale R (-t) (neg_ne_zero.mpr ht)]

theorem collisionFamilyValue_mirror (R : Type*) [Field R] (t : R) (ht : t ≠ 0) :
    flipTarget (collisionFamilyValue R t) = collisionFamilyValue R (-t) := by
  rw [collisionFamilyValue_eq_scale R t ht, flipTarget_eq_scale,
    scaleTarget_comp,
    show (-1 : R) * t⁻¹ = (-t)⁻¹ by rw [inv_neg, neg_one_mul],
    ← collisionFamilyValue_eq_scale R (-t) (neg_ne_zero.mpr ht)]

/-!
## The inverted parametrization

Scaling the parameter-`t` member by `t` recovers the mirrored integral
collision.
-/

theorem scale_collisionFamily₀ (R : Type*) [Field R] (t : R) (ht : t ≠ 0) :
    scaleSource t (collisionFamily₀ R t) = flipSource (collision₀ R) := by
  rw [collisionFamily₀_eq_scale R t ht, scaleSource_comp,
    mul_inv_cancel₀ ht, scaleSource_one]

theorem scale_collisionFamily₁ (R : Type*) [Field R] (t : R) (ht : t ≠ 0) :
    scaleSource t (collisionFamily₁ R t) = flipSource (collision₁ R) := by
  rw [collisionFamily₁_eq_scale R t ht, scaleSource_comp,
    mul_inv_cancel₀ ht, scaleSource_one]

theorem scale_collisionFamilyValue (R : Type*) [Field R] (t : R) (ht : t ≠ 0) :
    scaleTarget t (collisionFamilyValue R t) = flipTarget (collisionValue R) := by
  rw [collisionFamilyValue_eq_scale R t ht, scaleTarget_comp,
    mul_inv_cancel₀ ht, scaleTarget_one]

/-!
The integral collision of `Counterexample` is exactly the `t = -1` member of
the family.
-/

theorem collisionFamily₀_at_neg_one (R : Type*) [Field R] :
    collisionFamily₀ R (-1) = collision₀ R := by
  funext i
  fin_cases i <;>
    norm_num [collisionFamily₀, collision₀, Matrix.cons_val_two]

theorem collisionFamily₁_at_neg_one (R : Type*) [Field R] :
    collisionFamily₁ R (-1) = collision₁ R := by
  funext i
  fin_cases i <;>
    norm_num [collisionFamily₁, collision₁, Matrix.cons_val_two]

theorem collisionFamilyValue_at_neg_one (R : Type*) [Field R] :
    collisionFamilyValue R (-1) = collisionValue R := by
  funext i
  fin_cases i <;>
    norm_num [collisionFamilyValue, collisionValue, Matrix.cons_val_two]

end LeanProofs.JacobianCounterexample
