import Surreal.Algebra.Circle
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Projective rational coordinates on the unit circle

This file proves the projective bijection and algebraic multiplication
clauses of `trigonometry:thm:cayley` and `trigonometry:eq:projectiveaddition`.
The projective line is Mathlib's actual projectivization of `Fin 2 → F`;
its point at infinity is supplied by `OnePoint.equivProjectivization`.

The base is an arbitrary ordered field. No trigonometric function, angle
representative, surreal embedding, or topology is used by these claims.
-/

namespace Surreal.Complexify

open scoped LinearAlgebra.Projectivization
open OnePoint

noncomputable section

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

local instance projectiveCircleDecidableEq : DecidableEq F := Classical.decEq F

/-- Add the missing point `-1` to the rational affine circle chart. -/
def onePointCircleEquiv : OnePoint F ≃ {z : Complexify F // normSq z = 1} where
  toFun t := t.elim ⟨-1, by simp⟩ (fun x => ⟨circleParam x, normSq_circleParam x⟩)
  invFun z := if z.val = -1 then ∞ else ((circleCoord z.val : F) : OnePoint F)
  left_inv t := by
    cases t with
    | infty => simp
    | coe t => simp [circleParam_ne_neg_one]
  right_inv z := by
    by_cases hz : z.val = -1
    · apply Subtype.ext
      simp [hz]
    · apply Subtype.ext
      simp [hz, circleParam_circleCoord z.property hz]

@[simp] theorem onePointCircleEquiv_infty :
    (onePointCircleEquiv (∞ : OnePoint F)).val = -1 := rfl

@[simp] theorem onePointCircleEquiv_coe (t : F) :
    (onePointCircleEquiv (t : OnePoint F)).val = circleParam t := rfl

/-- The projective-line bijection in `trigonometry:thm:cayley`. -/
def projectiveCircleEquiv : ℙ F (Fin 2 → F) ≃ {z : Complexify F // normSq z = 1} :=
  (OnePoint.equivProjectivization F).symm.trans onePointCircleEquiv

/-- Homogeneous form of the rational circle chart. -/
def homogeneousCircle (p q : F) : Complexify F :=
  ⟨(q ^ 2 - p ^ 2) / (q ^ 2 + p ^ 2), 2 * p * q / (q ^ 2 + p ^ 2)⟩

theorem homogeneousCircle_den_ne_zero (p q : F)
    (h : ![p, q] ≠ (0 : Fin 2 → F)) : q ^ 2 + p ^ 2 ≠ 0 := by
  intro hz
  have hp : p = 0 := by nlinarith [sq_nonneg q, sq_nonneg p]
  have hq : q = 0 := by nlinarith [sq_nonneg q, sq_nonneg p]
  exact h (by simp [hp, hq])

theorem homogeneousCircle_eq_circleParam (p q : F) (hq : q ≠ 0) :
    homogeneousCircle p q = circleParam (p / q) := by
  have hd : q ^ 2 + p ^ 2 ≠ 0 := by positivity
  ext <;> simp only [homogeneousCircle, circleParam] <;> field_simp

@[simp] theorem homogeneousCircle_one (p : F) :
    homogeneousCircle p 1 = circleParam p := by
  simpa using homogeneousCircle_eq_circleParam p 1 one_ne_zero

theorem homogeneousCircle_at_infty (p : F) (hp : p ≠ 0) :
    homogeneousCircle p 0 = -1 := by
  ext <;> simp [homogeneousCircle, hp, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

/-- Evaluation of the projective chart on arbitrary homogeneous coordinates. -/
theorem projectiveCircleEquiv_mk (p q : F) (h : ![p, q] ≠ (0 : Fin 2 → F)) :
    (projectiveCircleEquiv (Projectivization.mk F ![p, q] h)).val =
      homogeneousCircle p q := by
  change (onePointCircleEquiv ((OnePoint.equivProjectivization F).symm
    (Projectivization.mk F ![p, q] h))).val = _
  rw [OnePoint.equivProjectivization_symm_apply_mk]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  by_cases hq : q = 0
  · have hp : p ≠ 0 := by intro hp; exact h (by simp [hp, hq])
    simp [hq, homogeneousCircle_at_infty p hp]
  · simp only [hq, ↓reduceIte, onePointCircleEquiv_coe]
    rw [homogeneousCircle_eq_circleParam p q hq, div_eq_inv_mul]

/-- Nonzero homogeneous input pairs give a nonzero product pair. This is
the sum-of-squares certificate in the proof of the projective addition law. -/
theorem projective_add_pair_ne_zero (p q r s : F)
    (hpq : ![p, q] ≠ (0 : Fin 2 → F)) (hrs : ![r, s] ≠ (0 : Fin 2 → F)) :
    ![p * s + q * r, q * s - p * r] ≠ (0 : Fin 2 → F) := by
  have hd := mul_ne_zero (homogeneousCircle_den_ne_zero p q hpq)
    (homogeneousCircle_den_ne_zero r s hrs)
  intro h
  have h₀ := congrFun h 0
  have h₁ := congrFun h 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply]
    at h₀ h₁
  apply hd
  calc
    (q ^ 2 + p ^ 2) * (s ^ 2 + r ^ 2) =
        (p * s + q * r) ^ 2 + (q * s - p * r) ^ 2 := by ring
    _ = 0 := by rw [h₀, h₁]; ring

/-- Homogeneous rational coordinates multiply by the displayed bilinear
rule in `trigonometry:eq:projectiveaddition`. -/
theorem homogeneousCircle_mul (p q r s : F)
    (hpq : ![p, q] ≠ (0 : Fin 2 → F)) (hrs : ![r, s] ≠ (0 : Fin 2 → F)) :
    homogeneousCircle p q * homogeneousCircle r s =
      homogeneousCircle (p * s + q * r) (q * s - p * r) := by
  have hp := homogeneousCircle_den_ne_zero p q hpq
  have hr := homogeneousCircle_den_ne_zero r s hrs
  have hd : (q * s - p * r) ^ 2 + (p * s + q * r) ^ 2 =
      (q ^ 2 + p ^ 2) * (s ^ 2 + r ^ 2) := by ring
  ext <;> simp only [mul_re, mul_im, homogeneousCircle, hd] <;>
    field_simp <;> ring

/-- Transport multiplication of directions to the actual projective line. -/
def projectiveAdd (u v : ℙ F (Fin 2 → F)) : ℙ F (Fin 2 → F) :=
  projectiveCircleEquiv.symm ⟨(projectiveCircleEquiv u).val *
    (projectiveCircleEquiv v).val, by
      rw [normSq_mul, (projectiveCircleEquiv u).property,
        (projectiveCircleEquiv v).property, one_mul]⟩

/-- The exact homogeneous-coordinate addition law, including points at infinity. -/
theorem projectiveAdd_mk (p q r s : F)
    (hpq : ![p, q] ≠ (0 : Fin 2 → F)) (hrs : ![r, s] ≠ (0 : Fin 2 → F)) :
    projectiveAdd (Projectivization.mk F ![p, q] hpq)
        (Projectivization.mk F ![r, s] hrs) =
      Projectivization.mk F ![p * s + q * r, q * s - p * r]
        (projective_add_pair_ne_zero p q r s hpq hrs) := by
  apply projectiveCircleEquiv.injective
  apply Subtype.ext
  change (projectiveCircleEquiv (projectiveCircleEquiv.symm _)).val = _
  rw [Equiv.apply_symm_apply]
  simp only [projectiveCircleEquiv_mk]
  exact homogeneousCircle_mul p q r s hpq hrs

/-- The homogeneous chart is the quotient `(q + ip) / (q - ip)`.
The coordinate-pair expression avoids any interpretation of infinity as a scalar. -/
theorem homogeneousCircle_eq_div (p q : F) :
    homogeneousCircle p q = (⟨q, p⟩ : Complexify F) / ⟨q, -p⟩ := by
  ext <;> simp [homogeneousCircle, div_eq_mul_inv, QuadraticAlgebra.norm_def] <;> ring

/-- The fractional expression in `trigonometry:eq:cayley`. -/
theorem circleParam_eq_fraction (t : F) :
    circleParam t = (1 + I * algebraMap F (Complexify F) t) /
      (1 - I * algebraMap F (Complexify F) t) := by
  rw [← homogeneousCircle_one t, homogeneousCircle_eq_div]
  congr 1 <;> ext <;> simp [I, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

/-- The affine direction product law when its affine denominator is nonzero. -/
theorem circleParam_mul (t u : F) (h : 1 - t * u ≠ 0) :
    circleParam t * circleParam u = circleParam ((t + u) / (1 - t * u)) := by
  have ht : ![t, 1] ≠ (0 : Fin 2 → F) := by simp
  have hu : ![u, 1] ≠ (0 : Fin 2 → F) := by simp
  have hprod := homogeneousCircle_mul t 1 u 1 ht hu
  simpa [homogeneousCircle_one,
    homogeneousCircle_eq_circleParam _ _ h] using hprod

/-- The affine denominator vanishes exactly when the product leaves the
affine chart and reaches the projective point `-1`. -/
theorem circleParam_mul_eq_neg_one_iff (t u : F) :
    circleParam t * circleParam u = -1 ↔ 1 - t * u = 0 := by
  by_cases h : 1 - t * u = 0
  · have ht : ![t, 1] ≠ (0 : Fin 2 → F) := by simp
    have hu : ![u, 1] ≠ (0 : Fin 2 → F) := by simp
    have hn := projective_add_pair_ne_zero t 1 u 1 ht hu
    have hsum : t + u ≠ 0 := by
      intro hs
      apply hn
      simp [h, hs]
    have hprod := homogeneousCircle_mul t 1 u 1 ht hu
    have heq : circleParam t * circleParam u = -1 := by
      simpa [homogeneousCircle_one, h,
        homogeneousCircle_at_infty _ hsum] using hprod
    simp [heq, h]
  · rw [circleParam_mul t u h]
    simp [circleParam_ne_neg_one, h]

@[simp] theorem projectiveCircleEquiv_onePoint (t : OnePoint F) :
    projectiveCircleEquiv ((OnePoint.equivProjectivization F) t) = onePointCircleEquiv t :=
  congrArg onePointCircleEquiv ((OnePoint.equivProjectivization F).symm_apply_apply t)

@[simp] theorem projectiveCircleEquiv_projectiveAdd (u v : ℙ F (Fin 2 → F)) :
    (projectiveCircleEquiv (projectiveAdd u v)).val =
      (projectiveCircleEquiv u).val * (projectiveCircleEquiv v).val :=
  congrArg Subtype.val (projectiveCircleEquiv.apply_symm_apply _)

/-- Two projective half-turns have the zero affine coordinate, the exceptional
case explicitly singled out after `trigonometry:eq:projectiveaddition`. -/
theorem projectiveAdd_infty_infty :
    projectiveAdd ((OnePoint.equivProjectivization F) ∞)
        ((OnePoint.equivProjectivization F) ∞) =
      (OnePoint.equivProjectivization F) ((0 : F) : OnePoint F) := by
  apply projectiveCircleEquiv.injective
  apply Subtype.ext
  rw [projectiveCircleEquiv_projectiveAdd]
  simp only [projectiveCircleEquiv_onePoint, onePointCircleEquiv_infty,
    onePointCircleEquiv_coe, neg_mul_neg, one_mul]
  ext <;> simp [circleParam, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem projectiveAdd_assoc (u v w : ℙ F (Fin 2 → F)) :
    projectiveAdd (projectiveAdd u v) w = projectiveAdd u (projectiveAdd v w) := by
  apply projectiveCircleEquiv.injective
  apply Subtype.ext
  simp only [projectiveCircleEquiv_projectiveAdd, mul_assoc]

theorem projectiveAdd_comm (u v : ℙ F (Fin 2 → F)) :
    projectiveAdd u v = projectiveAdd v u := by
  apply projectiveCircleEquiv.injective
  apply Subtype.ext
  simp only [projectiveCircleEquiv_projectiveAdd, mul_comm]

end

end Surreal.Complexify
