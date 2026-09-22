import Surreal.Surcomplex.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Ordered fields and algebraic closedness are different

This proves the two obstructions in `found:sub:realclosed`. The surreal
sign field is not algebraically closed: `X² + 1` has no root. The concrete
surcomplex field admits no linear order compatible with its existing
multiplication, because its imaginary unit squares to `-1`.

Neither obstruction assumes or proves real closedness of the sign field
or algebraic closedness of its complexification.
-/

universe u

namespace Surreal

open Polynomial

/-- Over any ordered field, the polynomial `X² + 1` is everywhere positive. -/
theorem eval_X_sq_add_one_pos {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (x : F) :
    0 < (X ^ 2 + 1 : F[X]).eval x := by
  simpa only [eval_add, eval_pow, eval_X, eval_one] using
    add_pos_of_nonneg_of_pos (sq_nonneg x) (zero_lt_one : (0 : F) < 1)

/-- The explicit root obstruction behind `found:sub:realclosed`. -/
theorem not_isRoot_X_sq_add_one {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (x : F) :
    ¬ (X ^ 2 + 1 : F[X]).IsRoot x :=
  (eval_X_sq_add_one_pos x).ne'

/-- A nontrivial ordered field cannot be algebraically closed. -/
theorem orderedField_not_isAlgClosed (F : Type*) [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] : ¬ IsAlgClosed F := by
  intro h
  letI := h
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : F) (n := 2) (by decide)
  have hnonneg := sq_nonneg x
  rw [hx] at hnonneg
  exact (neg_neg_of_pos (zero_lt_one : (0 : F) < 1)).not_ge hnonneg

namespace Foundations.SignSequence

/-- The actual surreal field is not algebraically closed. Its eventual
real-closedness theorem must be a different assertion. -/
theorem not_isAlgClosed : ¬ IsAlgClosed SignSequence.{u} :=
  orderedField_not_isAlgClosed SignSequence.{u}

end Foundations.SignSequence

namespace Surcomplex

/-- No choice of linear order makes the existing surcomplex multiplication
an ordered-ring multiplication. This quantifies over every possible order. -/
theorem no_compatible_linearOrder (order : LinearOrder Surcomplex.{u}) :
    letI := order
    ¬ IsStrictOrderedRing Surcomplex.{u} := by
  letI := order
  intro h
  letI := h
  have hnonneg := sq_nonneg (I : Surcomplex.{u})
  rw [I_sq] at hnonneg
  exact (neg_neg_of_pos (zero_lt_one : (0 : Surcomplex.{u}) < 1)).not_ge hnonneg

end Surcomplex

end Surreal
