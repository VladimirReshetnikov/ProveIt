import Absorb88First

/-! Reflection preserves the complete 89-row graph output under the negative
first-root sign.  This is a conditional ring statement, not yet the model
equivalence or an iPRA endpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace Absorb88FullReflection
open DiophantineConsistency FreeJAbsorb88 Absorb88First

variable {R : Type*} [CommRing R]

def reflect (v : Fin 12 → R) (first : R) : Fin 12 → R :=
  Function.update v 7 (v 7 + 2*first)

@[simp] theorem reflect_0 (v : Fin 12 → R) (first : R) : reflect v first 0 = v 0 := by simp [reflect]
@[simp] theorem reflect_1 (v : Fin 12 → R) (first : R) : reflect v first 1 = v 1 := by simp [reflect]
@[simp] theorem reflect_2 (v : Fin 12 → R) (first : R) : reflect v first 2 = v 2 := by simp [reflect]
@[simp] theorem reflect_3 (v : Fin 12 → R) (first : R) : reflect v first 3 = v 3 := by simp [reflect]
@[simp] theorem reflect_4 (v : Fin 12 → R) (first : R) : reflect v first 4 = v 4 := by simp [reflect]
@[simp] theorem reflect_5 (v : Fin 12 → R) (first : R) : reflect v first 5 = v 5 := by simp [reflect]
@[simp] theorem reflect_6 (v : Fin 12 → R) (first : R) : reflect v first 6 = v 6 := by simp [reflect]
@[simp] theorem reflect_7 (v : Fin 12 → R) (first : R) : reflect v first 7 = v 7 + 2*first := by simp [reflect]
@[simp] theorem reflect_8 (v : Fin 12 → R) (first : R) : reflect v first 8 = v 8 := by simp [reflect]
@[simp] theorem reflect_9 (v : Fin 12 → R) (first : R) : reflect v first 9 = v 9 := by simp [reflect]
@[simp] theorem reflect_10 (v : Fin 12 → R) (first : R) : reflect v first 10 = v 10 := by simp [reflect]
@[simp] theorem reflect_11 (v : Fin 12 → R) (first : R) : reflect v first 11 = v 11 := by simp [reflect]

theorem root_shift (p : Fin 4 → ℤ) (v : Fin 12 → R) (first : R) :
    (firstParts p).1.evalRing (reflect v first) =
      (firstParts p).1.evalRing v + (v 0 * (p 0 : R)) * (2*first) := by
  simp only [firstParts, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    Int.cast_one, Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat,
    reflect_0,reflect_1,reflect_2,reflect_3,reflect_4,reflect_5,reflect_6,reflect_7,
    reflect_8,reflect_9,reflect_10,reflect_11]
  ring

theorem rhs_invariant (p : Fin 4 → ℤ) (v : Fin 12 → R) (first : R) :
    (firstParts p).2.evalRing (reflect v first) = (firstParts p).2.evalRing v := by
  simp only [firstParts, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    Int.cast_one, Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat,
    reflect_0,reflect_1,reflect_2,reflect_3,reflect_4,reflect_5,reflect_6,reflect_7,
    reflect_8,reflect_9,reflect_10,reflect_11]

theorem main_invariant (p : Fin 4 → ℤ) (v : Fin 12 → R) (first : R) :
    (graph p).main.evalRing (reflect v first) = (graph p).main.evalRing v := by
  simp only [graph, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    Int.cast_one, Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat,
    reflect_0,reflect_1,reflect_2,reflect_3,reflect_4,reflect_5,reflect_6,reflect_7,
    reflect_8,reflect_9,reflect_10,reflect_11]

theorem ordinary_invariant (p : Fin 4 → ℤ) (v : Fin 12 → R) (first : R) :
    (graph p).ordinary.evalRing (reflect v first) = (graph p).ordinary.evalRing v := by
  simp only [graph, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    Int.cast_one, Int.cast_ofNat, Nat.cast_one, Nat.cast_ofNat,
    reflect_0,reflect_1,reflect_2,reflect_3,reflect_4,reflect_5,reflect_6,reflect_7,
    reflect_8,reflect_9,reflect_10,reflect_11]

theorem first_invariant (p : Fin 4 → ℤ) (v : Fin 12 → R) (first : R)
    (negative : (firstParts p).1.evalRing v = -((v 0 * (p 0 : R))*first)) :
    (graph p).first.evalRing (reflect v first) = (graph p).first.evalRing v := by
  rw [first_shape]
  simp only [Expr.evalRing_sub, Expr.evalRing_mul]
  rw [root_shift, rhs_invariant, negative]
  ring

theorem output_invariant (p : Fin 4 → ℤ) (v : Fin 12 → R) (first : R)
    (negative : (firstParts p).1.evalRing v = -((v 0 * (p 0 : R))*first)) :
    (graph p).output.evalRing (reflect v first) = (graph p).output.evalRing v := by
  have shape : (graph p).output =
      (graph p).first*(graph p).first+(graph p).main*(graph p).main+
        (graph p).ordinary*(graph p).ordinary := by rfl
  rw [shape]
  simp only [Expr.evalRing_add, Expr.evalRing_mul]
  rw [first_invariant p v first negative, main_invariant, ordinary_invariant]

#print axioms Absorb88FullReflection.output_invariant
end Absorb88FullReflection
