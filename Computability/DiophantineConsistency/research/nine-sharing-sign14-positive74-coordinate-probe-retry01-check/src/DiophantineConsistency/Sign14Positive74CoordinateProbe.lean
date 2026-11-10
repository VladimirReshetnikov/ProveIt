import DiophantineConsistency.Sign14Positive74Expression

/-! SOURCE-ONLY generic ring checks for the first three positive-coordinate nodes. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74CoordinateProbe
open Sign14Positive74

variable {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R)

def oldB (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  Expr.constant (p 0) * (Expr.var 1 + Expr.constant 1)

theorem beta_eval : (g00 p).evalRing (fun i => v i + 1) =
    (oldB p).evalRing (Fin.cons 1 v) := by
  have h1 : Fin.cases (1 : R) v (1 : Fin 15) = v 0 := by rfl
  simp [g00, oldB, Expr.evalRing, Fin.cons, h1]

theorem q_eval : (g01 p).evalRing (fun i => v i + 1) =
    (oldB p + Expr.constant 1).evalRing (Fin.cons 1 v) := by
  have h1 : Fin.cases (1 : R) v (1 : Fin 15) = v 0 := by rfl
  simp [g01, g00, oldB, Expr.evalRing, Fin.cons, h1]

theorem q_minus_f_eval : (g26 p).evalRing (fun i => v i + 1) =
    (oldB p - Expr.var 2).evalRing (Fin.cons 1 v) := by
  have h1 : Fin.cases (1 : R) v (1 : Fin 15) = v 0 := by rfl
  have h2 : Fin.cases (1 : R) v (2 : Fin 15) = v 1 := by rfl
  simp [g26, g01, g00, oldB, Expr.evalRing, Fin.cons, h1, h2]
  ring
end DiophantineConsistency.Sign14Positive74CoordinateProbe
#print axioms DiophantineConsistency.Sign14Positive74CoordinateProbe.beta_eval
#print axioms DiophantineConsistency.Sign14Positive74CoordinateProbe.q_eval
#print axioms DiophantineConsistency.Sign14Positive74CoordinateProbe.q_minus_f_eval
