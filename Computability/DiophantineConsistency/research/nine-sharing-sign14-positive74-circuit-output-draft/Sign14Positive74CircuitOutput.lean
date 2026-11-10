import DiophantineConsistency.Sign14Positive74CircuitTransitions08

/-! Final output of the checked register execution. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74Circuit

def circuitExpr (p : Fin 4 → ℤ) : Expr (Fin 14) :=
  (symState p 74).getD 73 (.constant 0)

def circuitEval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) : R :=
  (numState p v 74).getD 73 0

theorem circuitExpr_eq (p : Fin 4 → ℤ) : circuitExpr p = Sign14Positive74.expression p := by
  unfold circuitExpr
  rw [symState74]
  rfl

theorem circuitEval_eq {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    circuitEval p v = (Sign14Positive74.expression p).evalRing v := by
  unfold circuitEval
  rw [numState74]
  rfl

end DiophantineConsistency.Sign14Positive74Circuit
#print axioms DiophantineConsistency.Sign14Positive74Circuit.circuitExpr_eq
#print axioms DiophantineConsistency.Sign14Positive74Circuit.circuitEval_eq
