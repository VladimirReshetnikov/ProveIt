import DiophantineConsistency.Sign14Positive74Circuit

/-! Explicit execution of the register DAG, and its proposed correspondence with the checked expression. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74Circuit

def symArg (p : Fin 4 → ℤ) (s : List (Expr (Fin 14))) : Arg → Expr (Fin 14)
  | .var i => .var i
  | .port i => .constant (p i)
  | .lit z => .constant z
  | .reg j => s.getD j (.constant 0)

def symOp : Op → Expr (Fin 14) → Expr (Fin 14) → Expr (Fin 14)
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b

def symStep (p : Fin 4 → ℤ) (s : List (Expr (Fin 14))) (g : Gate) : List (Expr (Fin 14)) :=
  s ++ [symOp g.op (symArg p s g.left) (symArg p s g.right)]

def circuitExpr (p : Fin 4 → ℤ) : Expr (Fin 14) :=
  (gates.foldl (symStep p) []).getD 73 (.constant 0)

set_option maxHeartbeats 1000000 in
theorem circuitExpr_eq (p : Fin 4 → ℤ) : circuitExpr p = Sign14Positive74.expression p := by
  rfl

def numArg {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) (s : List R) : Arg → R
  | .var i => v i
  | .port i => (p i : R)
  | .lit z => (z : R)
  | .reg j => s.getD j 0

def numOp {R : Type*} [CommRing R] : Op → R → R → R
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b

def numStep {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) (s : List R) (g : Gate) : List R :=
  s ++ [numOp g.op (numArg p v s g.left) (numArg p v s g.right)]

def circuitEval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) : R :=
  (gates.foldl (numStep p v) []).getD 73 0

set_option maxHeartbeats 1000000 in
theorem circuitEval_eq {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    circuitEval p v = (Sign14Positive74.expression p).evalRing v := by
  rfl

end DiophantineConsistency.Sign14Positive74Circuit
#print axioms DiophantineConsistency.Sign14Positive74Circuit.circuitExpr_eq
#print axioms DiophantineConsistency.Sign14Positive74Circuit.circuitEval_eq
