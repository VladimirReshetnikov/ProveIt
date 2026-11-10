import DiophantineConsistency.Sign14Positive74Circuit

/-! Incremental register-state semantics: first three transitions only. -/
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
def symState (p : Fin 4 → ℤ) : ℕ → List (Expr (Fin 14))
  | 0 => []
  | n + 1 => symStep p (symState p n) (gateAt n)

theorem symState1 (p : Fin 4 → ℤ) : symState p 1 = [Sign14Positive74.g00 p] := by rfl
theorem symState2 (p : Fin 4 → ℤ) : symState p 2 = [Sign14Positive74.g00 p, Sign14Positive74.g01 p] := by
  rw [symState, symState1]
  rfl
theorem symState3 (p : Fin 4 → ℤ) : symState p 3 = [Sign14Positive74.g00 p, Sign14Positive74.g01 p, Sign14Positive74.g02 p] := by
  rw [symState, symState2]
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
def numState {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) : ℕ → List R
  | 0 => []
  | n + 1 => numStep p v (numState p v n) (gateAt n)

theorem numState1 {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) : numState p v 1 = [(Sign14Positive74.g00 p).evalRing v] := by rfl
theorem numState2 {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) : numState p v 2 = [(Sign14Positive74.g00 p).evalRing v, (Sign14Positive74.g01 p).evalRing v] := by
  rw [numState, numState1]
  rfl
theorem numState3 {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) : numState p v 3 = [(Sign14Positive74.g00 p).evalRing v, (Sign14Positive74.g01 p).evalRing v, (Sign14Positive74.g02 p).evalRing v] := by
  rw [numState, numState2]
  rfl
end DiophantineConsistency.Sign14Positive74Circuit
#print axioms DiophantineConsistency.Sign14Positive74Circuit.symState3
#print axioms DiophantineConsistency.Sign14Positive74Circuit.numState3
