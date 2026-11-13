import DiophantineConsistency.Sign14Positive74Nodes04

/-! Source-only generated positive-coordinate circuit nodes. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74

def g40 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g36 p) - (g39 p)
def g41 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g40 p) - (Expr.constant 1)
def g42 (p : Fin 4 → ℤ) : Expr (Fin 14) := (Expr.constant (p 1)) + (Expr.var 8)
def g43 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g26 p) - (Expr.var 2)
def g44 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g42 p) * (g43 p)
def g45 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g44 p) - (Expr.var 1)
def g46 (p : Fin 4 → ℤ) : Expr (Fin 14) := (Expr.var 3) - (Expr.constant 1)
def g47 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g46 p) * (g00 p)

end DiophantineConsistency.Sign14Positive74
