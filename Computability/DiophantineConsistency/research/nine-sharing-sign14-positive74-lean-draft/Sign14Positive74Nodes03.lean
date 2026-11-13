import DiophantineConsistency.Sign14Positive74Nodes02

/-! Source-only generated positive-coordinate circuit nodes. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74

def g24 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g06 p) * (Expr.var 9)
def g25 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g24 p) + (g08 p)
def g26 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g01 p) - (Expr.var 1)
def g27 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g00 p) * (g26 p)
def g28 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g27 p) + (Expr.var 2)
def g29 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g28 p) * (g03 p)
def g30 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g01 p) * (Expr.constant (p 3))
def g31 (p : Fin 4 → ℤ) : Expr (Fin 14) := (Expr.constant (p 2)) + (g30 p)

end DiophantineConsistency.Sign14Positive74
