import DiophantineConsistency.Sign14Optimized86Expression

/-! Source-only generated positive-coordinate circuit nodes. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74

def g00 (p : Fin 4 → ℤ) : Expr (Fin 14) := (Expr.constant (p 0)) * (Expr.var 0)
def g01 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g00 p) + (Expr.constant 1)
def g02 (p : Fin 4 → ℤ) : Expr (Fin 14) := (Expr.var 8) * (g01 p)
def g03 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g01 p) * (g01 p)
def g04 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g03 p) * (g01 p)
def g05 (p : Fin 4 → ℤ) : Expr (Fin 14) := (Expr.var 7) * (g04 p)
def g06 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g02 p) * (g05 p)
def g07 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g06 p) + (g05 p)

end DiophantineConsistency.Sign14Positive74
