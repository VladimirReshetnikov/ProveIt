import DiophantineConsistency.Sign14Positive74Nodes05

/-! Source-only generated positive-coordinate circuit nodes. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74

def g48 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g45 p) - (g47 p)
def g49 (p : Fin 4 → ℤ) : Expr (Fin 14) := (Expr.var 12) * (Expr.var 12)
def g50 (p : Fin 4 → ℤ) : Expr (Fin 14) := (Expr.var 5) * (g18 p)
def g51 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g50 p) * (g50 p)
def g52 (p : Fin 4 → ℤ) : Expr (Fin 14) := (Expr.var 4) * (Expr.var 4)
def g53 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g10 p) * (Expr.var 6)
def g54 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g53 p) - (g34 p)
def g55 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g52 p) * (g54 p)

end DiophantineConsistency.Sign14Positive74
