import DiophantineConsistency.Sign14Positive74Nodes00

/-! Source-only generated positive-coordinate circuit nodes. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74

def g08 (p : Fin 4 → ℤ) : Expr (Fin 14) := (Expr.var 10) + (Expr.var 11)
def g09 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g08 p) * (g05 p)
def g10 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g09 p) + (Expr.var 10)
def g11 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g07 p) * (g10 p)
def g12 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g02 p) + (g11 p)
def g13 (p : Fin 4 → ℤ) : Expr (Fin 14) := (Expr.constant 4) * (g07 p)
def g14 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g13 p) + (Expr.constant 3)
def g15 (p : Fin 4 → ℤ) : Expr (Fin 14) := (Expr.var 13) * (g14 p)

end DiophantineConsistency.Sign14Positive74
