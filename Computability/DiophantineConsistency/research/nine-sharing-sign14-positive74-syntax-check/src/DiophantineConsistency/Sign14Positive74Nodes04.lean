import DiophantineConsistency.Sign14Positive74Nodes03

/-! Source-only generated positive-coordinate circuit nodes. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74

def g32 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g31 p) * (Expr.var 0)
def g33 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g29 p) + (g32 p)
def g34 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g33 p) - (g28 p)
def g35 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g25 p) - (g34 p)
def g36 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g35 p) * (g35 p)
def g37 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g06 p) * (g09 p)
def g38 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g37 p) + (g08 p)
def g39 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g37 p) * (g38 p)

end DiophantineConsistency.Sign14Positive74
