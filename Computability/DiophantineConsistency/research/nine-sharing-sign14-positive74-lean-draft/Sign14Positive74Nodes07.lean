import DiophantineConsistency.Sign14Positive74Nodes06

/-! Source-only generated positive-coordinate circuit nodes. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74

def g56 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g55 p) - (g10 p)
def g57 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g56 p) * (g56 p)
def g58 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g49 p) - (g57 p)
def g59 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g51 p) * (g58 p)
def g60 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g49 p) - (g59 p)
def g61 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g60 p) - (Expr.constant 1)
def g62 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g20 p) * (g52 p)
def g63 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g62 p) - (g51 p)

end DiophantineConsistency.Sign14Positive74
