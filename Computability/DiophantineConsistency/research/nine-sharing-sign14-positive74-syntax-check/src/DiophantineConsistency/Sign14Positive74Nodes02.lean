import DiophantineConsistency.Sign14Positive74Nodes01

/-! Source-only generated positive-coordinate circuit nodes. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74

def g16 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g12 p) + (g15 p)
def g17 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g16 p) * (g16 p)
def g18 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g17 p) - (Expr.constant 1)
def g19 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g07 p) * (g07 p)
def g20 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g19 p) + (g14 p)
def g21 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g10 p) * (g10 p)
def g22 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g20 p) * (g21 p)
def g23 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g18 p) - (g22 p)

end DiophantineConsistency.Sign14Positive74
