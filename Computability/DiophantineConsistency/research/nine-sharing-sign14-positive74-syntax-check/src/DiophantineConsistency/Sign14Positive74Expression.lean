import DiophantineConsistency.Sign14Positive74Nodes08

/-! Source-only positive-coordinate candidate, sum of five squares. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74

def row00 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g23 p)
def row01 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g41 p)
def row02 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g48 p)
def row03 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g61 p)
def row04 (p : Fin 4 → ℤ) : Expr (Fin 14) := (g64 p)

def expression (p : Fin 4 → ℤ) : Expr (Fin 14) :=
  row00 p * row00 p + row01 p * row01 p + row02 p * row02 p +
    row03 p * row03 p + row04 p * row04 p

end DiophantineConsistency.Sign14Positive74
