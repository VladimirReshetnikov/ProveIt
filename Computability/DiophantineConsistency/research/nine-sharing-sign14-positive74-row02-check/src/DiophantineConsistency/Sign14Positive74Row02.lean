import DiophantineConsistency.Sign14Positive74CoordinateProbe

/-! SOURCE-ONLY: proposed transport-row evaluation under positive valuation. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74Row02
open Sign14Positive74

variable {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R)

theorem row_eval : (row02 p).evalRing (fun i => v i + 1) =
    (Sign14Optimized86.row02' p).evalRing (Fin.cons 1 v) := by
  have h1 : Fin.cases (1 : R) v (1 : Fin 15) = v 0 := by rfl
  have h2 : Fin.cases (1 : R) v (2 : Fin 15) = v 1 := by rfl
  have h3 : Fin.cases (1 : R) v (3 : Fin 15) = v 2 := by rfl
  have h4 : Fin.cases (1 : R) v (4 : Fin 15) = v 3 := by rfl
  have h9 : Fin.cases (1 : R) v (9 : Fin 15) = v 8 := by rfl
  simp [row02, g48, g47, g46, g45, g44, g43, g42, g26, g01, g00,
    Sign14Optimized86.row02', Expr.evalRing, Fin.cons, h1, h2, h3, h4, h9] <;> ring
end DiophantineConsistency.Sign14Positive74Row02
#print axioms DiophantineConsistency.Sign14Positive74Row02.row_eval
