import DiophantineConsistency.Sign14Positive74SharedC

/-! SOURCE-ONLY: first and fifth row evaluations, plus common scale square. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74RowsOuter
open Sign14Positive74 SharingSeed14Degree124 Sign14Positive74SharedB Sign14Positive74SharedC
variable {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R)

theorem row00_eval : (row00 p).evalRing (fun i => v i + 1) =
    (Sign14Optimized94.row00'' p).evalRing (Fin.cons 1 v) := by
  simp only [row00, g23, g22, g21, Sign14Optimized94.row00'', Expr.evalRing_sub,
    Expr.evalRing_mul, square_offset_eval, shared40_eval, shared17_eval]

theorem scale_square_eval : (g51 p).evalRing (fun i => v i + 1) =
    (Sign14Optimized94.shared43'' p).evalRing (Fin.cons 1 v) := by
  have h6 : Fin.cases (1 : R) v (6 : Fin 15) = v 5 := by rfl
  simp only [g51, g50, Sign14Optimized94.shared43'', Sign14Optimized94.shared42'',
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant,
    Int.cast_one, square_offset_eval]
  simp [Fin.cons, h6]

theorem row04_eval : (row04 p).evalRing (fun i => v i + 1) =
    (Sign14Optimized94.row04'' p).evalRing (Fin.cons 1 v) := by
  have h5 : Fin.cases (1 : R) v (5 : Fin 15) = v 4 := by rfl
  simp only [row04, g64, g63, g62, g52, Sign14Optimized94.row04'',
    Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var,
    Expr.evalRing_constant, Int.cast_one, shared40_eval, scale_square_eval]
  simp [Fin.cons, h5]
end DiophantineConsistency.Sign14Positive74RowsOuter
#print axioms DiophantineConsistency.Sign14Positive74RowsOuter.row00_eval
#print axioms DiophantineConsistency.Sign14Positive74RowsOuter.scale_square_eval
#print axioms DiophantineConsistency.Sign14Positive74RowsOuter.row04_eval
