import DiophantineConsistency.Sign14Positive74SharedD

/-! SOURCE-ONLY: proposed remaining positive/natural row evaluations. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74RowsInner
open Sign14Positive74 SharingSeed14Degree124 Sign14Positive74SharedB
  Sign14Positive74SharedD Sign14Positive74RowsOuter
variable {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R)

theorem shared20_eval : (g24 p).evalRing (fun i => v i + 1) =
    (shared20 p).evalRing (Fin.cons 1 v) := by
  have h10 : Fin.cases (1 : R) v (10 : Fin 15) = v 9 := by rfl
  simp only [g24, shared20, Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var,
    Expr.evalRing_constant, Int.cast_one, shared18_eval]
  simp [Fin.cons, h10]

theorem shared21_eval : (g25 p).evalRing (fun i => v i + 1) =
    (shared21 p).evalRing (Fin.cons 1 v) := by
  have h11 : Fin.cases (1 : R) v (11 : Fin 15) = v 10 := by rfl
  have h12 : Fin.cases (1 : R) v (12 : Fin 15) = v 11 := by rfl
  simp only [g25, g08, shared21, Expr.evalRing_add, Expr.evalRing_var,
    Expr.evalRing_constant, Int.cast_one, shared20_eval]
  simp [Fin.cons, h11, h12]

theorem shared36_eval : (g35 p).evalRing (fun i => v i + 1) =
    (Sign14Optimized86.shared36' p).evalRing (Fin.cons 1 v) := by
  simp only [g35, Sign14Optimized86.shared36', Expr.evalRing_sub, shared21_eval, difference_eval]

theorem shared29_eval : (g37 p).evalRing (fun i => v i + 1) =
    (shared29 p).evalRing (Fin.cons 1 v) := by
  simp only [g37, shared29, Expr.evalRing_mul, shared18_eval, shared16_eval]

theorem row01_eval : (Sign14Positive74.row01 p).evalRing (fun i => v i + 1) =
    (Sign14Optimized86.row01' p).evalRing (Fin.cons 1 v) := by
  have h11 : Fin.cases (1 : R) v (11 : Fin 15) = v 10 := by rfl
  have h12 : Fin.cases (1 : R) v (12 : Fin 15) = v 11 := by rfl
  simp only [Sign14Positive74.row01, g41, g40, g39, g38, g36, g08,
    Sign14Optimized86.row01', Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one, shared36_eval, shared29_eval] <;>
    simp [Fin.cons, h11, h12]

theorem shared19_eval : (g53 p).evalRing (fun i => v i + 1) =
    (shared19 p).evalRing (Fin.cons 1 v) := by
  have h7 : Fin.cases (1 : R) v (7 : Fin 15) = v 6 := by rfl
  simp only [g53, shared19, Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var,
    Expr.evalRing_constant, Int.cast_one, shared17_eval]
  simp [Fin.cons, h7]

theorem shared34_eval : (g54 p).evalRing (fun i => v i + 1) =
    (Sign14Optimized86.shared34' p).evalRing (Fin.cons 1 v) := by
  simp only [g54, Sign14Optimized86.shared34', Expr.evalRing_sub, shared19_eval, difference_eval]

theorem shared35_eval : (g55 p).evalRing (fun i => v i + 1) =
    (Sign14Optimized86.shared35' p).evalRing (Fin.cons 1 v) := by
  have h5 : Fin.cases (1 : R) v (5 : Fin 15) = v 4 := by rfl
  simp only [g55, g52, Sign14Optimized86.shared35', Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one, shared34_eval]
  simp [Fin.cons, h5]

theorem shared37_eval : (g56 p).evalRing (fun i => v i + 1) =
    (Sign14Optimized86.shared37' p).evalRing (Fin.cons 1 v) := by
  simp only [g56, Sign14Optimized86.shared37', Expr.evalRing_sub, shared35_eval, shared17_eval]

theorem row03_eval : (Sign14Positive74.row03 p).evalRing (fun i => v i + 1) =
    (Sign14Optimized86.row03' p).evalRing (Fin.cons 1 v) := by
  have h13 : Fin.cases (1 : R) v (13 : Fin 15) = v 12 := by rfl
  simp only [Sign14Positive74.row03, g61, g60, g59, g58, g57, g49,
    Sign14Optimized86.row03', Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one, scale_square_eval, shared37_eval] <;>
    simp [Fin.cons, h13]
end DiophantineConsistency.Sign14Positive74RowsInner
#print axioms DiophantineConsistency.Sign14Positive74RowsInner.shared20_eval
#print axioms DiophantineConsistency.Sign14Positive74RowsInner.shared21_eval
#print axioms DiophantineConsistency.Sign14Positive74RowsInner.shared36_eval
#print axioms DiophantineConsistency.Sign14Positive74RowsInner.shared29_eval
#print axioms DiophantineConsistency.Sign14Positive74RowsInner.row01_eval
#print axioms DiophantineConsistency.Sign14Positive74RowsInner.shared19_eval
#print axioms DiophantineConsistency.Sign14Positive74RowsInner.shared34_eval
#print axioms DiophantineConsistency.Sign14Positive74RowsInner.shared35_eval
#print axioms DiophantineConsistency.Sign14Positive74RowsInner.shared37_eval
#print axioms DiophantineConsistency.Sign14Positive74RowsInner.row03_eval
