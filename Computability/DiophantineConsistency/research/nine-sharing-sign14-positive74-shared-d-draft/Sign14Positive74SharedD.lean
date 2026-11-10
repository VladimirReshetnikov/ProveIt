import DiophantineConsistency.Sign14Positive74RowsOuter

/-! SOURCE-ONLY: transport/rank and shared difference evaluations. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74SharedD
open Sign14Positive74 SharingSeed14Degree124 Sign14Positive74SharedA
variable {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R)

theorem rank_eval : (g28 p).evalRing (fun i => v i + 1) =
    (Sign14Optimized90.shared14' p).evalRing (Fin.cons 1 v) := by
  have h1 : Fin.cases (1 : R) v (1 : Fin 15) = v 0 := by rfl
  have h2 : Fin.cases (1 : R) v (2 : Fin 15) = v 1 := by rfl
  have h3 : Fin.cases (1 : R) v (3 : Fin 15) = v 2 := by rfl
  simp [g28, g27, g26, g01, g00, Sign14Optimized90.shared14',
    Sign14Optimized93.shared14', Expr.evalRing, Fin.cons, h1, h2, h3] <;> ring

theorem shared09_eval : (g32 p).evalRing (fun i => v i + 1) =
    (shared09 p).evalRing (Fin.cons 1 v) := by
  have h1 : Fin.cases (1 : R) v (1 : Fin 15) = v 0 := by rfl
  simp [g32, g31, g30, g01, g00, shared09, shared04, shared00,
    Expr.evalRing, Fin.cons, h1] <;> ring

theorem shared27_eval : (g33 p).evalRing (fun i => v i + 1) =
    (Sign14Optimized90.shared27' p).evalRing (Fin.cons 1 v) := by
  simp only [g33, g29, Sign14Optimized90.shared27', Expr.evalRing_add,
    Expr.evalRing_mul, rank_eval, shared08_eval, shared09_eval]

theorem difference_eval : (g34 p).evalRing (fun i => v i + 1) =
    (Sign14Optimized86.sharedDiff p).evalRing (Fin.cons 1 v) := by
  simp only [g34, Sign14Optimized86.sharedDiff, Expr.evalRing_sub, shared27_eval, rank_eval]
end DiophantineConsistency.Sign14Positive74SharedD
#print axioms DiophantineConsistency.Sign14Positive74SharedD.rank_eval
#print axioms DiophantineConsistency.Sign14Positive74SharedD.shared09_eval
#print axioms DiophantineConsistency.Sign14Positive74SharedD.shared27_eval
#print axioms DiophantineConsistency.Sign14Positive74SharedD.difference_eval
