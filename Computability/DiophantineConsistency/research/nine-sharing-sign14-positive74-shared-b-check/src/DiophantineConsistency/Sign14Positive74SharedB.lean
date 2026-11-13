import DiophantineConsistency.Sign14Positive74SharedA

/-! SOURCE-ONLY: additional shared positive/natural evaluation identities. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74SharedB
open Sign14Positive74 SharingSeed14Degree124 Sign14Positive74SharedA
variable {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R)

theorem shared13_eval : (g05 p).evalRing (fun i => v i + 1) =
    (shared13 p).evalRing (Fin.cons 1 v) := by
  have h8 : Fin.cases (1 : R) v (8 : Fin 15) = v 7 := by rfl
  simp only [g05, shared13, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one, shared12_eval]
  simp [Fin.cons, h8]

theorem shared18_eval : (g06 p).evalRing (fun i => v i + 1) =
    (shared18 p).evalRing (Fin.cons 1 v) := by
  simp only [g06, shared18, Expr.evalRing_mul, shared05_eval, shared13_eval]

theorem shared23_eval : (g07 p).evalRing (fun i => v i + 1) =
    (shared23 p).evalRing (Fin.cons 1 v) := by
  simp only [g07, shared23, Expr.evalRing_add, shared18_eval, shared13_eval]

theorem shared16_eval : (g09 p).evalRing (fun i => v i + 1) =
    (shared16 p).evalRing (Fin.cons 1 v) := by
  have h11 : Fin.cases (1 : R) v (11 : Fin 15) = v 10 := by rfl
  have h12 : Fin.cases (1 : R) v (12 : Fin 15) = v 11 := by rfl
  simp only [g09, g08, shared16, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one, shared13_eval]
  simp [Fin.cons, h11, h12]

theorem shared17_eval : (g10 p).evalRing (fun i => v i + 1) =
    (shared17 p).evalRing (Fin.cons 1 v) := by
  have h11 : Fin.cases (1 : R) v (11 : Fin 15) = v 10 := by rfl
  simp only [g10, shared17, Expr.evalRing_add, Expr.evalRing_var,
    Expr.evalRing_constant, Int.cast_one, shared16_eval]
  simp [Fin.cons, h11]
end DiophantineConsistency.Sign14Positive74SharedB
#print axioms DiophantineConsistency.Sign14Positive74SharedB.shared13_eval
#print axioms DiophantineConsistency.Sign14Positive74SharedB.shared18_eval
#print axioms DiophantineConsistency.Sign14Positive74SharedB.shared23_eval
#print axioms DiophantineConsistency.Sign14Positive74SharedB.shared16_eval
#print axioms DiophantineConsistency.Sign14Positive74SharedB.shared17_eval
