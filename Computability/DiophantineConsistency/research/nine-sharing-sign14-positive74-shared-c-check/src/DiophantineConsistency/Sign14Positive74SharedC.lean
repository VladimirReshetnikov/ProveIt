import DiophantineConsistency.Sign14Positive74SharedB

/-! SOURCE-ONLY: central root and norm evaluation identities. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74SharedC
open Sign14Positive74 SharingSeed14Degree124 Sign14Positive74SharedA Sign14Positive74SharedB
variable {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R)

theorem shared31_eval : (g11 p).evalRing (fun i => v i + 1) =
    (shared31 p).evalRing (Fin.cons 1 v) := by
  simp only [g11, shared31, Expr.evalRing_mul, shared23_eval, shared17_eval]

theorem shared26_eval : (g14 p).evalRing (fun i => v i + 1) =
    (shared26 p).evalRing (Fin.cons 1 v) := by
  simp only [g14, g13, shared26, shared24, Expr.evalRing_add, Expr.evalRing_mul,
    Expr.evalRing_constant, shared23_eval]

theorem shared28_eval : (g15 p).evalRing (fun i => v i + 1) =
    (shared28 p).evalRing (Fin.cons 1 v) := by
  have h14 : Fin.cases (1 : R) v (14 : Fin 15) = v 13 := by rfl
  simp only [g15, shared28, Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var,
    Expr.evalRing_constant, Int.cast_one, shared26_eval]
  simp [Fin.cons, h14]

theorem center_eval : (g16 p).evalRing (fun i => v i + 1) =
    (Sign14Optimized94.center p).evalRing (Fin.cons 1 v) := by
  simp only [g16, g12, Sign14Optimized94.center, Expr.evalRing_add,
    shared05_eval, shared31_eval, shared28_eval]

theorem square_offset_eval : (g18 p).evalRing (fun i => v i + 1) =
    (Sign14Optimized94.shared41'' p).evalRing (Fin.cons 1 v) := by
  simp only [g18, g17, Sign14Optimized94.shared41'', Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_constant, center_eval]

theorem shared40_eval : (g20 p).evalRing (fun i => v i + 1) =
    (shared40 p).evalRing (Fin.cons 1 v) := by
  simp only [g20, g19, shared40, shared33, Expr.evalRing_add, Expr.evalRing_mul,
    shared23_eval, shared26_eval]
end DiophantineConsistency.Sign14Positive74SharedC
#print axioms DiophantineConsistency.Sign14Positive74SharedC.shared31_eval
#print axioms DiophantineConsistency.Sign14Positive74SharedC.shared26_eval
#print axioms DiophantineConsistency.Sign14Positive74SharedC.shared28_eval
#print axioms DiophantineConsistency.Sign14Positive74SharedC.center_eval
#print axioms DiophantineConsistency.Sign14Positive74SharedC.square_offset_eval
#print axioms DiophantineConsistency.Sign14Positive74SharedC.shared40_eval
