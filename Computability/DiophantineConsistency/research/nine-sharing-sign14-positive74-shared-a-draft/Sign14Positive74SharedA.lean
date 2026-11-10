import DiophantineConsistency.Sign14Positive74Row02

/-! SOURCE-ONLY: first shared positive/natural evaluation identities. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74SharedA
open Sign14Positive74 SharingSeed14Degree124
variable {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R)

theorem shared05_eval : (g02 p).evalRing (fun i => v i + 1) =
    (shared05 p).evalRing (Fin.cons 1 v) := by
  have h1 : Fin.cases (1 : R) v (1 : Fin 15) = v 0 := by rfl
  have h9 : Fin.cases (1 : R) v (9 : Fin 15) = v 8 := by rfl
  simp [g02, g01, g00, shared05, Expr.evalRing, Fin.cons, h1, h9] <;> ring

theorem shared08_eval : (g03 p).evalRing (fun i => v i + 1) =
    (shared08 p).evalRing (Fin.cons 1 v) := by
  have h1 : Fin.cases (1 : R) v (1 : Fin 15) = v 0 := by rfl
  simp [g03, g01, g00, shared08, Expr.evalRing, Fin.cons, h1] <;> ring

theorem shared12_eval : (g04 p).evalRing (fun i => v i + 1) =
    (shared12 p).evalRing (Fin.cons 1 v) := by
  have h1 : Fin.cases (1 : R) v (1 : Fin 15) = v 0 := by rfl
  simp [g04, g03, g01, g00, shared12, shared08, Expr.evalRing, Fin.cons, h1] <;> ring
end DiophantineConsistency.Sign14Positive74SharedA
#print axioms DiophantineConsistency.Sign14Positive74SharedA.shared05_eval
#print axioms DiophantineConsistency.Sign14Positive74SharedA.shared08_eval
#print axioms DiophantineConsistency.Sign14Positive74SharedA.shared12_eval
