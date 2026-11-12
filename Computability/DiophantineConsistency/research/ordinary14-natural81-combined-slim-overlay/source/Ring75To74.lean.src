import P75NegativePell
import P74PositiveGuard

/-! Source-only ring identity between the literal 75 and all-positive 74
graphs. This proves no positive-coordinate map or model endpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.Ring75To74Draft
open AdaptiveEquationSyntax2011
variable {R : Type*} [CommRing R]

/-- The 74 guard coordinate is the 75 coordinate plus one. -/
def transform (v : Fin 14 → R) : Fin 14 → R := Function.update v 13 (v 13+1)

theorem guard_cut (C X K F b h : R) :
    C*(X+K)+(1+b-F)-b*(h+1)=1+(C*(X+K)-F-b*h) := by ring

/-- The four restricted factors have identical literal expressions. -/
theorem common_fields (p : Fin 4 → ℤ) :
    (P74PositiveGuard.graph p).first=(P75NegativePell.graph p).first ∧
    (P74PositiveGuard.graph p).main=(P75NegativePell.graph p).main ∧
    (P74PositiveGuard.graph p).aux=(P75NegativePell.graph p).aux ∧
    (P74PositiveGuard.graph p).strong=(P75NegativePell.graph p).strong := by
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- None of the restricted factors depends on the guard slot. -/
theorem restricted_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P74PositiveGuard.graph p).first.evalRing (transform v)=
      (P75NegativePell.graph p).first.evalRing v ∧
    (P74PositiveGuard.graph p).main.evalRing (transform v)=
      (P75NegativePell.graph p).main.evalRing v ∧
    (P74PositiveGuard.graph p).aux.evalRing (transform v)=
      (P75NegativePell.graph p).aux.evalRing v ∧
    (P74PositiveGuard.graph p).strong.evalRing (transform v)=
      (P75NegativePell.graph p).strong.evalRing v := by
  simp [P74PositiveGuard.graph,P75NegativePell.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    transform,Function.update]

/-- The changed guard factor is exact for all rings and signed port values. -/
theorem guard_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P74PositiveGuard.graph p).guardFactor.evalRing (transform v)=
      (P75NegativePell.graph p).guardFactor.evalRing v := by
  simp [P74PositiveGuard.graph,P75NegativePell.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    transform,Function.update] <;> ring

theorem output_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P74PositiveGuard.graph p).output.evalRing (transform v)=
      (P75NegativePell.graph p).output.evalRing v := by
  rw [P74PositiveGuard.output_shape,P75NegativePell.output_shape]
  simp only [Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_ofNat,Expr.evalRing_constant,Int.cast_one,Nat.cast_one]
  rcases restricted_eval p v with ⟨h0,h1,h2,h3⟩
  rw [h0,h1,h2,h3,guard_eval]

end DiophantineConsistency.Ring75To74Draft

#print axioms DiophantineConsistency.Ring75To74Draft.output_eval
