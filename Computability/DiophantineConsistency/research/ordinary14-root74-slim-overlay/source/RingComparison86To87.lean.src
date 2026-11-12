import P87ShiftedGuardGraph
import P86ResidueGraph

/-! Source-only ring-evaluation comparison. No positive-model witness map or
reverse divisibility is established. Both graph imports are uncompiled drafts;
no Lean or endpoint result is claimed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.Ring86To87Draft
open AdaptiveEquationSyntax2011
variable {R : Type*} [CommRing R]

/-- The old guard coordinate is omega=h+C*K, with C=q-F-alpha. -/
def transform (p : Fin 4 → ℤ) (v : Fin 14 → R) : Fin 14 → R :=
  Function.update v 13 (v 13+((1+v 0*(p 0 : R))-v 1-v 2)*(p 1 : R))

/-- The exact guard cut uses q=1+b; all variables are ring-valued. -/
theorem guard_cut (b C X K F h : R) :
    C*(X+K*(1+b))-F-b*(h+C*K)=C*(X+K)-F-b*h := by ring

theorem first_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P87ShiftedGuard.graph p).A0.evalRing (transform p v) =
      (P86ResidueGraph.graph p).A0.evalRing v := by
  simp [P87ShiftedGuard.graph,P86ResidueGraph.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    transform,Function.update] <;> ring

theorem main_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P87ShiftedGuard.graph p).A1.evalRing (transform p v) =
      (P86ResidueGraph.graph p).A1.evalRing v := by
  simp [P87ShiftedGuard.graph,P86ResidueGraph.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    transform,Function.update] <;> ring

theorem aux_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P87ShiftedGuard.graph p).aux.evalRing (transform p v) =
      (P86ResidueGraph.graph p).aux.evalRing v := by
  simp [P87ShiftedGuard.graph,P86ResidueGraph.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    transform,Function.update] <;> ring

theorem strong_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P87ShiftedGuard.graph p).gap.evalRing (transform p v) =
      (P86ResidueGraph.graph p).gap.evalRing v := by
  simp [P87ShiftedGuard.graph,P86ResidueGraph.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    transform,Function.update] <;> ring

theorem guard_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P87ShiftedGuard.graph p).guardResidual.evalRing (transform p v) =
      (P86ResidueGraph.graph p).guardResidual.evalRing v := by
  simp [P87ShiftedGuard.graph,P86ResidueGraph.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    transform,Function.update] <;> ring

theorem output_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P87ShiftedGuard.graph p).output.evalRing (transform p v) =
      (P86ResidueGraph.graph p).output.evalRing v := by
  rw [P87ShiftedGuard.output_shape,P86ResidueGraph.output_shape]
  simp only [Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_ofNat,Expr.evalRing_constant,Int.cast_one,Nat.cast_one]
  rw [first_eval,main_eval,aux_eval,strong_eval,guard_eval]

end DiophantineConsistency.Ring86To87Draft

#print axioms DiophantineConsistency.Ring86To87Draft.output_eval
