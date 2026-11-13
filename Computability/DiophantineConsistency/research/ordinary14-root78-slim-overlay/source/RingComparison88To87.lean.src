import P88QuotientGuardedGraph
import P87ShiftedGuardGraph

/-! Source-only ring-field comparison for omega=t+F. Both graph imports are
unelaborated; no positive witness or model endpoint claim is asserted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.Ring88To87Draft
open AdaptiveEquationSyntax2011
variable {R : Type*} [CommRing R]

def transform (v : Fin 14 → R) : Fin 14 → R :=
  Function.update v 13 (v 13+v 1)

/-- The exact guard identity uses q=1+b, over any commutative ring. -/
theorem guard_cut (b C X K F t : R) :
    C*(X+K*(1+b))-F-b*(t+F)=C*(X+K*(1+b))-F*(1+b)-b*t := by ring

theorem first_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P87ShiftedGuard.graph p).A0.evalRing (transform v) =
      (P88QuotientGuarded.graph p).A0.evalRing v := by
  simp [P87ShiftedGuard.graph,P88QuotientGuarded.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    transform,Function.update] <;> ring

theorem main_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P87ShiftedGuard.graph p).A1.evalRing (transform v) =
      (P88QuotientGuarded.graph p).A1.evalRing v := by
  simp [P87ShiftedGuard.graph,P88QuotientGuarded.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    transform,Function.update] <;> ring

theorem aux_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P87ShiftedGuard.graph p).aux.evalRing (transform v) =
      (P88QuotientGuarded.graph p).aux.evalRing v := by
  simp [P87ShiftedGuard.graph,P88QuotientGuarded.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    transform,Function.update] <;> ring

theorem strong_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P87ShiftedGuard.graph p).gap.evalRing (transform v) =
      (P88QuotientGuarded.graph p).gap.evalRing v := by
  simp [P87ShiftedGuard.graph,P88QuotientGuarded.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    transform,Function.update] <;> ring

theorem guard_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P87ShiftedGuard.graph p).guardResidual.evalRing (transform v) =
      (P88QuotientGuarded.graph p).Bt.evalRing v-
        (P88QuotientGuarded.graph p).b.evalRing v*v 13 := by
  simp [P87ShiftedGuard.graph,P88QuotientGuarded.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    transform,Function.update] <;> ring

theorem output_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P87ShiftedGuard.graph p).output.evalRing (transform v) =
      (P88QuotientGuarded.graph p).output.evalRing v := by
  rw [P87ShiftedGuard.output_shape,P88QuotientGuarded.output_shape]
  simp only [Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,Expr.evalRing_var,
    Expr.evalRing_ofNat,Expr.evalRing_constant,Int.cast_one,Nat.cast_one]
  rw [first_eval,main_eval,aux_eval,strong_eval,guard_eval]

end DiophantineConsistency.Ring88To87Draft

#print axioms DiophantineConsistency.Ring88To87Draft.output_eval
