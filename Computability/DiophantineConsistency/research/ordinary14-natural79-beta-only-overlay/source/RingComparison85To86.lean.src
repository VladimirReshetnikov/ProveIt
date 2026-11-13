import P86ResidueGraph
import P85QcubeGraph

/-! Source-only ring-evaluation comparison. No positive-model witness map or
reverse quotient is established. Both graph imports are uncompiled drafts;
no Lean or endpoint result is claimed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.Ring85To86Draft
open AdaptiveEquationSyntax2011
variable {R : Type*} [CommRing R]

/-- Slot 7 becomes Y=q³*s and slot 8 becomes the old root r+s. -/
def transform (p : Fin 4 → ℤ) (v : Fin 14 → R) : Fin 14 → R :=
  Function.update (Function.update v 7 ((1+v 0*(p 0 : R))*
    ((1+v 0*(p 0 : R))*(1+v 0*(p 0 : R)))*v 7)) 8 (v 8+v 7)

/-- The exact first-root cut under Y=q³*s. -/
theorem first_cut (q b s P r : R) :
    (q*(q*q)*b)*(P-(r+s))+(q*(q*q)*s)*b = (q*(q*q)*b)*(P-r) := by ring

theorem first_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P86ResidueGraph.graph p).A0.evalRing (transform p v) =
      (P85QcubeGraph.graph p).A0.evalRing v := by
  simp [P86ResidueGraph.graph,P85QcubeGraph.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    transform,Function.update] <;> ring

theorem main_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P86ResidueGraph.graph p).A1.evalRing (transform p v) =
      (P85QcubeGraph.graph p).A1.evalRing v := by
  simp [P86ResidueGraph.graph,P85QcubeGraph.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    transform,Function.update] <;> ring

theorem aux_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P86ResidueGraph.graph p).aux.evalRing (transform p v) =
      (P85QcubeGraph.graph p).aux.evalRing v := by
  simp [P86ResidueGraph.graph,P85QcubeGraph.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    transform,Function.update] <;> ring

theorem strong_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P86ResidueGraph.graph p).gap.evalRing (transform p v) =
      (P85QcubeGraph.graph p).gap.evalRing v := by
  simp [P86ResidueGraph.graph,P85QcubeGraph.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    transform,Function.update] <;> ring

theorem guard_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P86ResidueGraph.graph p).guardResidual.evalRing (transform p v) =
      (P85QcubeGraph.graph p).guardResidual.evalRing v := by
  simp [P86ResidueGraph.graph,P85QcubeGraph.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    transform,Function.update] <;> ring

theorem output_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P86ResidueGraph.graph p).output.evalRing (transform p v) =
      (P85QcubeGraph.graph p).output.evalRing v := by
  rw [P86ResidueGraph.output_shape,P85QcubeGraph.output_shape]
  simp only [Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_ofNat,Expr.evalRing_constant,Int.cast_one,Nat.cast_one]
  rw [first_eval,main_eval,aux_eval,strong_eval,guard_eval]

end DiophantineConsistency.Ring85To86Draft

#print axioms DiophantineConsistency.Ring85To86Draft.output_eval
