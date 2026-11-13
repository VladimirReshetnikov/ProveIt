import P84QcubeGraph
import P85QcubeGraph

/-! Source-only ring-evaluation comparison. This is not a positive-model
witness map: the transformed gamma is a ring difference. Imported graph
modules are uncompiled draft sources; no Lean or endpoint result is claimed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.Ring84To85Draft
open AdaptiveEquationSyntax2011
variable {R : Type*} [CommRing R]

/-- Slot 6 becomes X=q*w and slot 12 becomes the ring difference
 gamma-old=gamma-prime−w. This is not a natural positive update. -/
def transform (p : Fin 4 → ℤ) (v : Fin 14 → R) : Fin 14 → R :=
  Function.update (Function.update v 6 ((1+v 0*(p 0 : R))*v 6)) 12 (v 12-v 6)

/-- The main carrier terms combine before any square or order argument. -/
theorem factor_main (q q3 s w gamma : R) :
    ((q3*s)*(q*q))*(gamma-w)+((q*w)*(q3*s))*q =
      ((q3*s)*(q*q))*gamma := by ring

theorem first_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P85QcubeGraph.graph p).A0.evalRing (transform p v) =
      (P84QcubeGraph.graph p).A0.evalRing v := by
  simp [P85QcubeGraph.graph,P84QcubeGraph.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    transform,Function.update] <;> ring

theorem main_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P85QcubeGraph.graph p).A1.evalRing (transform p v) =
      (P84QcubeGraph.graph p).A1.evalRing v := by
  simp [P85QcubeGraph.graph,P84QcubeGraph.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    transform,Function.update] <;> ring

theorem aux_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P85QcubeGraph.graph p).aux.evalRing (transform p v) =
      (P84QcubeGraph.graph p).aux.evalRing v := by
  simp [P85QcubeGraph.graph,P84QcubeGraph.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    transform,Function.update] <;> ring

theorem strong_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P85QcubeGraph.graph p).gap.evalRing (transform p v) =
      (P84QcubeGraph.graph p).gap.evalRing v := by
  simp [P85QcubeGraph.graph,P84QcubeGraph.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    transform,Function.update] <;> ring

theorem guard_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P85QcubeGraph.graph p).guardResidual.evalRing (transform p v) =
      (P84QcubeGraph.graph p).guardResidual.evalRing v := by
  simp [P85QcubeGraph.graph,P84QcubeGraph.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    transform,Function.update] <;> ring

theorem output_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P85QcubeGraph.graph p).output.evalRing (transform p v) =
      (P84QcubeGraph.graph p).output.evalRing v := by
  rw [P85QcubeGraph.output_shape,P84QcubeGraph.output_shape]
  simp only [Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_ofNat,Expr.evalRing_constant,Int.cast_one,Nat.cast_one]
  rw [first_eval,main_eval,aux_eval,strong_eval,guard_eval]

end DiophantineConsistency.Ring84To85Draft

#print axioms DiophantineConsistency.Ring84To85Draft.output_eval
