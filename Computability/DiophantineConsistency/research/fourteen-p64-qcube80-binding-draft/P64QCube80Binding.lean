import P64QCube81
import P64QCube80

/-! Draft: bind the 80 graph to the 81 graph under the remainder substitution. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace P64QCube80Binding
open DiophantineConsistency AdaptiveEquationSyntax2011
variable {R : Type*} [CommRing R]

def liftRing (v : Fin 14 → R) : Fin 14 → R := Function.update v 9 (v 9 + v 7)

theorem first (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64QCube80.graph p).A0.evalRing (liftRing v) = (P64QCube81.graph p).A0.evalRing v := by
  simp [P64QCube80.graph,P64QCube81.graph,liftRing,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat, add_assoc]

theorem main (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64QCube80.graph p).M.evalRing (liftRing v) = (P64QCube81.graph p).M.evalRing v := by
  simp [P64QCube80.graph,P64QCube81.graph,liftRing,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]

theorem strong (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64QCube80.graph p).W.evalRing (liftRing v) = (P64QCube81.graph p).W.evalRing v := by
  simp [P64QCube80.graph,P64QCube81.graph,liftRing,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]

theorem auxiliary (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64QCube80.graph p).Na.evalRing (liftRing v) = (P64QCube81.graph p).Na.evalRing v := by
  simp [P64QCube80.graph,P64QCube81.graph,liftRing,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]

theorem transport (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64QCube80.graph p).Lt.evalRing (liftRing v) = (P64QCube81.graph p).Lt.evalRing v := by
  simp [P64QCube80.graph,P64QCube81.graph,liftRing,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]

theorem output (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64QCube80.graph p).output.evalRing (liftRing v) = (P64QCube81.graph p).output.evalRing v := by
  simp [P64QCube80.graph,P64QCube81.graph,liftRing,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat, add_assoc]

#print axioms P64QCube80Binding.first
#print axioms P64QCube80Binding.main
#print axioms P64QCube80Binding.strong
#print axioms P64QCube80Binding.auxiliary
#print axioms P64QCube80Binding.transport
#print axioms P64QCube80Binding.output
end P64QCube80Binding
