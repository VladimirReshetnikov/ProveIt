import P64QCube79
import P64QCube80

/-! Draft: bind the first-root candidate to the 80-operation graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace P64QCube79Binding
open DiophantineConsistency AdaptiveEquationSyntax2011
variable {R : Type*} [CommRing R]

def ell (p : Fin 4 → ℤ) (v : Fin 14 → R) : R :=
  let q := (p 0:R)*v 0+1
  let Y := q*q*q*v 7
  (v 8*q)*Y*((v 10+v 11)*Y)

def liftRing (p : Fin 4 → ℤ) (v : Fin 14 → R) : Fin 14 → R :=
  Function.update v 9 (ell p v + v 9)

theorem first (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64QCube79.graph p).A0.evalRing (liftRing p v) = (P64QCube80.graph p).A0.evalRing v := by
  simp [P64QCube79.graph,P64QCube80.graph,liftRing,ell,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]

theorem main (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64QCube79.graph p).M.evalRing (liftRing p v) = (P64QCube80.graph p).M.evalRing v := by
  simp [P64QCube79.graph,P64QCube80.graph,liftRing,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]

theorem strong (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64QCube79.graph p).W.evalRing (liftRing p v) = (P64QCube80.graph p).W.evalRing v := by
  simp [P64QCube79.graph,P64QCube80.graph,liftRing,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]

theorem auxiliary (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64QCube79.graph p).Na.evalRing (liftRing p v) = (P64QCube80.graph p).Na.evalRing v := by
  simp [P64QCube79.graph,P64QCube80.graph,liftRing,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]

theorem transport (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64QCube79.graph p).Lt.evalRing (liftRing p v) = (P64QCube80.graph p).Lt.evalRing v := by
  simp [P64QCube79.graph,P64QCube80.graph,liftRing,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]

theorem output (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64QCube79.graph p).output.evalRing (liftRing p v) = (P64QCube80.graph p).output.evalRing v := by
  simp [P64QCube79.graph,P64QCube80.graph,liftRing,ell,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]

#print axioms P64QCube79Binding.first
#print axioms P64QCube79Binding.main
#print axioms P64QCube79Binding.strong
#print axioms P64QCube79Binding.auxiliary
#print axioms P64QCube79Binding.transport
#print axioms P64QCube79Binding.output
end P64QCube79Binding
