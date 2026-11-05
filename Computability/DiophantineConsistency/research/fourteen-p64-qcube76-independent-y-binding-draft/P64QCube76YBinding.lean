import P64QCube76Y
import P64QCube77

/-! Unchecked draft: ring-valued independent-y graph bindings. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace P64QCube76YBinding
open DiophantineConsistency AdaptiveEquationSyntax2011
variable {R : Type*} [CommRing R]

def oldV (p : Fin 4 → ℤ) (v : Fin 14 → R) : R :=
  let qm := (p 0:R)*v 0
  let q := qm+1
  let Y := q*q*q*v 7
  let k := v 10+v 11
  let c := k*Y+v 10
  let gap := qm*(q-v 1)+v 2
  let R := gap*(q*q-1)+((p 2:R)+q*(p 3:R))*v 0
  (v 4*v 4)*(c*v 6-R)-c

def liftRing (p : Fin 4 → ℤ) (v : Fin 14 → R) : Fin 14 → R :=
  Function.update v 12 (oldV p v+v 12)

theorem first (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64QCube76Y.graph p).A0.evalRing (liftRing p v) = (P64QCube77.graph p).A0.evalRing v := by
  simp [P64QCube76Y.graph,P64QCube77.graph,liftRing,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]

theorem main (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64QCube76Y.graph p).M.evalRing (liftRing p v) = (P64QCube77.graph p).M.evalRing v := by
  simp [P64QCube76Y.graph,P64QCube77.graph,liftRing,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]

theorem strong (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64QCube76Y.graph p).W.evalRing (liftRing p v) = (P64QCube77.graph p).W.evalRing v := by
  simp [P64QCube76Y.graph,P64QCube77.graph,liftRing,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]

theorem auxiliary (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64QCube76Y.graph p).Na.evalRing (liftRing p v) = (P64QCube77.graph p).Na.evalRing v := by
  simp [P64QCube76Y.graph,P64QCube77.graph,liftRing,oldV,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]

theorem transport (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64QCube76Y.graph p).Lt.evalRing (liftRing p v) = (P64QCube77.graph p).Lt.evalRing v := by
  simp [P64QCube76Y.graph,P64QCube77.graph,liftRing,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]

theorem output (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64QCube76Y.graph p).output.evalRing (liftRing p v) = (P64QCube77.graph p).output.evalRing v := by
  simp [P64QCube76Y.graph,P64QCube77.graph,liftRing,oldV,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]

theorem auxiliary_same_square (p : Fin 4 → ℤ) (v : Fin 14 → R) (r : R)
    (h : r*r = v 12*v 12) :
    (P64QCube76Y.graph p).Na.evalRing (Function.update v 12 r) =
      (P64QCube76Y.graph p).Na.evalRing v := by
  simp [P64QCube76Y.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,h]

theorem output_same_square (p : Fin 4 → ℤ) (v : Fin 14 → R) (r : R)
    (h : r*r = v 12*v 12) :
    (P64QCube76Y.graph p).output.evalRing (Function.update v 12 r) =
      (P64QCube76Y.graph p).output.evalRing v := by
  simp [P64QCube76Y.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,h]

#print axioms P64QCube76YBinding.first
#print axioms P64QCube76YBinding.main
#print axioms P64QCube76YBinding.strong
#print axioms P64QCube76YBinding.auxiliary
#print axioms P64QCube76YBinding.transport
#print axioms P64QCube76YBinding.output
#print axioms P64QCube76YBinding.auxiliary_same_square
#print axioms P64QCube76YBinding.output_same_square
end P64QCube76YBinding
