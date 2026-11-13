import P64QCubeMap
import P64QCube81

/-! Draft: bind the generated q³ quotient graph to P64 residuals. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace P64QCubeBinding
open DiophantineConsistency AdaptiveEquationSyntax2011 P64QCubeMap
variable {R : Type*} [CommRing R]

theorem first (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    let q := (p 0:R)*v 0+1
    let Q := q*q*q
    (P64Graph.graph p).A0.evalRing (liftRing p v)=
      Q*Q*(P64QCube81.graph p).A0.evalRing v := by
  rw [first_factor]
  simp only [P64QCube81.graph,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,Nat.cast_one]

theorem main (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64Graph.graph p).M.evalRing (liftRing p v)=(P64QCube81.graph p).M.evalRing v := by
  simp [P64Graph.graph,P64QCube81.graph,liftRing,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]

theorem strong (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64Graph.graph p).W.evalRing (liftRing p v)=(P64QCube81.graph p).W.evalRing v := by
  simp [P64Graph.graph,P64QCube81.graph,liftRing,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]

theorem auxiliary (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64Graph.graph p).Na.evalRing (liftRing p v)=(P64QCube81.graph p).Na.evalRing v := by
  simp [P64Graph.graph,P64QCube81.graph,liftRing,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]

theorem transport (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64Graph.graph p).Lt.evalRing (liftRing p v)=(P64QCube81.graph p).Lt.evalRing v := by
  simp [P64Graph.graph,P64QCube81.graph,liftRing,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]

theorem output_shape (p : Fin 4 → ℤ) : (P64QCube81.graph p).output =
    (P64QCube81.graph p).A0*(P64QCube81.graph p).A0+
    (P64QCube81.graph p).M*(P64QCube81.graph p).M+
    (P64QCube81.graph p).W*(P64QCube81.graph p).W+
    (P64QCube81.graph p).Na*(P64QCube81.graph p).Na+
    (P64QCube81.graph p).Lt*(P64QCube81.graph p).Lt-1 := by rfl

#print axioms P64QCubeBinding.first
#print axioms P64QCubeBinding.main
#print axioms P64QCubeBinding.strong
#print axioms P64QCubeBinding.auxiliary
#print axioms P64QCubeBinding.transport
#print axioms P64QCubeBinding.output_shape
end P64QCubeBinding
