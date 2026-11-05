import P64QCube72Free

/-! Unchecked draft: ring-level shape and main residual for 72 graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainGraphShape
open DiophantineConsistency AdaptiveEquationSyntax2011

theorem output_shape (p : Fin 4 → ℤ) : (P64QCube72Free.graph p).output =
    ((P64QCube72Free.graph p).A0*(P64QCube72Free.graph p).Na-1)*
      ((P64QCube72Free.graph p).A0*(P64QCube72Free.graph p).Na-1)+
    (P64QCube72Free.graph p).M*(P64QCube72Free.graph p).M+
    (P64QCube72Free.graph p).W*(P64QCube72Free.graph p).W+
    (P64QCube72Free.graph p).Lt*(P64QCube72Free.graph p).Lt := by rfl

theorem M_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    let q := (p 0:R)*v 0+1
    let Y := q*q*q*v 7
    let U := Y*Y
    let X := v 8*q
    let a := X*Y+Y
    let H := 4*a+3
    let c := (v 10+v 11)*Y+v 10
    let D := U*(X+a*c)+H*v 13
    let N := (a*a+H)*(c*c)+1
    (P64QCube72Free.graph p).M.evalRing v = D*D-U*U*N := by
  simp [P64QCube72Free.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]

#print axioms FreeMainGraphShape.output_shape
#print axioms FreeMainGraphShape.M_eval
end FreeMainGraphShape
