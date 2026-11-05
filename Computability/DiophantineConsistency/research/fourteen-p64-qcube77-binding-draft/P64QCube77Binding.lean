import P64QCube77
import P64QCube78

/-! Draft: unit-product candidate graph binding. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace P64QCube77Binding
open DiophantineConsistency AdaptiveEquationSyntax2011
variable {R : Type*} [CommRing R]

theorem first (p : Fin 4 → ℤ) : (P64QCube77.graph p).A0=(P64QCube78.graph p).A0 := by rfl
theorem main (p : Fin 4 → ℤ) : (P64QCube77.graph p).M=(P64QCube78.graph p).M := by rfl
theorem strong (p : Fin 4 → ℤ) : (P64QCube77.graph p).W=(P64QCube78.graph p).W := by rfl
theorem auxiliary (p : Fin 4 → ℤ) : (P64QCube77.graph p).Na=(P64QCube78.graph p).Na := by rfl
theorem transport (p : Fin 4 → ℤ) : (P64QCube77.graph p).Lt=(P64QCube78.graph p).Lt := by rfl

theorem output_shape (p : Fin 4 → ℤ) : (P64QCube77.graph p).output =
    ((P64QCube77.graph p).A0*(P64QCube77.graph p).Na-1)*
      ((P64QCube77.graph p).A0*(P64QCube77.graph p).Na-1)+
    (P64QCube77.graph p).M*(P64QCube77.graph p).M+
    (P64QCube77.graph p).W*(P64QCube77.graph p).W+
    (P64QCube77.graph p).Lt*(P64QCube77.graph p).Lt := by rfl

theorem output_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64QCube77.graph p).output.evalRing v =
      ((P64QCube78.graph p).A0.evalRing v*(P64QCube78.graph p).Na.evalRing v-1)*
      ((P64QCube78.graph p).A0.evalRing v*(P64QCube78.graph p).Na.evalRing v-1)+
      (P64QCube78.graph p).M.evalRing v*(P64QCube78.graph p).M.evalRing v+
      (P64QCube78.graph p).W.evalRing v*(P64QCube78.graph p).W.evalRing v+
      (P64QCube78.graph p).Lt.evalRing v*(P64QCube78.graph p).Lt.evalRing v := by
  rw [output_shape,first,main,strong,auxiliary,transport]
  simp [Expr.evalRing_add,Expr.evalRing_mul,Expr.evalRing_sub,Expr.evalRing_ofNat]

#print axioms P64QCube77Binding.first
#print axioms P64QCube77Binding.main
#print axioms P64QCube77Binding.strong
#print axioms P64QCube77Binding.auxiliary
#print axioms P64QCube77Binding.transport
#print axioms P64QCube77Binding.output_shape
#print axioms P64QCube77Binding.output_eval
end P64QCube77Binding
