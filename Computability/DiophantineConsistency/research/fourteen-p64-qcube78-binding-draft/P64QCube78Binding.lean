import P64QCube78
import P64QCube79

/-! Draft: bind the shifted first residual and output to the 79 graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace P64QCube78Binding
open DiophantineConsistency AdaptiveEquationSyntax2011
variable {R : Type*} [CommRing R]

theorem first (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64QCube78.graph p).A0.evalRing v = (P64QCube79.graph p).A0.evalRing v+1 := by
  simp [P64QCube78.graph,P64QCube79.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]
  ring

theorem main (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64QCube78.graph p).M.evalRing v = (P64QCube79.graph p).M.evalRing v := by
  rfl

theorem strong (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64QCube78.graph p).W.evalRing v = (P64QCube79.graph p).W.evalRing v := by
  rfl

theorem auxiliary (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64QCube78.graph p).Na.evalRing v = (P64QCube79.graph p).Na.evalRing v := by
  rfl

theorem transport (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64QCube78.graph p).Lt.evalRing v = (P64QCube79.graph p).Lt.evalRing v := by
  rfl

theorem output_shape (p : Fin 4 → ℤ) : (P64QCube78.graph p).output =
    (P64QCube78.graph p).A0*(P64QCube78.graph p).A0+
    (P64QCube78.graph p).M*(P64QCube78.graph p).M+
    (P64QCube78.graph p).W*(P64QCube78.graph p).W+
    (P64QCube78.graph p).Na*(P64QCube78.graph p).Na+
    (P64QCube78.graph p).Lt*(P64QCube78.graph p).Lt-2 := by rfl

theorem parent_output_shape (p : Fin 4 → ℤ) : (P64QCube79.graph p).output =
    (P64QCube79.graph p).A0*(P64QCube79.graph p).A0+
    (P64QCube79.graph p).M*(P64QCube79.graph p).M+
    (P64QCube79.graph p).W*(P64QCube79.graph p).W+
    (P64QCube79.graph p).Na*(P64QCube79.graph p).Na+
    (P64QCube79.graph p).Lt*(P64QCube79.graph p).Lt-1 := by rfl

theorem output (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64QCube78.graph p).output.evalRing v = (P64QCube79.graph p).output.evalRing v+
      2*(P64QCube79.graph p).A0.evalRing v := by
  rw [output_shape,parent_output_shape]
  simp only [Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,Expr.evalRing_ofNat]
  rw [first,main,strong,auxiliary,transport]
  ring

#print axioms P64QCube78Binding.first
#print axioms P64QCube78Binding.main
#print axioms P64QCube78Binding.strong
#print axioms P64QCube78Binding.auxiliary
#print axioms P64QCube78Binding.transport
#print axioms P64QCube78Binding.output
end P64QCube78Binding
