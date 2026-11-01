import DiophantineConsistency.AdaptiveZ46Zeros
import DiophantineConsistency.AdaptiveZ44Positivity
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveZ44Facts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveZ46Context AdaptiveZ46Zeros
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem facts (p : Fin 4 → ℕ) (v : Fin 46 → V)
    (hz : InternalZero (literal (fun j => (p j:ℤ))) v) :
    v 24*v 24 = v 14*v 14*(1+v 17*(v 17+(v 9+v 10))) ∧
    v 44+(v 9+v 10)*v 19 = v 45+(v 9+v 10)*v 18 ∧
    v 24+(v 14*v 44)+(v 18*v 20) =
      v 14*(v 17+(v 9+v 10)+v 8)+v 7*(v 0*(p 0:V))+(v 14*v 45)+(v 19*v 20) := by
  have hall := (sum_zero (fun j => (p j:ℤ)) newFill v).mp (by rw [new_literal]; exact hz)
  have h0 := hall 0
  have h20 := hall 20
  have h21 := hall 21
  have h29 := hall 29
  have h14 := hall 14
  change InternalZero ((.var 24*.var 24) - (.var 32 * (1+.var 33)) : Expr (Fin 46)) v at h0
  change InternalZero (.var 32 - (.var 14*.var 14) : Expr (Fin 46)) v at h20
  change InternalZero (.var 33 - (.var 17*(.var 17+(.var 9+.var 10))) : Expr (Fin 46)) v at h21
  change InternalZero ((.var 44-.var 45) - ((.var 9+.var 10)*(.var 18-.var 19)) : Expr (Fin 46)) v at h29
  change InternalZero (.var 24 - ((.var 14*((.var 17+(.var 9+.var 10)+.var 8)-(.var 44-.var 45)) + .var 7*(.var 0*.constant ((p 0:ℕ):ℤ))) - ((.var 18-.var 19)*.var 20)) : Expr (Fin 46)) v at h14
  simp [InternalZero,Expr.splitNatural,NatExpr.evalSemiring,HSub.hSub,Sub.sub] at h0 h20 h21 h29 h14
  refine ⟨?_, ?_, ?_⟩
  · rw [← h20, ← h21]
    exact h0
  · exact h29
  · convert h14 using 1 <;> ring
#print axioms facts
end DiophantineConsistency.AdaptiveZ44Facts
