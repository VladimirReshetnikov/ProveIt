import DiophantineConsistency.AdaptiveAQ33Zeros
import DiophantineConsistency.AdaptiveAQ33Bound
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ33Facts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveAQ33Context AdaptiveAQ33Zeros
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem facts (p : Fin 4 → ℕ) (v : Fin 34 → V)
    (hz : InternalZero (AdaptiveAQ34Literal.literal (fun j => (p j:ℤ))) v) :
    v 22*v 22 = v 13*v 13*(1+v 17*(v 17+(v 9+v 10))) ∧
    v 22+(v 13*(v 9+v 10))*v 18+v 18*((1+v 0*(p 0:V))*v 28) =
      v 13*(v 17+(v 9+v 10)+v 8)+v 7*(v 0*(p 0:V))+
        (v 13*(v 9+v 10))*v 19+v 19*((1+v 0*(p 0:V))*v 28) := by
  have hall := (sum_zero (fun j => (p j:ℤ)) oldFill v).mp (by rw [old_literal]; exact hz)
  have h0 := hall 0
  have h18 := hall 18
  have h12 := hall 12
  change InternalZero ((.var 22*.var 22) - ((.var 13*.var 13) * (1+.var 30)) : Expr (Fin 34)) v at h0
  change InternalZero (.var 30 - (.var 17*(.var 17+(.var 9+.var 10))) : Expr (Fin 34)) v at h18
  change InternalZero (.var 22 - ((.var 13*((.var 17+(.var 9+.var 10)+.var 8)-((.var 9+.var 10)*(.var 18-.var 19))) + .var 7*(.var 0*.constant ((p 0:ℕ):ℤ))) - ((.var 18-.var 19)*((1+.var 0*.constant ((p 0:ℕ):ℤ))*.var 28))) : Expr (Fin 34)) v at h12
  simp [InternalZero,Expr.splitNatural,NatExpr.evalSemiring,HSub.hSub,Sub.sub] at h0 h18 h12
  refine ⟨?_, ?_⟩
  · rw [← h18]
    exact h0
  · convert h12 using 1 <;> ring
#print axioms facts
end DiophantineConsistency.AdaptiveAQ33Facts
