import DiophantineConsistency.AdaptiveAQ32Zeros
import DiophantineConsistency.AdaptiveAQ32Bound
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ32Facts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveAQ32Context AdaptiveAQ32Zeros
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem facts (p : Fin 4 → ℕ) (v : Fin 33 → V)
    (hz : InternalZero (AdaptiveAQ33Literal.literal (fun j => (p j:ℤ))) v) :
    v 27 = (1+v 0*(p 0:V))*(1+v 0*(p 0:V)) ∧
    v 14 = v 7*v 27 ∧
    v 16 = v 9+v 7*(v 9+v 10) ∧
    v 22+(3+4*(v 28+v 7))*(v 9+v 10) =
      v 23+v 14*(v 6+(v 28+v 7)*v 16)+(3+4*(v 28+v 7))*(v 14*v 12+v 28*(1+v 0*(p 0:V))+v 15+1) := by
  have hall := (sum_zero (fun j => (p j:ℤ)) oldFill v).mp (by rw [old_literal]; exact hz)
  have h16 := hall 16
  have h5 := hall 5
  have h7 := hall 7
  have h13 := hall 13
  change InternalZero (.var 27 - ((1+.var 0*.constant ((p 0:ℕ):ℤ))*(1+.var 0*.constant ((p 0:ℕ):ℤ))) : Expr (Fin 33)) v at h16
  change InternalZero (.var 14 - (.var 7*.var 27) : Expr (Fin 33)) v at h5
  change InternalZero (.var 16 - (.var 9+.var 7*(.var 9+.var 10)) : Expr (Fin 33)) v at h7
  change InternalZero ((.var 22-.var 23) - ((.var 14*(.var 6+(.var 28+.var 7)*.var 16))+(3+4*(.var 28+.var 7))*(((.var 14*.var 12)+(.var 28*(1+.var 0*.constant ((p 0:ℕ):ℤ))))-((.var 9+.var 10)-.var 15-1))) : Expr (Fin 33)) v at h13
  simp [InternalZero,Expr.splitNatural,NatExpr.evalSemiring,HSub.hSub,Sub.sub] at h16 h5 h7 h13
  refine ⟨h16,h5,h7,?_⟩
  convert h13 using 1; all_goals ring
#print axioms facts
end DiophantineConsistency.AdaptiveAQ32Facts
