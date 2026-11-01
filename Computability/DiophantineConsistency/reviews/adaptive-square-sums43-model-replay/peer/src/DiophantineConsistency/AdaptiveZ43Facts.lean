import DiophantineConsistency.AdaptiveZ43Zeros
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveZ43Facts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveZ44Context AdaptiveZ43Zeros
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem facts (p : Fin 4 → ℕ) (v : Fin 44 → V)
    (hz : InternalZero (literal (fun j => (p j:ℤ))) v) :
    v 29 = (1+v 0*(p 0:V))*(1+v 0*(p 0:V)) ∧
    v 15 = v 7*v 29 ∧
    v 38 = v 7*(v 9+v 10) ∧
    v 39 = v 6+(v 30+v 7)*(v 9+v 38) ∧
    v 24+(3+4*(v 30+v 7))*(v 9+v 10) =
      v 25+v 15*v 39+(3+4*(v 30+v 7))*(v 40+v 20+v 16+1) := by
  have hall := (sum_zero (fun j => (p j:ℤ)) newFill v).mp (by rw [new_literal]; exact hz)
  have h18 := hall 18
  have h6 := hall 6
  have h28 := hall 28
  have h30 := hall 30
  have h15 := hall 15
  change InternalZero (.var 29 - ((1+.var 0*.constant ((p 0:ℕ):ℤ))*(1+.var 0*.constant ((p 0:ℕ):ℤ))) : Expr (Fin 44)) v at h18
  change InternalZero (.var 15 - (.var 7*.var 29) : Expr (Fin 44)) v at h6
  change InternalZero (.var 38 - (.var 7*(.var 9+.var 10)) : Expr (Fin 44)) v at h28
  change InternalZero (.var 39 - (.var 6+(.var 30+.var 7)*(.var 9+.var 38)) : Expr (Fin 44)) v at h30
  change InternalZero ((.var 24-.var 25) - ((.var 15*.var 39)+(3+4*(.var 30+.var 7))*((.var 40+.var 20)-((.var 9+.var 10)-.var 16-1))) : Expr (Fin 44)) v at h15
  simp [InternalZero,Expr.splitNatural,NatExpr.evalSemiring,HSub.hSub,Sub.sub] at h18 h6 h28 h30 h15
  refine ⟨h18,h6,h28,h30,?_⟩
  convert h15 using 1 <;> ring
#print axioms facts
end DiophantineConsistency.AdaptiveZ43Facts
