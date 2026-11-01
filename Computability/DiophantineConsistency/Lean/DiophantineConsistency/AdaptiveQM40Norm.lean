import DiophantineConsistency.AdaptiveQM40Maps
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveQM40Norm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveQM40Context AdaptiveQM40Zeros AdaptiveQM40Maps ArithmeticAdaptiveQuotients2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem old_norm (p : Fin 4 → ℤ) (v : Fin 41 → V)
    (hz : InternalZero (AdaptiveQF41Context.literal p) v) :
    v 24*v 24 = (v 15*v 15)*(1+v 34) := by
  have h1 := (old_all p v).mp hz 1
  have h21 := (old_all p v).mp hz 21
  change InternalZero ((.var 24*.var 24)-(.var 30*(1+.var 34)) : Expr (Fin 41)) v at h1
  change InternalZero ((.var 30-(.var 15*.var 15)) : Expr (Fin 41)) v at h21
  simp [InternalZero,Expr.splitNatural,NatExpr.evalSemiring,HSub.hSub,Sub.sub] at h1 h21
  rw [h21] at h1
  exact h1

theorem quotient (p : Fin 4 → ℤ) (v : Fin 41 → V) (hv : ∀ i,0<v i)
    (hz : InternalZero (AdaptiveQF41Context.literal p) v) :
    ∃ t : V, 0<t ∧ v 24=v 15*t ∧ t*t=1+v 34 := by
  obtain ⟨t,ht,hn⟩ := scaled_quotient (v 15) (v 24) (1+v 34) (hv 15) (old_norm p v hz)
  have hp : 0<t := by
    apply pos_of_mul_pos_right (a := v 15) _ (Arithmetic.zero_le _)
    rw [←ht]
    exact hv 24
  exact ⟨t,hp,ht,hn⟩

theorem child_norm (p : Fin 4 → ℤ) (v : Fin 40 → V) :
    InternalZero (residuals p 1) v ↔ v 24*v 24=1+v 33 := by
  change InternalZero ((.var 24*.var 24)-(1+.var 33) : Expr (Fin 40)) v ↔ _
  simp [InternalZero,Expr.splitNatural,NatExpr.evalSemiring,HSub.hSub,Sub.sub]
#print axioms old_norm
#print axioms quotient
#print axioms child_norm
end DiophantineConsistency.AdaptiveQM40Norm
