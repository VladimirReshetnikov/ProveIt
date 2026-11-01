import DiophantineConsistency.AdaptiveQF41Maps
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveQF41Norm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveQF41Context AdaptiveQF41Zeros AdaptiveQF41Maps ArithmeticAdaptiveQuotients2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem old_norm (p : Fin 4 → ℤ) (v : Fin 42 → V)
    (hz : InternalZero (AdaptiveQV42Context.literal p) v) :
    v 23*v 23 = (v 14*v 14)*(1+v 30) := by
  have h0 := (old_all p v).mp hz 0
  have h20 := (old_all p v).mp hz 20
  change InternalZero ((.var 23*.var 23)-(.var 29*(1+.var 30)) : Expr (Fin 42)) v at h0
  change InternalZero ((.var 29-(.var 14*.var 14)) : Expr (Fin 42)) v at h20
  simp [InternalZero,Expr.splitNatural,NatExpr.evalSemiring,HSub.hSub,Sub.sub] at h0 h20
  rw [h20] at h0
  exact h0

theorem quotient (p : Fin 4 → ℤ) (v : Fin 42 → V) (hv : ∀ i,0<v i)
    (hz : InternalZero (AdaptiveQV42Context.literal p) v) :
    ∃ t : V, 0<t ∧ v 23=v 14*t ∧ t*t=1+v 30 := by
  obtain ⟨t,ht,hn⟩ := scaled_quotient (v 14) (v 23) (1+v 30) (hv 14) (old_norm p v hz)
  have hp : 0<t := by
    apply pos_of_mul_pos_right (a := v 14) _ (Arithmetic.zero_le _)
    rw [←ht]
    exact hv 23
  exact ⟨t,hp,ht,hn⟩

theorem child_norm (p : Fin 4 → ℤ) (v : Fin 41 → V) :
    InternalZero (residuals p 0) v ↔ v 23*v 23=1+v 29 := by
  change InternalZero ((.var 23*.var 23)-(1+.var 29) : Expr (Fin 41)) v ↔ _
  simp [InternalZero,Expr.splitNatural,NatExpr.evalSemiring,HSub.hSub,Sub.sub]
#print axioms old_norm
#print axioms quotient
#print axioms child_norm
end DiophantineConsistency.AdaptiveQF41Norm
