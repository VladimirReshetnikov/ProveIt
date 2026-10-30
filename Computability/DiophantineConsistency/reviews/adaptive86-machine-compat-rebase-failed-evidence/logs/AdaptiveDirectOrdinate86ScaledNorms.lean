import DiophantineConsistency.AdaptiveDirectOrdinate86Units
import DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011

/-! Actual first and main scaled Pell norms from the direct-ordinate zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveDirectOrdinate86ScaledNorms
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveScaledNorms2011 AdaptiveDirectOrdinate86Literal
open AdaptiveDirectOrdinate86Factors AdaptiveDirectOrdinate86Units
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem expressionAt_scaled_norms86 (p : Fin 4 → ℤ) (v : Fin 13 → V)
    (hz : InternalZero (expressionAt86 p) v) :
    magnitude (pairEval (rootTerm (factors p).1) v)*magnitude (pairEval (rootTerm (factors p).1) v) +
        (pairEval (rightTerm (factors p).1) v).2 = (pairEval (rightTerm (factors p).1) v).1 ∧
    magnitude (pairEval (rootTerm (factors p).2.1) v)*magnitude (pairEval (rootTerm (factors p).2.1) v) +
        (pairEval (rightTerm (factors p).2.1) v).2 = (pairEval (rightTerm (factors p).2.1) v).1 := by
  obtain ⟨h0,h1,_,_⟩ := expressionAt_factor_units86 p v hz
  rw [←first_factor_pair_eq p v] at h0
  rw [second_factor_eq] at h1
  rw [first_shape p] at h0
  rw [main_shape p] at h1
  exact ⟨unit_square_norm _ _ _ h0,unit_square_norm _ _ _ h1⟩

theorem expressionAt_concrete_scaled_norms86 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hz : InternalZero (expressionAt86 (fun j => (p j:ℤ))) v) : ScaledNorms p v := by
  have h := expressionAt_scaled_norms86 (fun j => (p j:ℤ)) v hz
  rw [first_rhs_pair p v,main_rhs_pair p v] at h
  simpa only [ScaledNorms,Prod.fst,Prod.snd,add_zero] using h
end DiophantineConsistency.AdaptiveDirectOrdinate86ScaledNorms
