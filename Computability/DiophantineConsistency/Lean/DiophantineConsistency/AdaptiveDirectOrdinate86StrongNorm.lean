import DiophantineConsistency.AdaptiveDirectOrdinate86Comparison
import DiophantineConsistency.ArithmeticAdaptiveStrongNorm2011

/-! Strong Pell norm from the actual direct-ordinate 86 zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveDirectOrdinate86StrongNorm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveStrongNorm2011 AdaptiveDirectOrdinate86Literal
open AdaptiveDirectOrdinate86Factors AdaptiveDirectOrdinate86Units
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem expressionAt_strong_norm86 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hz : InternalZero (expressionAt86 (fun j => (p j:ℤ))) v) : StrongNorm v := by
  have hu := (expressionAt_factor_units86 (fun j => (p j:ℤ)) v hz).2.2.2
  rw [strong_factor_eq] at hu
  exact strong_norm_of_unit p v hu

end DiophantineConsistency.AdaptiveDirectOrdinate86StrongNorm
