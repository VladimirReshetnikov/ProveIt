import DiophantineConsistency.AdaptiveGap85Units
import DiophantineConsistency.ArithmeticAdaptiveStrongNorm2011

/-! The actual 85 strong factor implies its additive Pell norm. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85StrongNorm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveStrongNorm2011 AdaptiveGap85Literal AdaptiveGap85Units
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem expressionAt_strong_norm85 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) : StrongNorm v := by
  have hu := (expressionAt_factor_units85 (fun j => (p j:ℤ)) v hz).2.2.2
  change (pairEval (ArithmeticAdaptiveFactorMagnitude2011.factors (fun j => (p j:ℤ))).2.2.2 v).1 =
    (pairEval (ArithmeticAdaptiveFactorMagnitude2011.factors (fun j => (p j:ℤ))).2.2.2 v).2+1 at hu
  exact strong_norm_of_unit p v hu
end DiophantineConsistency.AdaptiveGap85StrongNorm
