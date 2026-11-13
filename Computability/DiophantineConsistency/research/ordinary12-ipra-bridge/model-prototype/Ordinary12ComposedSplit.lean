import DiophantineConsistency.Ordinary12CarrierExclusions
import DiophantineConsistency.Ordinary12FactorSplit

/-! Unconditional abstract three-factor unit split over IΣ₁ models. Literal
binding to the 12-variable graph, ports, and rank reconstruction remain open. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Ordinary12ComposedSplit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
open DiophantineConsistency.Ordinary12Residual
open DiophantineConsistency.Ordinary12CarrierExclusions
open DiophantineConsistency.Ordinary12FactorSplit

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Each of the three abstract signed factors is +1 whenever their product
is +1. The three valuations may differ; no port or rank premise is used. -/
theorem abstract_ordinary_three_factor_units (v₀ v₁ v₂ : Fin 8 → V)
    (h : Equivalent
      (multiply (multiply (pairEval firstFactor v₀) (pairEval mainFactor v₁))
        (pairEval ordinaryFactor v₂)) (natural (1:V))) :
    (pairEval firstFactor v₀).1 = (pairEval firstFactor v₀).2 + 1 ∧
    (pairEval mainFactor v₁).1 = (pairEval mainFactor v₁).2 + 1 ∧
    (pairEval ordinaryFactor v₂).1 = (pairEval ordinaryFactor v₂).2 + 1 := by
  exact three_factor_units h (first_factor_ne_negative_one v₀)
    (main_factor_ne_negative_one v₁) (ordinary_factor_ne_negative_one v₂)

end DiophantineConsistency.Ordinary12ComposedSplit
#print axioms DiophantineConsistency.Ordinary12ComposedSplit.abstract_ordinary_three_factor_units
