import OrdinarySphere7084Generic
import OrdinarySphere7084Literal

/-! The literal 70/84 expression and the 67/94 expression have the same
positive-shifted zeros at each valuation of every IΣ₁ model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.OrdinarySphere7084Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts ModelArithmetic
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem sameZero94 (v : Fin 14 → V) :
    InternalZero (positiveShift (OrdinarySphere7084Literal.expressionAt CurrentWindowCarry2011.ports)) v ↔
      InternalZero Carrier94Syntax.naturalExpression94 v := by
  change InternalZero (positiveShift (OrdinarySphere7084Literal.expressionAt CurrentWindowCarry2011.ports)) v ↔
    InternalZero (positiveShift (Carrier94Syntax.expressionAt94 CurrentWindowCarry2011.ports)) v
  rw [internalZero_positiveShift, internalZero_positiveShift, internalZero_iff, internalZero_iff,
    OrdinarySphere7084Literal.eval_expression, Carrier94Value.evalRing_expressionAt94]
  change OrdinarySphere7084Generic.value70 _ _ = 0 ↔ Carrier94Value.value94 _ _ = 0
  exact OrdinarySphere7084Generic.zero_iff94 FreshCarrierSpheres.modelFacts _ _
    FreshModel106.beta_pos (FreshModel106.shifted_pos v)

#print axioms sameZero94
end DiophantineConsistency.OrdinarySphere7084Model
