import OrdinarySphere6984Literal
import OrdinarySphere7084IPRA

/-! Same-valuation model identity and standard-iPRA/GG endpoint for 69/84. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.OrdinarySphere6984IPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat
open HAExpressionAssembly FoundationHANoZero
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix

section Model
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem sameZero70 (v : Fin 14 → V) :
    InternalZero (positiveShift (OrdinarySphere6984Literal.expressionAt CurrentWindowCarry2011.ports)) v ↔
      InternalZero (positiveShift (OrdinarySphere7084Literal.expressionAt CurrentWindowCarry2011.ports)) v := by
  rw [internalZero_positiveShift, internalZero_positiveShift, internalZero_iff, internalZero_iff,
    OrdinarySphere6984Literal.eval_expression, OrdinarySphere7084Literal.eval_expression,
    OrdinarySphere6984Literal.value_eq70]
end Model

theorem bridge69 : PolynomialBridge
    (positiveShift (OrdinarySphere6984Literal.expressionAt CurrentWindowCarry2011.ports)) := by
  intro V _ _
  have eqv : (classicalNoZero (positiveShift
      (OrdinarySphere6984Literal.expressionAt CurrentWindowCarry2011.ports))).Evalb (M := V) ![] ↔
      (classicalNoZero (positiveShift
      (OrdinarySphere7084Literal.expressionAt CurrentWindowCarry2011.ports))).Evalb (M := V) ![] := by
    rw [classicalNoZero_iff, classicalNoZero_iff]
    simpa only [InternalZero, ne_eq] using
      (forall_congr' fun v : Fin 14 → V => not_congr (sameZero70 v))
  exact eqv.trans (OrdinarySphere7084IPRA.bridge70 V)

theorem native_equivalence69 : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero
      (positiveShift (OrdinarySphere6984Literal.expressionAt CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ bridge69

theorem standard_equivalence69 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero
      (positiveShift (OrdinarySphere6984Literal.expressionAt CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence69

theorem standard_translated_equivalence69 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero
      (positiveShift (OrdinarySphere6984Literal.expressionAt CurrentWindowCarry2011.ports)) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ := by
  apply (IPRAStandardTheory.provable_iff _).2
  obtain ⟨h⟩ := native_equivalence69
  have z := IPRABoundedRhoZFC.zfcEquiv
  exact ⟨Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z))
    (Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h))⟩

#print axioms sameZero70
#print axioms bridge69
#print axioms standard_equivalence69
#print axioms standard_translated_equivalence69
end DiophantineConsistency.OrdinarySphere6984IPRA
