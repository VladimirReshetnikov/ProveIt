import DiophantineConsistency.Sign14Positive74IPRABridge
import DiophantineConsistency.IPRAExpressionNative
import DiophantineConsistency.IPRAStandardTheory

/-! SOURCE-ONLY: native and standard iPRA endpoints for optimized expression. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74IPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing PRALanguage IPRANativeTheory
  IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat

attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  CurrentWindowCarry2011.ports IPRAExpressionNative.nativeNoZero

theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (Sign14Positive74.expression CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ polynomialBridge

theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (Sign14Positive74.expression CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence

theorem standard_translated_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (Sign14Positive74.expression CurrentWindowCarry2011.ports)) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ := by
  apply (IPRAStandardTheory.provable_iff _).2
  obtain ⟨h⟩ := (IPRAStandardTheory.provable_iff _).1 standard_equivalence
  have z := IPRABoundedRhoZFC.zfcEquiv
  exact ⟨Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z))
    (Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h))⟩
end DiophantineConsistency.Sign14Positive74IPRA
#print axioms DiophantineConsistency.Sign14Positive74IPRA.native_equivalence
#print axioms DiophantineConsistency.Sign14Positive74IPRA.standard_equivalence
#print axioms DiophantineConsistency.Sign14Positive74IPRA.standard_translated_equivalence
