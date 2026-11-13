import Absorb89Halt
import PositiveModelIPRAReferenceTranslated

/-! Unchecked proposed iPRA clients for the 89-operation model bridge.
The imports first require a coherent, guarded provider and a checked join. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Absorb89IPRAEndpoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 CompactSymbolicModelIff CompactBytePortsModelIff
open FreeJAbsorb89 Absorb89Halt PositiveModelIPRAAdapter
open PositiveModelIPRAStandardAdapter PositiveModelIPRAReferenceTranslated
open PRALanguage IPRAStandardTheory IPRAEqualityOnlyReference IPRAOrderErasure
open IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat

theorem positive_bridge : PositiveModelBridge (graph p).output := by
  intro V _ _
  exact Absorb89Halt.positive_model_iff

theorem byte_positive_bridge : PositiveModelBridge (graph byteP).output := by
  rw [byteP_eq]
  exact positive_bridge

theorem standard_consistency : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (graph byteP).output) 🡘
      ∼mappedNativeRefutation embedding :=
  standard_equivalence_of_positive _ byte_positive_bridge

theorem standard_translated_consistency : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (graph byteP).output) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ :=
  standard_translated_of_positive _ byte_positive_bridge

theorem reference_consistency : referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero (positiveShift (graph byteP).output)) 🡘
      ∼erase (mappedNativeRefutation embedding) :=
  reference_equivalence_of_positive _ byte_positive_bridge

theorem reference_translated_consistency : referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero (positiveShift (graph byteP).output)) 🡘
      erase ((Semiformula.lMap embedding sourceSentence)ᴺ) :=
  reference_translated_of_positive _ byte_positive_bridge

#print axioms Absorb89IPRAEndpoint.positive_bridge
#print axioms Absorb89IPRAEndpoint.byte_positive_bridge
#print axioms Absorb89IPRAEndpoint.standard_consistency
#print axioms Absorb89IPRAEndpoint.standard_translated_consistency
#print axioms Absorb89IPRAEndpoint.reference_consistency
#print axioms Absorb89IPRAEndpoint.reference_translated_consistency
end Absorb89IPRAEndpoint
