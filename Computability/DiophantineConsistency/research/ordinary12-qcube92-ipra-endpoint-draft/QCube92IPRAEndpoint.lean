import QCube92Halt
import PositiveModelIPRAReferenceTranslated

/-! Unchecked proposed iPRA clients for the 92-operation model bridge.
The imports first require a coherent, guarded provider and a checked join. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace QCube92IPRAEndpoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 CompactSymbolicModelIff CompactBytePortsModelIff
open FreeJQCube92 FreeJQCube92Halt PositiveModelIPRAAdapter
open PositiveModelIPRAStandardAdapter PositiveModelIPRAReferenceTranslated
open PRALanguage IPRAStandardTheory IPRAEqualityOnlyReference IPRAOrderErasure
open IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat

theorem positive_bridge : PositiveModelBridge (graph p).output := by
  intro V _ _
  exact FreeJQCube92Halt.positive_model_iff

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

#print axioms QCube92IPRAEndpoint.positive_bridge
#print axioms QCube92IPRAEndpoint.byte_positive_bridge
#print axioms QCube92IPRAEndpoint.standard_consistency
#print axioms QCube92IPRAEndpoint.standard_translated_consistency
#print axioms QCube92IPRAEndpoint.reference_consistency
#print axioms QCube92IPRAEndpoint.reference_translated_consistency
end QCube92IPRAEndpoint
