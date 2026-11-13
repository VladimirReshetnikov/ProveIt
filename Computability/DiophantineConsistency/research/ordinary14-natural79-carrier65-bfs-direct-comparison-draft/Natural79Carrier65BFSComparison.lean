import Natural79Endpoint
import DiophantineConsistency.BFS943.IPRACarrier65BFS943
import DiophantineConsistency.IPRAReferenceInductionConversion

/-! Source-only proposed composition of two endpoint statements. Neither this
file nor the selected natural-79 endpoint has been checked by Lean in this
packet. Carrier65 is at the direct BFS943 ports, with positive variables
encoded by `positiveShift`. No file/PDF coefficient binding is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Natural79Carrier65BFSComparisonDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open FoundationZFCConsistencyNat

/-- The two explicit input proofs must concern the same native theory and the
same mapped refutation. Intuitionistic biconditional transitivity then gives a
proof of no-zero equivalence in that theory. -/
theorem native_of_endpoints
    (h79 : nativeTheory ⊢
      IPRAExpressionNative.nativeNoZero Natural79EndpointDraft.expression 🡘
        ∼mappedNativeRefutation embedding)
    (h65 : nativeTheory ⊢
      IPRAExpressionNative.nativeNoZero (positiveShift IPRACarrier65BFS943.expression) 🡘
        ∼mappedNativeRefutation embedding) :
    nativeTheory ⊢
      IPRAExpressionNative.nativeNoZero Natural79EndpointDraft.expression 🡘
        IPRAExpressionNative.nativeNoZero (positiveShift IPRACarrier65BFS943.expression) := by
  obtain ⟨a⟩ := h79
  obtain ⟨b⟩ := h65
  exact ⟨Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left a) (Entailment.K_right b))
    (Entailment.C_trans (Entailment.K_left b) (Entailment.K_right a))⟩

/-- Proposed application of the two source declarations. This declaration is
only as established as its unelaborated endpoint imports and this draft. -/
theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero Natural79EndpointDraft.expression 🡘
      IPRAExpressionNative.nativeNoZero (positiveShift IPRACarrier65BFS943.expression) :=
  native_of_endpoints Natural79EndpointDraft.native_equivalence
    IPRACarrier65BFS943.native_equivalence

/-- The same natural-79 no-zero sentence against the selected Foundation
consistency sentence after the repository's native translation. -/
theorem native_translated_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero Natural79EndpointDraft.expression 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ := by
  obtain ⟨h⟩ := Natural79EndpointDraft.native_equivalence
  have z := IPRABoundedRhoZFC.zfcEquiv
  exact ⟨Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z))
    (Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h))⟩

theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero Natural79EndpointDraft.expression 🡘
      IPRAExpressionNative.nativeNoZero (positiveShift IPRACarrier65BFS943.expression) :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence

theorem reference_equivalence : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero Natural79EndpointDraft.expression) 🡘
      IPRAOrderErasure.erase
        (IPRAExpressionNative.nativeNoZero (positiveShift IPRACarrier65BFS943.expression)) :=
  IPRAReferenceInductionConversion.nativeToReference native_equivalence

theorem standard_translated_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero Natural79EndpointDraft.expression 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ :=
  (IPRAStandardTheory.provable_iff _).2 native_translated_equivalence

theorem reference_translated_equivalence : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero Natural79EndpointDraft.expression) 🡘
      IPRAOrderErasure.erase ((Semiformula.lMap embedding sourceSentence)ᴺ) :=
  IPRAReferenceInductionConversion.nativeToReference native_translated_equivalence

end DiophantineConsistency.Natural79Carrier65BFSComparisonDraft

#print axioms DiophantineConsistency.Natural79Carrier65BFSComparisonDraft.native_of_endpoints
#print axioms DiophantineConsistency.Natural79Carrier65BFSComparisonDraft.native_equivalence
#print axioms DiophantineConsistency.Natural79Carrier65BFSComparisonDraft.native_translated_equivalence
#print axioms DiophantineConsistency.Natural79Carrier65BFSComparisonDraft.standard_equivalence
#print axioms DiophantineConsistency.Natural79Carrier65BFSComparisonDraft.reference_equivalence
#print axioms DiophantineConsistency.Natural79Carrier65BFSComparisonDraft.standard_translated_equivalence
#print axioms DiophantineConsistency.Natural79Carrier65BFSComparisonDraft.reference_translated_equivalence
