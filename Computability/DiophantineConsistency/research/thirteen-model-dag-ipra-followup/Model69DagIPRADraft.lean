import Model69EndpointBindingDraft
import DiophantineConsistency.IPRABoundedRhoZFC

/-! Source-only proposed bridge from the semantic 69-node binding to iPRA.
This draft has not been compiled or checked against a completed successor. -/
set_option autoImplicit false
noncomputable section
namespace Model69DagIPRADraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 HAExpressionNoZeroEquiv
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open FoundationZFCConsistencyNat

/-- The exact shifted 69-node literal and the new endpoint expression have
the same no-zero predicate in every model of IΣ₁. -/
theorem sameNoZeroDag : SameNoZero Thirteen69Cuts.currentLiteral
    (positiveShift (ModelThirteenCarrier.expressionAt69 CurrentWindowCarry2011.ports)) := by
  intro V _ _
  constructor
  · intro h v hz
    apply h v
    exact (Model69EndpointBindingDraft.shifted_zero_equal CurrentWindowCarry2011.ports v).mp hz
  · intro h v hz
    apply h v
    exact (Model69EndpointBindingDraft.shifted_zero_equal CurrentWindowCarry2011.ports v).mpr hz

/-- Transfer the existing polynomial bridge to the exact 69-node syntax. -/
theorem bridgeDag : HAExpressionAssembly.PolynomialBridge Thirteen69Cuts.currentLiteral :=
  HAExpressionNoZeroEquiv.bridge _ _ sameNoZeroDag ModelThirteenCarrier.bridge69

theorem native_equivalenceDag : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero Thirteen69Cuts.currentLiteral 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ bridgeDag

theorem standard_equivalenceDag : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero Thirteen69Cuts.currentLiteral 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalenceDag

theorem reference_equivalenceDag : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero Thirteen69Cuts.currentLiteral) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  IPRAReferenceInductionConversion.nativeToReference native_equivalenceDag
/-- Standard iPRA with the Gödel–Gentzen image of Foundation's selected
ZFC consistency sentence on the right-hand side. -/
theorem standard_translated_consistencyDag : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero Thirteen69Cuts.currentLiteral 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ := by
  apply (IPRAStandardTheory.provable_iff _).2
  obtain ⟨h⟩ := native_equivalenceDag
  have z := IPRABoundedRhoZFC.zfcEquiv
  exact ⟨Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z))
    (Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h))⟩

end Model69DagIPRADraft
#print axioms Model69DagIPRADraft.sameNoZeroDag
#print axioms Model69DagIPRADraft.bridgeDag
#print axioms Model69DagIPRADraft.native_equivalenceDag
#print axioms Model69DagIPRADraft.standard_equivalenceDag
#print axioms Model69DagIPRADraft.reference_equivalenceDag
#print axioms Model69DagIPRADraft.standard_translated_consistencyDag
