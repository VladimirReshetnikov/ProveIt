import DiophantineConsistency.Thirteen75Cuts
import DiophantineConsistency.IPRABoundedRhoZFC

/-! Proposed iPRA transfer for the exact 75-node degree-96 candidate. -/
set_option autoImplicit false
noncomputable section
namespace Model75DagIPRADraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 HAExpressionNoZeroEquiv
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open FoundationZFCConsistencyNat

/-- The exact shifted 75-node literal and the new endpoint expression have
the same no-zero predicate in every model of IΣ₁. -/
theorem sameNoZeroDag : SameNoZero Thirteen75Cuts.currentLiteral
    (positiveShift (ModelThirteenSquares.expressionAt75 CurrentWindowCarry2011.ports)) := by
  intro V _ _
  constructor
  · intro h v hz
    apply h v
    exact (Thirteen75Cuts.shifted_zero_equal CurrentWindowCarry2011.ports v).mpr hz
  · intro h v hz
    apply h v
    exact (Thirteen75Cuts.shifted_zero_equal CurrentWindowCarry2011.ports v).mp hz

/-- Transfer the existing polynomial bridge to the exact 75-node syntax. -/
theorem bridgeDag : HAExpressionAssembly.PolynomialBridge Thirteen75Cuts.currentLiteral :=
  HAExpressionNoZeroEquiv.bridge _ _ sameNoZeroDag ModelThirteenSquares.bridge75

theorem native_equivalenceDag : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero Thirteen75Cuts.currentLiteral 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ bridgeDag

theorem standard_equivalenceDag : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero Thirteen75Cuts.currentLiteral 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalenceDag

theorem reference_equivalenceDag : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero Thirteen75Cuts.currentLiteral) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  IPRAReferenceInductionConversion.nativeToReference native_equivalenceDag
/-- Standard iPRA with the Gödel–Gentzen image of Foundation's selected
ZFC consistency sentence on the right-hand side. -/
theorem standard_translated_consistencyDag : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero Thirteen75Cuts.currentLiteral 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ := by
  apply (IPRAStandardTheory.provable_iff _).2
  obtain ⟨h⟩ := native_equivalenceDag
  have z := IPRABoundedRhoZFC.zfcEquiv
  exact ⟨Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z))
    (Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h))⟩

end Model75DagIPRADraft
#print axioms Model75DagIPRADraft.sameNoZeroDag
#print axioms Model75DagIPRADraft.bridgeDag
#print axioms Model75DagIPRADraft.native_equivalenceDag
#print axioms Model75DagIPRADraft.standard_equivalenceDag
#print axioms Model75DagIPRADraft.reference_equivalenceDag
#print axioms Model75DagIPRADraft.standard_translated_consistencyDag
