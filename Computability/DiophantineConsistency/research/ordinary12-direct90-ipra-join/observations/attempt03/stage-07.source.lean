import PositiveModelIPRAStandardAdapter

/-! Conditional equality-only endpoint for the translated consistency sentence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PositiveModelIPRAReferenceTranslated
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 PositiveModelIPRAAdapter
open PRALanguage IPRAEqualityOnlyReference IPRAOrderErasure
open IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat

theorem reference_translated_of_positive {n : ℕ} (e : Expr (Fin n))
    (hp : PositiveModelBridge e) : referenceTheory ⊢
      erase (IPRAExpressionNative.nativeNoZero (positiveShift e)) 🡘
        erase ((Semiformula.lMap embedding sourceSentence)ᴺ) := by
  refine IPRAReferenceInductionConversion.nativeToReference
    (σ := IPRAExpressionNative.nativeNoZero (positiveShift e) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ) ?_
  obtain ⟨h⟩ := native_equivalence_of_positive e hp
  have z := IPRABoundedRhoZFC.zfcEquiv
  exact ⟨Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z))
    (Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h))⟩

#print axioms PositiveModelIPRAReferenceTranslated.reference_translated_of_positive
end PositiveModelIPRAReferenceTranslated
