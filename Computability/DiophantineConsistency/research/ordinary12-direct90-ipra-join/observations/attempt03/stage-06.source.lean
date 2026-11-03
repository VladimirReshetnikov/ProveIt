import PositiveModelIPRAAdapter
import DiophantineConsistency.IPRAStandardTheory
import DiophantineConsistency.IPRAReferenceInductionConversion

/-! Conditional standard and equality-only iPRA endpoints for a positive
    all-model bridge. No particular expression's bridge is assumed here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PositiveModelIPRAStandardAdapter
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 PositiveModelIPRAAdapter
open PRALanguage IPRAStandardTheory IPRAEqualityOnlyReference IPRAOrderErasure
open IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat

theorem standard_equivalence_of_positive {n : ℕ} (e : Expr (Fin n))
    (hp : PositiveModelBridge e) : standardTheory ⊢
      IPRAExpressionNative.nativeNoZero (positiveShift e) 🡘
        ∼mappedNativeRefutation embedding :=
  (provable_iff _).2 (native_equivalence_of_positive e hp)

theorem standard_translated_of_positive {n : ℕ} (e : Expr (Fin n))
    (hp : PositiveModelBridge e) : standardTheory ⊢
      IPRAExpressionNative.nativeNoZero (positiveShift e) 🡘
        (Semiformula.lMap embedding sourceSentence)ᴺ := by
  apply (provable_iff _).2
  obtain ⟨h⟩ := native_equivalence_of_positive e hp
  have z := IPRABoundedRhoZFC.zfcEquiv
  exact ⟨Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z))
    (Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h))⟩

theorem reference_equivalence_of_positive {n : ℕ} (e : Expr (Fin n))
    (hp : PositiveModelBridge e) : referenceTheory ⊢
      erase (IPRAExpressionNative.nativeNoZero (positiveShift e)) 🡘
        ∼erase (mappedNativeRefutation embedding) :=
  IPRAReferenceInductionConversion.nativeToReference
    (native_equivalence_of_positive e hp)

#print axioms PositiveModelIPRAStandardAdapter.standard_equivalence_of_positive
#print axioms PositiveModelIPRAStandardAdapter.standard_translated_of_positive
#print axioms PositiveModelIPRAStandardAdapter.reference_equivalence_of_positive
end PositiveModelIPRAStandardAdapter
