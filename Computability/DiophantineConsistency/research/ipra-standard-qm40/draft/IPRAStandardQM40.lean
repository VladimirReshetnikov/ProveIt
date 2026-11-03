import DiophantineConsistency.IPRAStandardTheory
import DiophantineConsistency.IPRAQM40Native
import DiophantineConsistency.IPRABoundedRhoZFC

/-! Uncompiled standard-presentation client for the proposed QM40 endpoint.
The imported native and standard-theory providers require a coherent build. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAStandardQM40
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRAStandardTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

theorem literal_equivalence : standardTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveQM40Context.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  (provable_iff _).2 IPRAQM40Native.literal_equivalence

theorem selected_foundation_consistency : standardTheory ⊢
    (Semiformula.lMap embedding FoundationZFCConsistencyNat.sourceSentence)ᴺ 🡘
      ∼mappedNativeRefutation embedding :=
  (provable_iff _).2 ⟨IPRABoundedRhoZFC.zfcEquiv⟩

theorem literal_iff_translated_consistency : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero
      (positiveShift (AdaptiveQM40Context.literal CurrentWindowCarry2011.ports)) 🡘
        (Semiformula.lMap embedding FoundationZFCConsistencyNat.sourceSentence)ᴺ :=
  Entailment.E!_trans literal_equivalence
    (Entailment.E!_symm selected_foundation_consistency)

#print axioms literal_equivalence
#print axioms selected_foundation_consistency
#print axioms literal_iff_translated_consistency
end DiophantineConsistency.IPRAStandardQM40
