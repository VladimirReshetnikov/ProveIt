import DiophantineConsistency.IPRAStandardTheory
import DiophantineConsistency.IPRAAQ16Native
import DiophantineConsistency.IPRABoundedRhoZFC

/-! Exploratorily compiled endpoint client for the same-language standard presentation.
The imported AQ16 and standard-theory statements require coherent replay.
The consistency sentence is Foundation's selected sentence after the
language map and Gödel–Gentzen translation. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAStandardAQ16
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRAStandardTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

theorem literal_equivalence : standardTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveAQ16Literal.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  (provable_iff _).2 IPRAAQ16Native.literal_equivalence

theorem selected_foundation_consistency : standardTheory ⊢
    (Semiformula.lMap embedding FoundationZFCConsistencyNat.sourceSentence)ᴺ 🡘
      ∼mappedNativeRefutation embedding :=
  (provable_iff _).2 ⟨IPRABoundedRhoZFC.zfcEquiv⟩

theorem literal_iff_translated_consistency : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero
      (positiveShift (AdaptiveAQ16Literal.literal CurrentWindowCarry2011.ports)) 🡘
        (Semiformula.lMap embedding FoundationZFCConsistencyNat.sourceSentence)ᴺ :=
  Entailment.E!_trans literal_equivalence
    (Entailment.E!_symm selected_foundation_consistency)

#print axioms literal_equivalence
#print axioms selected_foundation_consistency
#print axioms literal_iff_translated_consistency
end DiophantineConsistency.IPRAStandardAQ16
