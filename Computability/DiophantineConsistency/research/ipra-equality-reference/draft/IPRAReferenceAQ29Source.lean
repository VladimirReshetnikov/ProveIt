import DiophantineConsistency.IPRAReferenceAQ29Direct
import DiophantineConsistency.IPRAReferenceSourceConsistency

/-! Uncompiled assembly: the direct equality-only AQ29 no-zero sentence is
compared to the erased GG reading of Foundation's selected Con(ZFC). The
underlying endpoint and theory-transfer drafts still require coherent replay. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAReferenceAQ29Source
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open IPRAEqualityOnlyReference AdaptiveEquationSyntax2011

local instance : IPRAEqualityOnlyReference.language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (EqualityRel k); infer_instance

theorem literal_equivalence : referenceTheory ⊢
    IPRAReferenceNoZero.noZero
      (positiveShift (AdaptiveAQ29Literal.literal CurrentWindowCarry2011.ports)) 🡘
      IPRAReferenceSourceConsistency.translatedSource := by
  have he : referenceTheory ⊢
      IPRAReferenceNoZero.noZero
        (positiveShift (AdaptiveAQ29Literal.literal CurrentWindowCarry2011.ports)) 🡘
        ∼(IPRAOrderErasure.erase
          (IPRAFoundationZFCMappedNegation.mappedNativeRefutation PRALanguage.embedding)) := by
    simpa only [IPRAReferenceRefutationReading.refutation_eq_erased_native] using
      IPRAReferenceAQ29Direct.literal_equivalence
  exact Entailment.E!_trans he (Entailment.E!_symm IPRAReferenceSourceConsistency.equivalence)

end DiophantineConsistency.IPRAReferenceAQ29Source
