import DiophantineConsistency.IPRAReferenceInductionConversion
import DiophantineConsistency.IPRAAQ29Native

/-! Exploratory fixed AQ29 endpoint transported to the equality-only theory.
The erasure is explicit; separate identification of its consistency formula
with a standard reference-language coding and a coherent replay are required. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAReferenceAQ29
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open IPRAOrderErasure IPRAEqualityOnlyReference IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

theorem literal_equivalence : referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero
      (positiveShift (AdaptiveAQ29Literal.literal CurrentWindowCarry2011.ports))) 🡘
      ∼(erase (mappedNativeRefutation PRALanguage.embedding)) := by
  have h := IPRAReferenceInductionConversion.nativeToReference IPRAAQ29Native.literal_equivalence
  simpa only [LogicalConnective.iff, Semiformulaᵢ.neg_def, erase] using h

#print axioms literal_equivalence
end DiophantineConsistency.IPRAReferenceAQ29
