import DiophantineConsistency.IPRAReferenceAQ29
import DiophantineConsistency.IPRAReferenceNoZero
import DiophantineConsistency.IPRAReferenceRefutationReading

/-! Uncompiled assembly of three uncompiled drafts. This states the endpoint
using the separately defined equality-only no-zero formula and the direct
reader of the *same* Foundation ZFC refutation formula. It makes no claim
about other ZFC proof codings or any completed Lean verification. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAReferenceAQ29Direct
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open IPRAEqualityOnlyReference AdaptiveEquationSyntax2011

theorem literal_equivalence : referenceTheory ⊢
    IPRAReferenceNoZero.noZero
      (positiveShift (AdaptiveAQ29Literal.literal CurrentWindowCarry2011.ports)) 🡘
      ∼IPRAReferenceRefutationReading.refutation := by
  rw [← IPRAReferenceNoZero.erase_nativeNoZero,
    IPRAReferenceRefutationReading.refutation_eq_erased_native]
  exact IPRAReferenceAQ29.literal_equivalence

end DiophantineConsistency.IPRAReferenceAQ29Direct
