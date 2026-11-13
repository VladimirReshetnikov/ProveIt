import DiophantineConsistency.ModelJonesNine
import DiophantineConsistency.ModelProgramLink
import DiophantineConsistency.ModelRepFinal

/-! # Unconditional iPRA endpoints for the nine-variable `ExplicitZFC` equation

`IPRAExplicitZFCReduction` derives native, standard and equality-only iPRA
equivalences between the no-zero sentence of `ExplicitZFCSyntax.expression`
(`= ExplicitZFC.expression`, by `ExplicitZFC.expression_eq_syntax`) and the
selected Foundation ZFC consistency predicate from two model obligations.
Both are now theorems:

* `JonesModel` — `ModelJonesNine.jonesModel` (Jones's nine unknowns inside
  every model of `𝗜𝚺₁`);
* `SourceModel` — `ModelProgramLink.sourceModel`, from the internal
  correctness of the compiled scalar primitive recursive program
  (`ModelRepFinal.precCase`: Gödel's β-function and the bounded-quantifier
  certificate, with Matiyasevich's Pell criterion inside the model) and the
  link between the enumerator program and the internal C222 machine. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAExplicitZFCFinal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation

theorem sourceModel : IPRAExplicitZFCReduction.SourceModel :=
  ModelProgramLink.sourceModel ModelRepFinal.precCase

/-- **Native iPRA: the nine-variable equation has no zero iff ZFC is consistent.** -/
theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero ExplicitZFCSyntax.expression 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExplicitZFCReduction.native_equivalence ModelJonesNine.jonesModel sourceModel

/-- **Standard iPRA.** -/
theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero ExplicitZFCSyntax.expression 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExplicitZFCReduction.standard_equivalence ModelJonesNine.jonesModel sourceModel

/-- **Equality-only iPRA.** -/
theorem reference_equivalence : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero ExplicitZFCSyntax.expression) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  IPRAExplicitZFCReduction.reference_equivalence ModelJonesNine.jonesModel sourceModel

#print axioms sourceModel
#print axioms native_equivalence
#print axioms standard_equivalence
#print axioms reference_equivalence

end DiophantineConsistency.IPRAExplicitZFCFinal
