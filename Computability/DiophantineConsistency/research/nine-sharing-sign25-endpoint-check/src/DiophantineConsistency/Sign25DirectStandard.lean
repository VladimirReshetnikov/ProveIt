import DiophantineConsistency.Sign25DirectNative
import DiophantineConsistency.IPRAStandardTheory

/-! SOURCE-ONLY UNCOMPILED standard iPRA endpoint. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign25DirectIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing PRALanguage IPRANativeTheory
  IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat

theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence
end DiophantineConsistency.Sign25DirectIPRA
#print axioms DiophantineConsistency.Sign25DirectIPRA.standard_equivalence
