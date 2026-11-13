import DiophantineConsistency.Sign26DirectNative
import DiophantineConsistency.IPRAStandardTheory

/-! SOURCE-ONLY UNCOMPILED standard iPRA endpoint. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign26DirectIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing PRALanguage IPRANativeTheory
  IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat

theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence
end DiophantineConsistency.Sign26DirectIPRA
#print axioms DiophantineConsistency.Sign26DirectIPRA.standard_equivalence
