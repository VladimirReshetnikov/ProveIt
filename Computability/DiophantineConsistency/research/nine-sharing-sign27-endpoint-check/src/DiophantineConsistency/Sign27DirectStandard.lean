import DiophantineConsistency.Sign27DirectNative
import DiophantineConsistency.IPRAStandardTheory

/-! SOURCE-ONLY UNCOMPILED standard iPRA endpoint. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign27DirectIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing PRALanguage IPRANativeTheory
  IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat

theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence
end DiophantineConsistency.Sign27DirectIPRA
#print axioms DiophantineConsistency.Sign27DirectIPRA.standard_equivalence
