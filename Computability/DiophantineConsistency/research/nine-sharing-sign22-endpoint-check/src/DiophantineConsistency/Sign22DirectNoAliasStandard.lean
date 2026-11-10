import DiophantineConsistency.Sign22DirectNoAliasNative
import DiophantineConsistency.IPRAStandardTheory

/-! SOURCE-ONLY candidate: standard iPRA endpoint. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign22DirectNoAlias
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing PRALanguage IPRANativeTheory
  IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat

attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign22CurrentExpression.expression SharingSeed22Dodecic.seed
  CurrentWindowCarry2011.ports IPRAExpressionNative.nativeNoZero

theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero Sign22CurrentExpression.expression 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence
end DiophantineConsistency.Sign22DirectNoAlias
#print axioms DiophantineConsistency.Sign22DirectNoAlias.standard_equivalence
