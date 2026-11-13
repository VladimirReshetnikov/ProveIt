import DiophantineConsistency.Sign14DirectNoAliasNative
import DiophantineConsistency.IPRAStandardTheory

/-! SOURCE-ONLY candidate: standard iPRA endpoint. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14DirectNoAlias
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing PRALanguage IPRANativeTheory
  IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat

attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign14CurrentExpression.expression SharingSeed14Degree124.seed
  CurrentWindowCarry2011.ports IPRAExpressionNative.nativeNoZero

theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero Sign14CurrentExpression.expression 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence
end DiophantineConsistency.Sign14DirectNoAlias
#print axioms DiophantineConsistency.Sign14DirectNoAlias.standard_equivalence
