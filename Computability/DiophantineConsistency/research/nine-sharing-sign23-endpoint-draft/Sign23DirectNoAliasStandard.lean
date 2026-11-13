import DiophantineConsistency.Sign23DirectNoAliasNative
import DiophantineConsistency.IPRAStandardTheory

/-! SOURCE-ONLY candidate: standard iPRA endpoint. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign23DirectNoAlias
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing PRALanguage IPRANativeTheory
  IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat

attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign23CurrentExpression.expression SharingSeed23Octic.seed
  CurrentWindowCarry2011.ports IPRAExpressionNative.nativeNoZero

theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero Sign23CurrentExpression.expression 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence
end DiophantineConsistency.Sign23DirectNoAlias
#print axioms DiophantineConsistency.Sign23DirectNoAlias.standard_equivalence
