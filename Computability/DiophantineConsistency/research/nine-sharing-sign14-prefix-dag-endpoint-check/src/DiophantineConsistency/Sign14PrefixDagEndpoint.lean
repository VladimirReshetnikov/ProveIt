import DiophantineConsistency.Sign14PrefixDagDegree
import DiophantineConsistency.Sign14DirectNoAliasTranslated

/-! SOURCE-ONLY: transfer the iPRA endpoints to the fragment-DAG expression. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDagCurrent
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing PRALanguage IPRANativeTheory
  IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat

attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign14CurrentExpression.expression SharingSeed14Degree124.seed
  CurrentWindowCarry2011.ports IPRAExpressionNative.nativeNoZero

theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding := by
  rw [expression_eq]
  exact Sign14DirectNoAlias.native_equivalence

theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding := by
  rw [expression_eq]
  exact Sign14DirectNoAlias.standard_equivalence

theorem standard_translated_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero expression 🡘 (Semiformula.lMap embedding sourceSentence)ᴺ := by
  rw [expression_eq]
  exact Sign14DirectNoAlias.standard_translated_equivalence
end DiophantineConsistency.Sign14PrefixDagCurrent
#print axioms DiophantineConsistency.Sign14PrefixDagCurrent.native_equivalence
#print axioms DiophantineConsistency.Sign14PrefixDagCurrent.standard_equivalence
#print axioms DiophantineConsistency.Sign14PrefixDagCurrent.standard_translated_equivalence
