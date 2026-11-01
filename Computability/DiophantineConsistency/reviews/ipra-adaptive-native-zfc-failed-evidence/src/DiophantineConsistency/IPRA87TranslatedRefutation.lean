import DiophantineConsistency.IPRAFullGGTransfer
import DiophantineConsistency.PRA87ZFCStrict
/-! The literal 13-variable 87-operation equation in the native intuitionistic candidate,
compared with the negated GG translation of the actual refutation predicate.
Identifying that predicate with ordinary native consistency is separate. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRA87TranslatedRefutation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRANoZeroUnary FoundationHANoZero
  FoundationHAConsistencyNormalization PRAWitnessZFCRefutationBound
  IPRANativeTheory IPRAFullGGTransfer

theorem translated_refutation : nativeTheory ⊢
    (∀⁰* (∼(Semiformulaᵢ.rel Language.ORing.Rel.eq
      ![Semiterm.lMap embedding (sourceTerm 13 (ArithmeticExpression.term Fin.val AdaptiveFirstRootFactor87Literal.naturalExpression87.splitNatural.1)),
        Semiterm.lMap embedding (sourceTerm 13 (ArithmeticExpression.term Fin.val AdaptiveFirstRootFactor87Literal.naturalExpression87.splitNatural.2))]))) 🡘
    ∼(Semiformula.lMap embedding refutation)ᴺ := by
  have h : PRA ⊢
      (Semiformula.lMap embedding (noZero 13
        (sourceTerm 13 (ArithmeticExpression.term Fin.val AdaptiveFirstRootFactor87Literal.naturalExpression87.splitNatural.1))
        (sourceTerm 13 (ArithmeticExpression.term Fin.val AdaptiveFirstRootFactor87Literal.naturalExpression87.splitNatural.2))) 🡘
       ∼(Semiformula.lMap embedding refutation)) := by
    simpa only [noZero, classicalNoZero,
      source_eq_neg_rho, rho, refutation, LogicalConnective.HomClass.map_neg] using
      PRA87ZFCStrict.equivalence
  have ht := IPRAConditionalComparison.translated_comparison axiom_images
    (Semiformula.lMap embedding (noZero 13
      (sourceTerm 13 (ArithmeticExpression.term Fin.val AdaptiveFirstRootFactor87Literal.naturalExpression87.splitNatural.1))
      (sourceTerm 13 (ArithmeticExpression.term Fin.val AdaptiveFirstRootFactor87Literal.naturalExpression87.splitNatural.2))))
    (Semiformula.lMap embedding refutation) h
  simpa only [IPRAMappedNoZero.mapped_gg_noZero] using ht
end DiophantineConsistency.IPRA87TranslatedRefutation
