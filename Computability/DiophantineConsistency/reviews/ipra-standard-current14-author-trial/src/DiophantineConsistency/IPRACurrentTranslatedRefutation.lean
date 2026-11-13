import DiophantineConsistency.IPRAFullGGTransfer
import DiophantineConsistency.PRACurrentZFCStrict
/-! The literal 14-variable equation in the native intuitionistic candidate,
compared with the negated GG translation of the actual refutation predicate.
Identifying that predicate with ordinary native consistency is separate. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRACurrentTranslatedRefutation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRANoZeroUnary FoundationHANoZero ObjectCurrentEquation2011
  FoundationHAConsistencyNormalization PRAWitnessZFCRefutationBound
  IPRANativeTheory IPRAFullGGTransfer

theorem current_translated_refutation : nativeTheory ⊢
    (∀⁰* (∼(Semiformulaᵢ.rel Language.ORing.Rel.eq
      ![Semiterm.lMap embedding (sourceTerm 14 (ArithmeticExpression.term Fin.val naturalExpression.splitNatural.1)),
        Semiterm.lMap embedding (sourceTerm 14 (ArithmeticExpression.term Fin.val naturalExpression.splitNatural.2))]))) 🡘
    ∼(Semiformula.lMap embedding refutation)ᴺ := by
  have h : PRA ⊢
      (Semiformula.lMap embedding (noZero 14
        (sourceTerm 14 (ArithmeticExpression.term Fin.val naturalExpression.splitNatural.1))
        (sourceTerm 14 (ArithmeticExpression.term Fin.val naturalExpression.splitNatural.2))) 🡘
       ∼(Semiformula.lMap embedding refutation)) := by
    simpa only [noZero, FoundationHACurrentNoZero2011.classicalSentence, classicalNoZero,
      source_eq_neg_rho, rho, refutation, LogicalConnective.HomClass.map_neg] using
      PRACurrentZFCStrict.current_equivalence
  have ht := IPRAConditionalComparison.translated_comparison axiom_images
    (Semiformula.lMap embedding (noZero 14
      (sourceTerm 14 (ArithmeticExpression.term Fin.val naturalExpression.splitNatural.1))
      (sourceTerm 14 (ArithmeticExpression.term Fin.val naturalExpression.splitNatural.2))))
    (Semiformula.lMap embedding refutation) h
  simpa only [IPRAMappedNoZero.mapped_gg_noZero] using ht
end DiophantineConsistency.IPRACurrentTranslatedRefutation
