import DiophantineConsistency.PRAWitnessZFCStrictComparison
import DiophantineConsistency.HACurrentEquation2011
import DiophantineConsistency.FoundationHAConsistencyNormalization

/-! The literal maintained 14-variable equation and Foundation ZFC
consistency in the repository's candidate PRA. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.PRACurrentZFCStrict
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRANoZeroUnary FoundationHANoZero ObjectCurrentEquation2011
  FoundationHAConsistencyNormalization PRAWitnessZFCRefutationBound

theorem current_equivalence : PRA ⊢
    (Semiformula.lMap embedding FoundationHACurrentNoZero2011.classicalSentence 🡘
      Semiformula.lMap embedding FoundationZFCConsistencyNat.sourceSentence) := by
  have h : 𝗜𝚺₁ ⊢
      (noZero 14
        (sourceTerm 14 (ArithmeticExpression.term Fin.val naturalExpression.splitNatural.1))
        (sourceTerm 14 (ArithmeticExpression.term Fin.val naturalExpression.splitNatural.2)) 🡘 ∼refutation) := by
    simpa only [noZero, FoundationHACurrentNoZero2011.classicalSentence, classicalNoZero,
      source_eq_neg_rho, rho, refutation] using HACurrentEquation2011.isigma1_proves_current_iff_consistency
  have hp := PRAWitnessZFCStrictComparison.comparison 14
    (sourceTerm 14 (ArithmeticExpression.term Fin.val naturalExpression.splitNatural.1))
    (sourceTerm 14 (ArithmeticExpression.term Fin.val naturalExpression.splitNatural.2)) h
  simpa only [noZero, FoundationHACurrentNoZero2011.classicalSentence, classicalNoZero,
    source_eq_neg_rho, rho, refutation] using hp
end DiophantineConsistency.PRACurrentZFCStrict
