import DiophantineConsistency.PRAStrictConComparison
import DiophantineConsistency.HACurrentEquation2011
import DiophantineConsistency.FoundationHAConsistencyNormalization
/-! The maintained equation versus the bounded strict surrogate of Foundation
ZFC consistency. The literal consistency equivalence is a separate obligation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
namespace DiophantineConsistency.PRACurrentStrictCon
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRANoZeroUnary PRAStrictConComparison StrictPiTwoBridge
  FoundationHANoZero ObjectCurrentEquation2011 FoundationHAConsistencyNormalization

theorem comparison : PRA ⊢
    (Semiformula.lMap embedding FoundationHACurrentNoZero2011.classicalSentence 🡘
      Semiformula.lMap embedding (conB rho)) := by
  have h : 𝗜𝚺₁ ⊢
      (noZero 14
        (sourceTerm 14 (ArithmeticExpression.term Fin.val naturalExpression.splitNatural.1))
        (sourceTerm 14 (ArithmeticExpression.term Fin.val naturalExpression.splitNatural.2)) 🡘 ∼rho) := by
    simpa only [noZero, FoundationHACurrentNoZero2011.classicalSentence, classicalNoZero,
      source_eq_neg_rho] using HACurrentEquation2011.isigma1_proves_current_iff_consistency
  simpa only [noZero, FoundationHACurrentNoZero2011.classicalSentence, classicalNoZero] using
    PRAStrictConComparison.comparison 14
      (sourceTerm 14 (ArithmeticExpression.term Fin.val naturalExpression.splitNatural.1))
      (sourceTerm 14 (ArithmeticExpression.term Fin.val naturalExpression.splitNatural.2))
      rho rho_sigma_one h
end DiophantineConsistency.PRACurrentStrictCon
