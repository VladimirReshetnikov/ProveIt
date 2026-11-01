import DiophantineConsistency.PRAWitnessZFCStrictComparison
import DiophantineConsistency.HAAdaptiveDirectOrdinate86
import DiophantineConsistency.FoundationHAConsistencyNormalization
/-! The literal 13-variable 86-operation equation in classical candidate PRA. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.PRA86ZFCStrict
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRANoZeroUnary FoundationHANoZero
  FoundationHAConsistencyNormalization PRAWitnessZFCRefutationBound

attribute [local irreducible] AdaptiveDirectOrdinate86Literal.naturalExpression86

theorem equivalence : PRA ⊢
    (Semiformula.lMap embedding (classicalNoZero AdaptiveDirectOrdinate86Literal.naturalExpression86) 🡘
      Semiformula.lMap embedding FoundationZFCConsistencyNat.sourceSentence) := by
  have hi := HAExpressionAssembly.isigma1_equivalence
    AdaptiveDirectOrdinate86Literal.naturalExpression86 HAAdaptiveDirectOrdinate86.polynomialBridge
  have h : 𝗜𝚺₁ ⊢
      (noZero 13
        (sourceTerm 13 (ArithmeticExpression.term Fin.val AdaptiveDirectOrdinate86Literal.naturalExpression86.splitNatural.1))
        (sourceTerm 13 (ArithmeticExpression.term Fin.val AdaptiveDirectOrdinate86Literal.naturalExpression86.splitNatural.2)) 🡘 ∼refutation) := by
    simpa only [noZero, classicalNoZero, source_eq_neg_rho, rho, refutation] using hi
  have hp := PRAWitnessZFCStrictComparison.comparison 13
    (sourceTerm 13 (ArithmeticExpression.term Fin.val AdaptiveDirectOrdinate86Literal.naturalExpression86.splitNatural.1))
    (sourceTerm 13 (ArithmeticExpression.term Fin.val AdaptiveDirectOrdinate86Literal.naturalExpression86.splitNatural.2)) h
  simpa only [noZero, classicalNoZero, source_eq_neg_rho, rho, refutation] using hp
end DiophantineConsistency.PRA86ZFCStrict
