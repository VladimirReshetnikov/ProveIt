import DiophantineConsistency.PRAWitnessZFCStrictComparison
import DiophantineConsistency.HAAdaptiveFactor87
import DiophantineConsistency.FoundationHAConsistencyNormalization
/-! The literal 13-variable 87-operation equation in classical candidate PRA. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.PRA87ZFCStrict
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRANoZeroUnary FoundationHANoZero
  FoundationHAConsistencyNormalization PRAWitnessZFCRefutationBound

attribute [local irreducible] AdaptiveFirstRootFactor87Literal.naturalExpression87

theorem equivalence : PRA ⊢
    (Semiformula.lMap embedding (classicalNoZero AdaptiveFirstRootFactor87Literal.naturalExpression87) 🡘
      Semiformula.lMap embedding FoundationZFCConsistencyNat.sourceSentence) := by
  have hi := HAExpressionAssembly.isigma1_equivalence
    AdaptiveFirstRootFactor87Literal.naturalExpression87 HAAdaptiveFactor87.polynomialBridge
  have h : 𝗜𝚺₁ ⊢
      (noZero 13
        (sourceTerm 13 (ArithmeticExpression.term Fin.val AdaptiveFirstRootFactor87Literal.naturalExpression87.splitNatural.1))
        (sourceTerm 13 (ArithmeticExpression.term Fin.val AdaptiveFirstRootFactor87Literal.naturalExpression87.splitNatural.2)) 🡘 ∼refutation) := by
    simpa only [noZero, classicalNoZero, source_eq_neg_rho, rho, refutation] using hi
  have hp := PRAWitnessZFCStrictComparison.comparison 13
    (sourceTerm 13 (ArithmeticExpression.term Fin.val AdaptiveFirstRootFactor87Literal.naturalExpression87.splitNatural.1))
    (sourceTerm 13 (ArithmeticExpression.term Fin.val AdaptiveFirstRootFactor87Literal.naturalExpression87.splitNatural.2)) h
  simpa only [noZero, classicalNoZero, source_eq_neg_rho, rho, refutation] using hp
end DiophantineConsistency.PRA87ZFCStrict
