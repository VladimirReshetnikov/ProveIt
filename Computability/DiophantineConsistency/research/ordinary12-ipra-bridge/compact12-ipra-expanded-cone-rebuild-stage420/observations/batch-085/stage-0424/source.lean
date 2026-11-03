import DiophantineConsistency.PRAWitnessZFCStrictComparison
import DiophantineConsistency.HAExpressionAssembly
/-! Optional expression-level transfer to the literal ZFC PRA comparison;
source-current coherent replay is pending. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.PRAExpressionZFCStrict
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRANoZeroUnary FoundationHANoZero
  FoundationHAConsistencyNormalization PRAWitnessZFCRefutationBound

theorem comparison_of_isigma1 {n : ℕ} (e : Expr (Fin n))
    (h : 𝗜𝚺₁ ⊢ (classicalNoZero e 🡘 FoundationZFCConsistencyNat.sourceSentence)) :
    PRA ⊢ (Semiformula.lMap embedding (classicalNoZero e) 🡘
      Semiformula.lMap embedding (∼refutation)) := by
  have hh : 𝗜𝚺₁ ⊢
      (noZero n
        (sourceTerm n (ArithmeticExpression.term Fin.val e.splitNatural.1))
        (sourceTerm n (ArithmeticExpression.term Fin.val e.splitNatural.2)) 🡘 ∼refutation) := by
    simpa only [noZero, classicalNoZero, source_eq_neg_rho, rho, refutation] using h
  simpa only [noZero, classicalNoZero] using
    PRAWitnessZFCStrictComparison.comparison n
      (sourceTerm n (ArithmeticExpression.term Fin.val e.splitNatural.1))
      (sourceTerm n (ArithmeticExpression.term Fin.val e.splitNatural.2)) hh

theorem comparison_of_bridge {n : ℕ} (e : Expr (Fin n)) (hp : HAExpressionAssembly.PolynomialBridge e) :
    PRA ⊢ (Semiformula.lMap embedding (classicalNoZero e) 🡘
      Semiformula.lMap embedding (∼refutation)) :=
  comparison_of_isigma1 e (HAExpressionAssembly.isigma1_equivalence e hp)
end DiophantineConsistency.PRAExpressionZFCStrict
