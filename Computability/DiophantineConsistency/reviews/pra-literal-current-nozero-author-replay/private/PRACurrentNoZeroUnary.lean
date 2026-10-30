import DiophantineConsistency.PRANoZeroUnary
import DiophantineConsistency.FoundationHACurrentNoZero2011
/-! Concrete specialization to the maintained fourteen-variable source. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace DiophantineConsistency.PRACurrentNoZeroUnary
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRANoZeroUnary FoundationHANoZero ObjectCurrentEquation2011

theorem current_unary_open : ∃ q : Semisentence language 1, q.Open ∧
    PRA ⊢ (Semiformula.lMap embedding FoundationHACurrentNoZero2011.classicalSentence 🡘 ∀⁰ q) := by
  simpa only [FoundationHACurrentNoZero2011.classicalSentence, classicalNoZero, noZero] using
    noZero_unary_open 14
      (sourceTerm 14 (ArithmeticExpression.term Fin.val naturalExpression.splitNatural.1))
      (sourceTerm 14 (ArithmeticExpression.term Fin.val naturalExpression.splitNatural.2))
end DiophantineConsistency.PRACurrentNoZeroUnary
