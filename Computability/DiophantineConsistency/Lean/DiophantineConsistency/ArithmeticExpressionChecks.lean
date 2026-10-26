import DiophantineConsistency.ArithmeticCurrentEquation2011

set_option Elab.async false
namespace DiophantineConsistency.ArithmeticExpressionChecks
open SetTheory.PA
open ArithmeticExpression

-- These are the actual term constructors: only one old subterm occurs
-- at each bit. Neither doubling nor numeral compilation copies it.
example : binaryNumeral 0 = .zero := by decide +kernel
example : binaryNumeral 1 = .succ (.mul (.succ (.succ .zero)) .zero) := by decide +kernel
example : binaryNumeral 2 = .mul (.succ (.succ .zero)) (binaryNumeral 1) := by decide +kernel
example : binaryNumeral 3 = .succ (.mul (.succ (.succ .zero)) (binaryNumeral 1)) := by decide +kernel

example {R : Type*} [CommSemiring R] (ee : ℕ → R) (n : ℕ) :
    Term.eval (semiringStructure R) ee (binaryNumeral n) = (n : R) :=
  eval_binaryNumeral ee n

-- An empty tuple and a nonzero negative constant retain their meaning.
example : (∀ ee : ℕ → ℕ, Formula.Sat (semiringStructure ℕ) ee
    (noZeroSentence (Expr.constant (-7) : Expr (Fin 0)))) := by
  rw [sat_noZeroSentence_nat]
  simp only [Expr.eval_constant, not_exists]
  intro v
  decide

example : ¬ (∀ ee : ℕ → ℕ, Formula.Sat (semiringStructure ℕ) ee
    (noZeroSentence (Expr.constant 0 : Expr (Fin 0)))) := by
  rw [sat_noZeroSentence_nat]
  intro h
  exact h ⟨Fin.elim0, rfl⟩

-- Both signs and a nontrivial coordinate map are retained.
example (ee : ℕ → ℕ) : Formula.Sat (semiringStructure ℕ) ee
    (equation ((Expr.var (0 : Fin 1)) - Expr.constant 3) (fun _ => 5)) ↔
      (ee 5 : ℤ) - 3 = 0 := by
  rw [sat_equation, NatExpr.evalSemiring_nat, NatExpr.evalSemiring_nat]
  exact (Expr.eval_eq_zero_iff_splitNatural
    ((Expr.var (0 : Fin 1)) - Expr.constant 3) (fun _ => ee 5)).symm

example : Formula.Sentence ArithmeticCurrentEquation2011.unsolvabilitySentence :=
  ArithmeticCurrentEquation2011.sentence_unsolvabilitySentence

example : (∀ ee : ℕ → ℕ, Formula.Sat (semiringStructure ℕ) ee
    ArithmeticCurrentEquation2011.unsolvabilitySentence) ↔
      ¬ CurrentCarrierArithmetic2011.PositiveZero CurrentPolynomialWindow2011.polynomial :=
  ArithmeticCurrentEquation2011.sat_unsolvabilitySentence_nat

#print axioms eval_binaryNumeral
#print axioms binaryNumeral_closed
#print axioms eval_term
#print axioms free_term
#print axioms sentence_noZeroSentence
#print axioms sat_noZeroSentence
#print axioms sat_noZeroSentence_nat
#print axioms ArithmeticCurrentEquation2011.sentence_unsolvabilitySentence
#print axioms ArithmeticCurrentEquation2011.sat_unsolvabilitySentence
#print axioms ArithmeticCurrentEquation2011.sat_unsolvabilitySentence_nat

end DiophantineConsistency.ArithmeticExpressionChecks
