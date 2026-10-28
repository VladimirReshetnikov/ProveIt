import DiophantineConsistency.CurrentEquationSyntax2011
import DiophantineConsistency.ArithmeticExpression
import DiophantineConsistency.ObjectCurrentEquation2011

/-! # Arithmetic sentence for the exact current positive equation

The sentence uses fourteen natural variables, each shifted by one, and
the complete current four ports. No port is replaced by an uninterpreted
symbol. This binds the equation side of the HA target; it does not define
an arithmetized ZFC proof checker or prove the equivalence inside HA.
-/

set_option Elab.async false
namespace DiophantineConsistency.ArithmeticCurrentEquation2011
open SetTheory.PA
open ObjectCurrentEquation2011

attribute [local irreducible] expression naturalExpression

theorem sentence_unsolvabilitySentence : Formula.Sentence unsolvabilitySentence :=
  ArithmeticExpression.sentence_noZeroSentence naturalExpression

/-- Every tuple of the interpreted semiring is included. This is an exact
syntax/semantics identity without any arithmetic induction assumption. -/
theorem sat_unsolvabilitySentence {R : Type*} [CommSemiring R] :
    (∀ ee : ℕ → R, Formula.Sat (ArithmeticExpression.semiringStructure R) ee
      unsolvabilitySentence) ↔
      ∀ v : Fin 14 → R, ¬ InternalZero expression (fun i => v i + 1) := by
  rw [unsolvabilitySentence, ArithmeticExpression.sat_noZeroSentence]
  unfold naturalExpression
  constructor
  · intro h v hz
    exact h v ((internalZero_positiveShift expression v).mpr hz)
  · intro h v hz
    exact h v ((internalZero_positiveShift expression v).mp hz)

/-- The standard interpretation is exactly no positive integer zero of
the maintained Carrier65 polynomial, with every coefficient unchanged. -/
theorem sat_unsolvabilitySentence_nat :
    (∀ ee : ℕ → ℕ, Formula.Sat (ArithmeticExpression.semiringStructure ℕ) ee
      unsolvabilitySentence) ↔
      ¬ CurrentCarrierArithmetic2011.PositiveZero
        CurrentPolynomialWindow2011.polynomial := by
  rw [unsolvabilitySentence, ArithmeticExpression.sat_noZeroSentence_nat]
  exact not_congr natural_zero_iff_positive_zero

end DiophantineConsistency.ArithmeticCurrentEquation2011
