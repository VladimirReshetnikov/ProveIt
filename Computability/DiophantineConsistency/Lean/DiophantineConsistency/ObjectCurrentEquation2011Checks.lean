import DiophantineConsistency.ObjectCurrentEquation2011

/-! Focused literal-polynomial, domain-shift, and all-model semantics checks.
No test expands the current natural-expression pair or its large ports. -/

set_option Elab.async false

noncomputable section
namespace DiophantineConsistency.ObjectCurrentEquation2011Checks

open ObjectCurrentEquation2011
open SetTheory SetTheory.Form LeanProofs.BoundedZFCConsistency ObjectOmegaSemiring

attribute [local irreducible] expression naturalExpression

example : CurrentMasks2011.width = 94517 := by decide

example : CurrentWindowCarry2011.ports 0 = (CurrentMasks2011.beta : ℤ) := rfl
example : CurrentWindowCarry2011.ports 1 = (CurrentKernel2011.K : ℤ) := rfl
example : CurrentWindowCarry2011.ports 2 = (CurrentMasks2011.lowPort : ℤ) := rfl
example : CurrentWindowCarry2011.ports 3 =
    ((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : ℤ) := rfl

example : expression.toPolynomial =
    Carrier65.polynomial CurrentWindowCarry2011.ports := polynomial_expression

example {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (expressionAt p).evalRing v = Carrier65.value (fun j => (p j : R)) v :=
  evalRing_expressionAt p v

/-- The shift excludes a zero independent coordinate; it is not the identity. -/
example : (positiveShift (Expr.var (0 : Fin 14))).eval (fun _ => 0) = 1 := rfl
example : (Expr.var (0 : Fin 14)).eval (fun _ => 0) = 0 := rfl

/-- Negative coefficients are interpreted through the two natural sides. -/
example {R : Type*} [CommSemiring R] (v : Fin 1 → R) :
    InternalZero (positiveShift (Expr.var 0 - Expr.constant 2)) v ↔ v 0 + 1 = 2 := by
  rw [internalZero_positiveShift]
  simp [InternalZero, Expr.splitNatural, NatExpr.evalSemiring, HSub.hSub, Sub.sub]

example (v : Fin 14 → ℕ) :
    naturalExpression.eval (fun i => (v i : ℤ)) =
      MvPolynomial.eval (fun i => (v i : ℤ) + 1)
        CurrentPolynomialWindow2011.polynomial := eval_naturalExpression v

example :
    (∃ v : Fin 14 → ℕ, naturalExpression.eval (fun i => (v i : ℤ)) = 0) ↔
      CurrentCarrierArithmetic2011.PositiveZero CurrentPolynomialWindow2011.polynomial :=
  natural_zero_iff_positive_zero

example : Sentence unsolvabilitySentence := sentence_unsolvabilitySentence

universe u
variable {V : Type u} {mem : V → V → Prop} (H : ZFAxioms mem)

/-- No restriction to standard numeral tuples occurs in this quantifier. -/
example : (∀ ee : ℕ → V, Sat mem ee unsolvabilitySentence) ↔
    ∀ v : Fin 14 → Natural H, (∀ i, 0 < v i) → ¬ InternalZero expression v :=
  sat_unsolvabilitySentence_iff H

example (v : Fin 14 → Natural H) (hv : ∀ i, 0 < v i) :
    ∃ x : Fin 14 → Natural H, ∀ i, v i = x i + 1 := by
  classical
  exact Classical.skolem.mp (fun i => (internal_positive_iff_successor H _).mp (hv i))

example (h : ∀ ee : ℕ → V, Sat mem ee unsolvabilitySentence) :
    ¬ CurrentCarrierArithmetic2011.PositiveZero CurrentPolynomialWindow2011.polynomial :=
  no_positive_zero_of_sat H h

#print axioms evalRing_expressionAt
#print axioms polynomial_expression
#print axioms eval_naturalExpression
#print axioms natural_zero_iff_positive_zero
#print axioms split_positiveShift
#print axioms no_shifted_zero_iff_positive
#print axioms sentence_unsolvabilitySentence
#print axioms sat_unsolvabilitySentence_iff
#print axioms equationRel_numerals_iff
#print axioms no_positive_zero_of_sat

end DiophantineConsistency.ObjectCurrentEquation2011Checks
