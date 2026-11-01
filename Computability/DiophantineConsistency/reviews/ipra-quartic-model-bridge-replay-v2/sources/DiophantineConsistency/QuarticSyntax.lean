import DiophantineConsistency.QuarticCompiler
import DiophantineConsistency.QuarticSyntaxCore
import DiophantineConsistency.SyntaxCoefficients
import Mathlib.Algebra.BigOperators.Fin

/-! # Executable syntax and coefficients for the normalized gate quartic -/

namespace DiophantineConsistency.QuarticSyntax

open QuarticCompiler

@[simp] theorem polynomial_sumExpressions {σ : Type*} (es : List (Expr σ)) :
    (sumExpressions es).toPolynomial = (es.map Expr.toPolynomial).sum := by
  induction es <;> simp_all [sumExpressions, Expr.toPolynomial]

theorem polynomial_expression {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    (expression p q).toPolynomial = quartic p q := by
  rw [expression, Gates.polynomial_rename, polynomial_sumExpressions, quartic]
  apply congrArg (MvPolynomial.rename (coordinate p q))
  simp only [List.map_ofFn]
  rw [Fin.sum_ofFn]
  unfold sumSquares QuarticCompiler.residual
  change (∑ i, (residualSyntax p q ((equationIndex p q).symm i)).toPolynomial *
    (residualSyntax p q ((equationIndex p q).symm i)).toPolynomial) = _
  simpa only [pow_two] using
    (Fintype.sum_equiv (equationIndex p q).symm
      (fun i => (residualSyntax p q ((equationIndex p q).symm i)).toPolynomial *
        (residualSyntax p q ((equationIndex p q).symm i)).toPolynomial)
      (fun j => (residualSyntax p q j).toPolynomial * (residualSyntax p q j).toPolynomial)
      (fun _ => rfl))

/-- Fully executable coefficient reader for the quartic compiled from `p,q`. -/
def coefficient {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m))
    (d : Fin (witnessCount p q + 1) → ℕ) : ℤ :=
  SyntaxCoefficients.coefficient (SyntaxCoefficients.expand (expression p q)) d

theorem coefficient_correct {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m))
    (d : Fin (witnessCount p q + 1) → ℕ) :
    coefficient p q d = MvPolynomial.coeff (SyntaxCoefficients.exponent d) (quartic p q) := by
  rw [coefficient, SyntaxCoefficients.coefficient_expand, polynomial_expression]

#print axioms coefficient_correct

end DiophantineConsistency.QuarticSyntax
