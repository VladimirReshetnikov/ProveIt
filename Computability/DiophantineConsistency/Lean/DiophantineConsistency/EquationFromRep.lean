import DiophantineConsistency.QuarticCompiler
import DiophantineConsistency.JonesSyntax

/-!
# A fixed nine-variable equation computed from representation data

The supplied `Rep Empty` contains its finite witness count and integer
arithmetic syntax in `Type`. The constructor below computes a normalized
quartic, the literal Jones index, the arithmetic expression in nine natural
unknowns, and the corresponding ordinary integer polynomial. It never
selects a polynomial from an existential representation theorem.

Imported polynomial operations and coefficient readers are noncomputable
library definitions. Thus this is a specified finite coefficient recipe
with a checked syntax artifact, rather than a standalone executable
semidecider-to-equation compiler.
-/

namespace DiophantineConsistency.EquationFromRep

/-- Both presentations of the same fixed equation, with their complete
correctness certificates on the natural domain. -/
structure Result (A : Prop) where
  expression : Expr (Fin 9)
  polynomial : MvPolynomial (Fin 9) ℤ
  eval_equal : ∀ v : Fin 9 → ℤ, expression.eval v = MvPolynomial.eval v polynomial
  syntax_correct : (∃ v : Fin 9 → ℕ, expression.eval (fun i => (v i : ℤ)) = 0) ↔ A
  polynomial_correct : HasNaturalZero polynomial ↔ A

/-- Compute every algebraic stage from the supplied finite representation data. -/
noncomputable def construct {A : Prop} (r : Rep Empty (fun _ => A)) : Result A :=
  let q := QuarticCompiler.compile r
  { expression := JonesSyntax.expression q.polynomial 0
    polynomial := NinePolynomial.polynomial q.polynomial 0
    eval_equal := JonesSyntax.eval_expression q.polynomial 0
    syntax_correct :=
      (JonesSyntax.hasNaturalZero_expression q.polynomial q.positive q.degree q.normalized 0).trans
        (q.correct 1)
    polynomial_correct :=
      (NinePolynomial.hasNaturalZero_polynomial q.polynomial q.positive q.degree q.normalized 0).trans
        (q.correct 1) }

/-- The constructed polynomial has a natural solution exactly when `A` holds. -/
theorem hasNaturalZero_construct {A : Prop} (r : Rep Empty (fun _ => A)) :
    HasNaturalZero (construct r).polynomial ↔ A :=
  (construct r).polynomial_correct

/-- The constructed polynomial has no natural solution exactly when `¬ A` holds. -/
theorem noNaturalZero_construct {A : Prop} (r : Rep Empty (fun _ => A)) :
    (¬ HasNaturalZero (construct r).polynomial) ↔ ¬ A :=
  not_congr (hasNaturalZero_construct r)

/-- The explicit arithmetic syntax has the same unsolvability equivalence. -/
theorem noSyntaxZero_construct {A : Prop} (r : Rep Empty (fun _ => A)) :
    (¬ ∃ v : Fin 9 → ℕ, (construct r).expression.eval (fun i => (v i : ℤ)) = 0) ↔ ¬ A :=
  not_congr (construct r).syntax_correct

/-- The expression denotes the polynomial at every integer tuple, rather than
merely having an equivalent existential zero set. -/
theorem eval_expression_construct {A : Prop} (r : Rep Empty (fun _ => A)) (v : Fin 9 → ℤ) :
    (construct r).expression.eval v = MvPolynomial.eval v (construct r).polynomial :=
  (construct r).eval_equal v

#print axioms noNaturalZero_construct
#print axioms noSyntaxZero_construct

end DiophantineConsistency.EquationFromRep
