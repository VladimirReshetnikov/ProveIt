# The sum-of-squares compiler step is proved inside ZFC

`ObjectResidualSquares.zfc_proves_residual_conjunction` is an actual
`BProv ZFCax_s []` derivation for every supplied finite list of integer
residual expressions. Under the internal-natural coordinate guard, its
closed sentence says that their sum of squares is zero exactly when every
residual is zero. Both sides use the existing object-language polynomial
graph formulas.

The proof covers all natural values of every ZFC model, including
nonstandard values. It first supplies the necessary internal arithmetic:

- `ObjectNaturalOrder` proves each summand is at most its sum, and constructs
  an internal natural difference whenever one natural is at most another.
  Both inductions use explicit formulas. Existing internal ordinal
  linearity gives a linear order on the entire omega; this is the canonical
  additive order, compatible with cancellation.
- `ObjectNaturalZero` proves that a product of internal naturals is zero
  exactly when one factor is zero, using a supplied formula induction and
  the already checked zero-sum law. This provides `NoZeroDivisors` for the
  internal semiring.

For every pair `a,b`, comparison and an internal difference `d` give

```text
a^2+b^2 = 2*a*b+d^2,     d=0 iff a=b.
```

Folding these gaps through a finite list shows that equality of the sums of
`a^2+b^2` and `2*a*b` forces equality in every pair. The proof uses only
finite structural induction on the supplied list; the values need not be
external numerals.

The actual `Expr.splitNatural` components of
`QuarticSyntax.sumExpressions (es.map (fun e => e*e))` are identified with
those two sums. The exact formula/semiring bridge then yields conjunction
semantics for the existing object equation predicates. Validity in every
model and first-order completeness produce the closed ZFC derivation.
Twenty-six dependency audits use only the standard Lean axioms.

This closes the algebraic sum-of-squares step, and does not yet identify a
complete arithmetic proof checker with its polynomial in every model.
Nonstandard coding and representation correctness, native compiler
calibration, and the final consistency/unsolvability biconditional remain
separate obligations.
