# A quartic computed from supplied representation syntax

[`QuarticCompiler.lean`](Lean/DiophantineConsistency/QuarticCompiler.lean)
constructs normalized quartic data directly from
`r : Rep Empty (fun _ => A)`. Its theorem-bearing result contains:

- a specified natural witness count `ν ≥ 1`;
- an actual `MvPolynomial (Fin (ν+1)) ℤ`;
- proofs of degree at most four and Jones normalization;
- `∀ x : ℕ, Wset polynomial x ↔ A`.

The distinguished input `x` is ignored. The coefficients depend on the
supplied arithmetic expression and its witness count. The construction does
not select an index or a representing polynomial from an existential proof.
Mathlib's polynomial interpretation remains noncomputable, while the
stored gate residual syntax and finite indexing are executable data.

## Construction

Split the original integer expression into two natural expressions `p,q`
whose values have the original value as their difference. If the original
representation has `m` natural witnesses, and the two syntax trees have
`np,nq` nodes, set

```
ν = m + np + nq + 1.
```

Retain the original witnesses, allocate one natural value to every node in
both trees, and allocate one guard `g`. The quadratic residuals are:

```
output - c                 for a natural constant node,
output - originalWitness   for a variable node,
output - left - right      for an addition node,
output - left*right        for a multiplication node,
pRoot - qRoot              for the final equality,
g - 1                      for normalization.
```

There are `np+nq+2` residuals. The polynomial is their sum of squares.
The compiler indexes the finite tree nodes by an explicit recursive sum
bijection with `Fin np` or `Fin nq`; it does not use `Fintype.equivFin`.
Every operation references the two smaller source subtrees, giving an
acyclic gate construction.

## Correctness

Structural evaluation supplies canonical natural node values and satisfies
every gate. Conversely, induction through the gate equations reconstructs
the original natural expression values from any satisfying assignment.
Thus the final equality is precisely the original zero condition.

A sum of integer squares is zero exactly when every residual is zero.
Each residual has degree at most two, so the resulting polynomial has
degree at most four. At the all-zero witness tuple the guard residual is
`-1`, so the polynomial is nonzero for every input, including arbitrary
integer inputs before the final coordinate renaming.

`QuarticCompiler.compile` combines those facts with the supplied
representation's correctness theorem. Its transitive axiom audit reports
only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
No new axiom or proof placeholder is used.

The resulting data feed directly into
[`JonesSyntax.hasNaturalZero_expression`](Lean/DiophantineConsistency/JonesSyntax.lean)
using their supplied degree and normalization proofs. That gives an actual
nine-variable arithmetic expression whose natural solvability is equivalent
to `A`. The starting `Rep` must itself be supplied as data; this compiler
does not turn an existential MRDP representation into explicit syntax.
