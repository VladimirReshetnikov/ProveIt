# Pell indices for an actual adaptive zero

`ArithmeticAdaptivePellIndices2011` applies both internal Pell classifications
to the literal adaptive equation, over every `ORingStructure` satisfying
`IΣ₁`. Its public natural-input client takes only a zero of the current
13-variable expression. Positivity of the shifted variables is derived, as are
the quotient witnesses and the orientation of the main root.

Writing the shifted inputs as `v`, put `Q = v₆v₇²`, `k = v₉+v₁₀`,
`a = v₆v₇+v₇`, and `c = v₉+v₇k`. The first quotient norm is
`first² = 1+Q(Q+1)k²`; `Q > 0` is derived from the inputs. The first
classification gives a positive internal index `n ≤ k`, with
`first = xcoord(n, 2(Q−1)+1)` and `k = 2 ycoord(n, 2(Q−1)+1)`.
The module retains the exact equality between the magnitude of the literal
first signed root and its scale times `first`; it does not claim the sign of
that root.

The oriented main quotient satisfies `main² = 1+(a+1)(a+3)c²`. The main
classification gives a positive internal index `m ≤ c`, with
`main = xcoord(m,a)` and `c = ycoord(m,a)`. The theorem retains the signed
pair equivalence between the actual main root and its positive scale times
`main`. Positivity of both indices follows from the positive ordinates and
zero-index recurrence values; it is not a classification premise.

The implementation does not assert any relation between `n` and `m`, an index
offset, a power representation for an input, or the complete internal HA
proof. These remain separate tasks. The all-model theorem is a semantic
intermediate and is not by itself a Lean proof that HA proves the desired
sentence.
