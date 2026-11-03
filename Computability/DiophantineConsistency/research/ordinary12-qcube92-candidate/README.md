# A 92-operation quotient candidate

This candidate reparametrizes the independently checked 94-operation graph:
the old positive coordinate `Y` becomes `q³s`, with `q = 1 + Jβ` and new
positive coordinate `s`. In the first residual, writing
`W = ell + k + r − k Bt`, the previous root and scale are

```
Z = q³(q−1)W + Y(q−1) − q³ Bt,     M = q³(q−1).
```

After substitution, the new root and scale are

```
Z' = (q−1)(W+s) − Bt,              M' = q−1.
```

The new first residual is `A0' = Z'² − M'²(1+ell(ell+k))`; the remaining
residuals `A1` and `N` are the original expressions evaluated with
`Y = q³s`. The output is `A0'² + A1² + N²`. The old first residual equals
`q⁶ A0'`, while the other two residuals agree under the substitution.

The complete [graph](candidate.json) uses twelve positive witnesses and 92
live binary integer-leaf operations: 51 multiplications, 24 additions and
17 subtractions. Relative to its pinned parent, it adds `Y=q³s` while
removing two further multiplication operations overall. It preserves the
four fixed integer ports. The self-contained graph checker validates every
row against that transformation, checks topological order and liveness, and
checks the residual identities on 25 exact integer assignments. The separate
[independent audit](../../reviews/ordinary12-qcube92-independent/README.md)
checks the entire graph, the exact polynomial identity, and fixed-port degree
evidence; it reports exact degree 164. This trades a larger degree for two
fewer operations than the parent’s 94-operation, degree-84 variant. The
finite graph and degree checks are external to Lean.

There is a specific route to an all-model existence equivalence, not yet a
checked end-to-end theorem for this candidate. In a model of `IΣ₁`, with
natural-number ports and positive β and all witnesses positive, the existing
`FreeJRootBinding.first_factor_forces_Y_divisible` theorem gives `q³ ∣ Y` at
an old zero. Since `q` and `Y` are positive, the quotient `s` is positive,
including in nonstandard models. Conversely, a positive new witness maps to
an old witness by `Y=q³s`. In the model's ordered difference ring, `q³` is
nonzero; the scaling identity and nonnegativity of squares give the two zero
implications. This route depends on the previous divisibility theorem and an
as-yet-unchecked graph-to-expression and model join. In particular, this
packet does **not** claim an iPRA derivation, a Lean proof of the proposed
92-gate equivalence, an end-to-end fixed-port file/PDF binding, or global
minimality.

Run `python3 -I -S -B check_graph.py` from this directory. The script rejects
optimized Python, pins the parent graph, and does not modify artifacts.
