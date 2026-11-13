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

A separately checked Lean model bridge now proves, in every model of `IΣ₁`,
that this graph has a positive zero exactly when the represented machine has
an internal halt. Its witness map uses the previously proved `q³ ∣ Y`
condition: positive `Y` gives a positive quotient `s`, including in
nonstandard models. In the other direction, `Y=q³s` preserves positivity.
The bridge uses the residual scaling identity in the model's ordered
difference ring and checks the fixed β positivity premise. See [HALT.md](HALT.md)
for the exact theorem, byte-recipe version, selected-provider evidence and
remaining ancestry limits.

The Lean graph and JSON source remain connected by an external check. This
packet does **not** claim an iPRA derivation, an end-to-end fixed-port
file/PDF binding inside Lean, or global minimality.

Run `python3 -I -S -B check_graph.py` from this directory. The script rejects
optimized Python, pins the parent graph, and does not modify artifacts.
