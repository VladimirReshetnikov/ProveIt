# Candidate: sheared 14-variable 72-operation degree-46 graph

This is a **candidate**, not yet an equation proved equivalent to consistency. It retains the exact current2011 four fixed ports and all fourteen strictly positive integer coordinates of the checked 71/60 graph, but interprets its `y` coordinate through the shear `y_parent = V + y`. The exact graph identity over any commutative ring is

```
parent(v with y_parent := V+y) = candidate(v).
```

Only the auxiliary factor changes. With `A = Delta*(f^2-1)`, the original `A*(V^2-y_parent^2)+y_parent^2` becomes `(V+y)^2 - A*y*(2*V+y)`. The graph reuses `y_old = V+y`, so its six replacement rows add only one live binary operation relative to the five old rows. The resulting 72 live gates comprise 38 multiplications, 20 additions and 14 subtractions. Both graphs use the same four fixed integer leaves; the checker validates their actual gzip hashes, raw bytes and bit lengths.

The read-only checker proves the exact shear identity by integer sparse-polynomial calculation at the auxiliary cut and checks every unchanged graph row, topology and liveness. An upper-degree propagation includes the explicit main-norm cancellation; all fourteen witnesses set to `t` and the actual fixed bytes evaluated modulo 1,000,000,007 yield degree 46 with nonzero leading coefficient 110,098,480. Thus the candidate has exact fixed-byte degree 46 externally. No Lean theorem about this graph, external files, or its degree is asserted.

**Unresolved: a positive-coordinate zero bridge.** The shear is an integer polynomial automorphism, but `V` can be negative, so it does not preserve positive `y` automatically. A possible all-IΣ₁-model proof must establish both directions:

1. From a parent zero, use the existing 71/60 norm decomposition to get `A = (i*c^2)^2` and auxiliary norm `A*(V^2-y_parent^2)+y_parent^2=1`. If `y_parent <= V`, positivity and `A>1` force `y_parent=V=1`. Existing `ArithmeticCarrier94Indices.ordinary_first_indices` derives `2*R<c` from the corresponding ordinary-norm hypotheses; the scalar-window lemma supplies `8 <= R`. The checked 71/60-to-67/94 bridge is a route to those hypotheses. The ordinary strong equation does **not** directly give `f^2 ≡ 1 (mod c)`. Under the main-norm, positivity and large-`c` hypotheses, `ArithmeticCarrier94Indices.ordinary_half_index` derives this residue using `relaxed_auxiliary`, Pell index divisibility and the Pell identity. Its proof-local residue argument would need to be exposed or reproved. Combined with `V=f^2*(c*T-R)-c`, the residue gives `V ≡ -R (mod c)` and excludes `V=1` because `8 <= R` and `2*R<c`. This would yield `y_parent-V>0`.
2. For a candidate zero, first show `V+y` is nonzero without assuming it positive. If it were zero, `V=-y` is nonzero; if `f=1`, the strong square is too large, while if `f>1`, `A*V^2` is too large for the total sum of squares to vanish. Then the parent coordinate `|V+y|` is positive and gives the same value because the parent graph uses that coordinate only through its square. The proof must check these inequalities and all model-domain conversions rigorously; the current graph check does not.

A successful all-model bridge, exact graph evaluator in Lean and iPRA transfer remain required before treating this as a proved Pareto improvement. Run `python3 -I -S -B check.py` from this directory. `build.py` pins the parent and refuses to overwrite the output.
