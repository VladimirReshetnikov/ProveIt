# Bounded sign-pair rewrite search on the 69/84 equation

This search starts from the separately validated 14-positive-variable, 69-operation, degree-84 ordinary graph in [`current2011-ordinary69-84-candidate`](../current2011-ordinary69-84-candidate/). It keeps the same witnesses, fixed integer ports and integer-leaf operation metric. It found no graph below 69 operations in the states visited. The 65/150 maintained equation remains the smaller operation-count result; 69/84 is a different degree/operation tradeoff. No global minimum or new equation follows.

The seed set contains the original graph and the three variants obtained by reversing the subtraction in any two of `N0`, `N1`, and `Nt`. The script verifies their only consumers feed `N0*N1*Nt`, and checks in the exact free commutative polynomial ring that negating two factors preserves `X*(X-2)`. All other graph nodes remain unchanged, so each seed computes the identical polynomial and has the same zero set, including both directions on positive inputs.

For ten iterations, the search applies the previously independently checked ring-rewrite templates (signed reassociation, multiplication reassociation, distribution and common-product factoring) at one live node, rebuilds the graph with commutative sharing, keeps intermediate graphs with at most 71 live binary gates, and retains at most 160 states per depth using deterministic seed 69085. It includes a separate 3-to-2-gate factoring control. It imports only five function definitions from the SHA-pinned prior engine using Python's AST; it does not run the prior search. Both source graph and engine bytes are pinned. The retained beam is a small subset of generated states, so this is not exhaustive even within all possible sequences of those rewrites. The literal integer terminals are the ones already in the graph; the search does not add arbitrary constants or change variables.

The recorded run found no sub-69 state; [`result.json`](result.json) lists the visited depth counts. The script refuses to claim a result if it encounters a smaller state, which would require separate exact validation. This read-only calculation adds no Lean theorem or JSON/PDF semantics binding. Run from the repository root with:

```
python3 -I -S -B Computability/DiophantineConsistency/research/current2011-ordinary69-sign-beam/search.py
```

Independent review passed: [`reviews/current2011-ordinary69-sign-beam-second-independent/`](../../reviews/current2011-ordinary69-sign-beam-second-independent/) reproduced the deterministic receipt, checked the sign identities and graph bindings, and reran the prior exact rewrite-template audit. Its conclusion applies only to the visited beam.
