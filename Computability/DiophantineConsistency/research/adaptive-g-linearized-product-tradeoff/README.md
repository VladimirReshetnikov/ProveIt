# One multiplication exchanged for additions/subtractions

Both existing 13-variable candidate DAGs compute the same intermediate

```text
q = 1 + qm,  qF = q − F,  C = qF − α,
q2 = q²,  g28 = Fq,
g44 = qF·qm,  G = α + g44.
```

All of `q2`, `g28` and `C` are already live at this point. Replace only the
last two rows with

```text
g44 = q2 − g28
G = g44 − C.
```

In any commutative ring,

```text
q² − Fq − C = q(q−F) − ((q−F)−α)
             = (q−F)(q−1) + α
             = α + qF·qm.
```

The temporary `g44` is used only by `G`. Every later row is unchanged, so
induction over the DAG gives the identical complete output polynomial for
every assignment of all variables and coefficient ports. Each positive
witness tuple therefore transports in both directions by the identity map.
This is polynomial equality, not an inference from a finite sample. The old
and new fixed-port positive-shifted equations are also identical polynomials,
so their exact degrees remain the previously certified 36 and 56 respectively.

| Existing graph | Original `× / + / −` | Rewritten `× / + / −` | Total operations |
| --- | --- | --- | ---: |
| Sum of squares | 48 / 21 / 18 | 47 / 20 / 20 | 87, unchanged |
| Product | 47 / 21 / 18 | 46 / 20 / 20 | 86, unchanged |

`check.py` pins both source graphs; verifies all prerequisite rows, that the
temporary has no other consumer, topological order, live outputs and all 13
witnesses and four ports; proves the local polynomial identity by exact sparse
integer arithmetic; rejects a sign mutation; checks both operation breakdowns;
and compares 50 deterministic signed assignments per graph. The normal run
actually exited 0. Optimized Python is rejected because the checks use
assertions. The finite assignments are additional checks; the ring identity
and unchanged surrounding rows justify same-polynomial transport.

This is a representation tradeoff with **one fewer multiplication but the same
total binary-operation count**, not a 12-variable or lower-degree equation.
The equality gives the same degree as the existing certificates in
`../adaptive-square-sums/verify.py` and `../adaptive-direct-ordinate86/DEGREE.md`;
this packet does not recalculate them. No new Lean literal binding, internal
proof of equivalence, current-source replay or published display is claimed.
