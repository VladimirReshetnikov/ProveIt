# Independent source review: auxiliary model geometry

**Source review passes; not elaborated.** In the stated natural-model
setting, `Y>0` gives `Y≥1` and `X≤XY²`. The explicit inequality
`8XY²+4≤k` therefore yields `X+4≤k`. With `eta>0`,

```
A=XY+Y+2 < Y(X+4) ≤ Yk < eta+Yk=c.
```

This argument uses only nonnegativity of X, which is automatic in the
natural-like model; it does not need the stronger hypothesis X>0. Also
`A≥2`, so `A²=Delta+1` gives `0<Delta<A²<c²≤c³` and `c>1`. The stated
Delta identity is a natural equality; no unproved conversion from truncated
natural subtraction is used.

The checker pins the proposed source and the linked source-level model
prerequisites, verifies the central polynomial identity exactly, replays the
author inventory and independent bounds review, and exercises finite cases
including X=0. It does not invoke Lean. Tactic elaboration, model instances,
provider ancestry and graph-specific extraction of the first/main norms and
Delta identity remain open, as do the graph/iPRA endpoints.

From `Computability/DiophantineConsistency`, run:

```
python3 -I -S -B reviews/ordinary14-aux-geometry-model-draft-independent/check.py
```

Compare stdout with `result.json`.
