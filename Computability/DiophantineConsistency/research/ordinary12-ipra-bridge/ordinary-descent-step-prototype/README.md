# Conditional adjacent-coefficient descent invariants

Over any commutative ring, the transformation

```
v'=(2q−1)v−2(q−1)y,    y'=(2q−1)y−2qv
```

preserves `qv²−(q−1)y²`. Separately, given an explicit divisor witness
`q−1=b·s`, its cleared numerator
`a'=(2q−1)a−2qvb` satisfies `a'−a=b(2sa−2qv)`. If `b≠0` and a Bézout
certificate `a·x+b·y=1` are supplied, Lean constructs a certificate for
`a'` and the same nonzero b. The result does not establish that such a
nonzero denominator, divisor witness, or certificate exists, nor does it
prove a strictly decreasing positive measure, termination, integrality,
the strong norm, or graph-to-ring transport.

Fresh historical replay session 36762 actually exited 0 and printed
`PASS_BOUNDED_ORDINARY_DESCENT_STEP
edf46847ad52e19b9c7aef7fdd977de8a7b2730d0de5084fbf061955e1af064c`.
The receipt includes three Lean axiom reports, direct imports, source/object
hashes and inherited ordinary-tail/provider replay. Exploratory session 12445
also exited 0. An earlier failed tactic attempt is recorded under
`observations/`. This is single-author algebra, not a matched full-project
replay, dynamic dependency audit, or iPRA derivation.
