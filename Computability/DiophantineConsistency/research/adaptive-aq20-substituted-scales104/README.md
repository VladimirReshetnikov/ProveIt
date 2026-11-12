# Two substituted scales: 20 variables, 104 operations, degree 14

This external candidate substitutes two existing positive scale bindings into
the [22/110/10 two-quotient graph](../adaptive-aq22-two-quotients110/). It has
20 positive integer inputs, 104 binary arithmetic rows, and degree 14; the
literal `+1` shift gives a 20-natural-input graph with 124 rows and the same
degree. This trades lower degree for fewer variables and operations. There is
no claim of global minimality or of a Lean endpoint for this new equation.

## Zero maps

Let `qm = J*beta`, `q = 1+qm`, `M = q³*qm`, and `U = Y*q²`, with all
non-port coordinates positive. Substitute `M` for `scaleVariable` and `U` for
`mainScaleVariable`, and delete their two binding residuals and the associated
two squares and two additions. Exact sparse-polynomial checks show that the
other 11 residuals are unchanged under that substitution, the two removed
bindings become zero, and both complete outputs are sums of the stated
squares. The two substitutions are simultaneous and the expressions depend
only on retained inputs.

For `beta > 0`, both `M` and `U` are positive in the ordered IΣ₁ models used
by the parent argument: `J,Y>0` implies `qm>0` and `q>0`. Any child zero lifts
to a positive parent zero by supplying these two scale coordinates. Conversely,
a positive parent zero has both binding residuals zero and hence projects to a
child zero. These facts do not require sign assumptions on the other three
ports. The same maps work over the ordinary positive integers; positive inputs
and natural inputs correspond via `n+1` and positive predecessor. Graph
subtractions are interpreted in the associated signed integer/difference ring.

The selected fixed beta satisfies the assumption: the pinned source defines
`CurrentMasks2011.ports K` with `beta` as port zero, the pinned current kernel
uses that tuple, and `CurrentMasks2011.beta_pos_int` states `0 < beta` in the
integers. The local checker pins and inspects those source declarations; it
does not elaborate them or by itself establish the represented positivity in
every desired model.

## Degree and comparison

All 11 child residuals have witness degree at most seven. `zDifference` has
the degree-seven monomial `J⁵*X*eta` with coefficient `beta⁵` and no other
port-dependent coefficient on that witness monomial. For each fixed positive
beta, this is nonzero. The degree-14 leading term of the sum of squares is
therefore nonzero over the real polynomial ring. Positive shifting preserves
degree. The checker verifies the complete residual expansions and this
coefficient without expanding the full output.

The earlier [AQ22 positive-binding survey](../aq22-positive-binding-survey/)
reports its best 20-variable point within that finite family as 20/108/20.
This candidate has fewer rows and lower degree, because it starts from the new
quotient graph, while its Lean transfer is not elaborated. AQ22's historical
paired parent replay has inherited provider limitations; the intermediate
22/110 quotient expression and this 20/104 expression both still need Lean
model transports and iPRA clients. The numerical comparison does not compare
those proof statuses or claim a global frontier.

## Reproduce

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/adaptive-aq20-substituted-scales104/build.py
python3 -I -S -B research/adaptive-aq20-substituted-scales104/check.py
```

The first command regenerates both JSON graphs from the hash-pinned 22/110
candidate. The second checks the hashes, graph liveness, natural shift,
residual substitutions, sum-of-squares wiring, source declarations for beta,
and exact degree witness. Its output is [receipt.json](receipt.json). These
are external checks; no Lean process is run.
