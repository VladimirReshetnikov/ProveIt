# Three positive bindings: 17 variables, 95 operations, degree 20

This external candidate substitutes three existing positive bindings into the
[20/104/14 graph](../adaptive-aq20-substituted-scales104/). It has 17 positive
integer inputs, 95 binary arithmetic rows and degree 20. The literal `+1`
shift gives a 17-natural-input graph with 112 rows and the same degree. It
trades a higher degree for fewer variables and operations; no global minimum is
claimed.

## Zero maps

For positive inputs write `E = X*Y`, `k = eta+zeta`, `c = eta+Y*k`, and
`a = E+Y`. Substitute

```
ellVariable     = E*Y*k
cSquareVariable = c*c
deltaVariable   = 3 + 4*a + a*a
```

into the parent and delete their three binding residuals, squares and sum
additions. These expressions depend only on retained inputs and are all
positive: `E,Y,k,c` are positive, and `3 + 4*a + a*a >= 3`. Exact polynomial
checks verify equality of the eight remaining residuals, vanishing of all
three deleted residuals, and both sum-of-squares wirings. These local maps
hold for arbitrary integer port values and in ordered IΣ₁ models: project a
positive parent zero using its three vanishing binding residuals; lift a
child zero using the three positive expressions. Circuit subtraction is in the
associated signed difference ring. The natural version uses `n+1` and positive
predecessors. The earlier bridge from 20/104 to 22/110 separately assumes the
fixed first port `beta > 0`, as documented in the parent packet.

## Degree and provenance

The eight residuals have witness degree at most ten. The strong residual `g72`
has monomial `Y⁴*eta⁴*i²` with coefficient one, with no other port-dependent
coefficient on that witness monomial. It therefore has degree ten after every
fixed-port specialization; its leading contribution to the sum of squares
cannot cancel identically over the real polynomial ring. The output degree is
exactly 20, including after positive shifting. The checker verifies this without
expanding the complete sum.

The retained [17/99/20 graph](../adaptive-square-sums17/) uses the same numbers
of positive variables and degree, and four more operations. Its own native
endpoint and provenance are documented there; the present graph has a
completely separate construction and **its model transfer and iPRA endpoint
have not been elaborated in Lean**. The two intermediate 20/104 and 22/110
transfers are also open. The [older positive-binding survey](../aq22-positive-binding-survey/)
records 17/99/32 for its separate five-binding branch. These numerical
comparisons do not establish global optimality or identical proof provenance.

## Reproduction

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/adaptive-aq17-positive-bindings95/build.py
python3 -I -S -B research/adaptive-aq17-positive-bindings95/check.py
```

The generator pins the 20/104 parent and produces the positive and natural
JSON graphs. The checker pins all three graphs, checks liveness, explicit
natural shifting, exact residual substitutions, sum-of-squares wiring and the
leading degree witness. Its deterministic output is [receipt.json](receipt.json).
These external checks do not invoke Lean.
