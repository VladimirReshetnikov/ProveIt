# Proposed 87/36 ↔ 88/30 auxiliary graph client

This is a source-only, unelaborated proposal. It pins the exact 87 literal,
88 literal and generic witness sources, and proposes the two-way positive-zero
map at the same model and arbitrary signed port tuple. It does not establish
any Lean theorem, provider/axiom replay, fixed-port byte/PDF binding or
endpoint.

Coordinate 11 is positive y in the 87 graph and positive u in the 88 graph.
`put` changes only that coordinate. `eval87` and `eval88` propose exact graph
identities into the existing five-square interface with fifth square zero.
The first, main and strong residuals are taken from the 87 graph and are
independent of coordinate 11. The signed common fields are

```
z = f²*(T*c−R)−c,    Q = Delta*(f²−1),
```

where c, Delta, q and the signed R are literal graph expressions. Their
values are never assumed to be model naturals. The auxiliary residuals are
`y²−Q*(y²−z²)−1` and `(z+u)²−Q*u*((z+u)+z)−1`. The unelaborated
`positive_aux_coordinate_iff` source proposes same-model natural witnesses,
using the natural cone after the strictly positive signed inequalities are
established.

`BoundsCut` explicitly requires `1<Q` and `1<z²` at each positive zero of
either actual graph. Under that cut, `positive_zero_iff` proposes each graph
zero transports to the other by updating coordinate 11 to the positive
model-natural witness. It preserves all other coordinates and p. The source
imports no proof that the actual graph yields those strict bounds: first and
main scaled-norm extraction, strong norm, positive scale/port casts and the
fact-level bound clients remain separate obligations. A positive-z sign is
not an assumption, nor is finite enumeration a model argument.

The checker pins the exact source/graph bytes and evaluates both entire graph
literals at 400 model-natural input tuples with arbitrary signed ports and
independent coordinate replacements. It checks both five-square formulas and
z/Q values; it does not elaborate Lean or establish nonstandard-model
semantics. From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-positive87-to88-aux-model-draft/check.py | cmp - research/ordinary13-positive87-to88-aux-model-draft/receipt.json
```
