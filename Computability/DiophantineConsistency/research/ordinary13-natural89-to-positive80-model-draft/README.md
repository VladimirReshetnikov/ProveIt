# Natural 89 to positive 80: mixed coordinate draft

This is an **unelaborated conditional source proposal**, not a checked graph
bridge, proof of the three direct-coordinate properties, or iPRA endpoint.
The exact positive 80 unit-product literal is generated from its pinned JSON;
the 89 natural literal is the separately generated exact parent.

The 13 witness positions are the same in both graphs. Natural-to-positive
`lift` increments positions `0,1,2,4,5,6,7,9,10,12` and leaves
`f=3`, `r=8`, and `y=11` direct. The positive-to-natural map subtracts one
only at the ten incremented coordinates. The proposed graph evaluation
identity includes the actual `kbase` and `r0` folds; even an exact
polynomial identity does not establish positivity of the three direct inputs.
For any strictly positive parent valuation, the predecessor map is natural and
lifts back to it.

The reverse zero-existence direction uses the deliberately weak all-model
`PositiveDirectReplacement`: any natural 89 zero admits **some** natural 89
zero with all three direct coordinates positive. It does not claim r is
positive at the original zero. The file also exposes a more specific pair of
open cuts, `DirectFY` and `RReplacement`: the former requires f,y>0 at every
zero, and the latter asks for another zero with r>0 while preserving f,y.
Their composition provides `PositiveDirectReplacement`. The externally
reviewed root-switch proof suggests such an r replacement, while the signed
factor geometry suggests f/y positivity; neither all-model graph binding is
proved or assumed as an established theorem here. In particular, the separate
85 prototype graph source applies only after supplying the appropriate exact
forward mapping and preserving the relevant direct coordinates.

Conditional on `PositiveDirectReplacement K` and an explicit
`PolynomialBridge` for **positiveShift of this exact positive-80 graph** at
the same compact tuple, the proposed client supplies the exact 89 bridge.
The chained 85 native client additionally assumes the separate `ForcedEta K`.
No positive-80 endpoint, root-switch theorem, provider/axiom replay, fixed
external byte/PDF linkage, or user-facing ZFC equivalence is asserted here.
The source's exact graph evaluation and zero maps have not been Lean checked.

From `Computability/DiophantineConsistency`, run
`python3 -I -S -B research/ordinary13-natural89-to-positive80-model-draft/check.py`
and compare with `receipt.json`. The checker regenerates the positive literal
in a temporary tree, verifies witness positions and valuation identities, and
never runs Lean.
