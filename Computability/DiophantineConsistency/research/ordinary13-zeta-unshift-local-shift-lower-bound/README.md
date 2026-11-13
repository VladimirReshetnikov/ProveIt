# Local gate obstruction for zeta-unshifted main shift

The exact eta/zeta-natural boundary probe has 85 arithmetic rows, the same as
its eta-natural parent. This bounded check asks whether its *local* main shift
can be computed in two binary `+`, `−`, `*` gates after its already available
inputs are fixed as `x=U*gamma`, R and `k=eta+zeta`. The changed graph needs

```
shift = x + R + 1 − k.
```

Its actual `r0base=k−R`, `r0=r0base−1`, `shift=x−r0` uses three gates.
The checker enumerates **all** one- and two-gate straight-line circuits over
the formal independent inputs x, R, k and constants 0, 1, 3, 4, using exact
sparse integer polynomial arithmetic. Reuse of the first intermediate is
allowed. None yields the target polynomial; the existing three-gate
construction does. This is an exact finite algebraic obstruction under those
local assumptions, not a random-test result.

It does **not** prove global minimality or rule out an 84-operation graph.
A different representation might reuse other non-independent expressions
from earlier rows, change several surrounding gates or coordinates, or use a
zero-set equivalence that holds only under compact-port/model hypotheses.
The local enumeration does not cover such alternatives. Zeta forcing and the
two-way source-only zero map also remain unelaborated. No Lean/build,
provider, endpoint or PDF claim is made.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-zeta-unshift-local-shift-lower-bound/check.py | cmp - research/ordinary13-zeta-unshift-local-shift-lower-bound/receipt.json
```
