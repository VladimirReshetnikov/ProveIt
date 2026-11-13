# Source review: calibrated rank under uniform realization

Reviewed commit `d51d628ec6`. The source chooses a controller selector `δ`
using the base word's `windowRank`, applies the **same** `δ` to the
realization hypothesis, and passes the resulting `X1`, base `X0`, selector,
pointwise update and support bounds to `calibrated_rank`. Both `PackingInput`
premises use the same symbolic kernel, masks, period and stride; the rank
constant `c` is also shared. No witness mismatch was found in the inspected
composition.

The theorem is deliberately conditional. It assumes a Σ₁-definable base
`X0` satisfying the full `PackingInput`; it also assumes that **every**
Σ₁-definable Boolean selector with the stated positive, nonwrapping support
can be realized by a Σ₁-definable `X1` satisfying that same full packing
interface and the exact cell update. `PackingInput` includes the relevant
size, origin and low/high no-carry properties. The result constructs neither
the base packing nor this uniform realization. The quantification over
definable functions is a Lean metatheoretic statement about each IΣ₁ model,
not a first-order iPRA derivation.

[`audit.py`](audit.py) checks the source, recorded author compile, selected
direct objects, frozen source and exact axiom report at a point in time. The
normal check exited 0; optimized Python was rejected. It does not rerun Lean,
authenticate transitive or dynamic providers, prove physical dummy safety,
bind retained bytes or a displayed coefficient, construct a graph zero, or
establish the desired iPRA equivalence. Original `/tmp` artifacts are required
to reproduce the object checks.
