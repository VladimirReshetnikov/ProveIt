# Independent review of the forward coordinate map

The proposed coordinate map has the correct direction and uses the same
parent valuation throughout; no concrete source-level mismatch was found.
Its local imports and every proposed Lean proof remain unelaborated, so this
is not a checked model map or iPRA endpoint.

`Carrier65.core` defines `V=f²*(c*T−rank)−c`; none of the variables in
its dependency chain uses slot 12. The parent graph dependency traversal
independently confirms the same property. Its y field is slot 12. Therefore,
if `x=u 12−V`, updating only slot 12 of u to x leaves V fixed and the
literal shear replaces x by `V+x=u 12`, recovering all 14 parent coordinates.
This is the claimed `shear_inverse` equality over a commutative ring.

At model-natural valuation v, the parent ring valuation is
`u j=ι(v j+1)`. The separate positive-gap source proposes n satisfying
`ι(n+1)=u 12−V`. Updating v at index 12 to n and then applying the positive
shift gives exactly the old u at all other coordinates and `ι(n+1)` at slot
12. The reviewed source uses this equality to apply its shear inverse, then
the proposed child-to-parent ring evaluator identity. The directions of
`internalZero_positiveShift` and `internalZero_iff` are correct: parent
split zero gives parent ring zero; the recovered child ring zero gives the
child split zero. The final forward client invokes the signed half-bound,
norm-order and positive-gap sources with their interfaces and produces the
updated natural valuation. Those predecessor claims and their imports have
not been rechecked by Lean here.

The independent checker pins the direct drafts and the defining source/graph
interfaces, verifies the slot and graph dependency, and exercises 80 finite
successor updates and full parent/child graph evaluations. Those controls do
not prove a model theorem, graph-to-Lean file semantics, or the existence of
a zero. `simp` on `Function.update`, coercion/definitional equality,
`rw` occurrence selection, all provider objects and axiom reports need a
coherent Lean replay. The reverse map and encoded iPRA transfer also remain
separate obligations.

From `Computability/DiophantineConsistency`:

    set -o pipefail
    timeout 30s python3 -I -S -B research/current2011-shear-forward-coordinate-map-draft/check.py | cmp - research/current2011-shear-forward-coordinate-map-draft/result.json
    timeout 30s python3 -I -S -B reviews/current2011-shear-forward-coordinate-map-independent/check.py | cmp - reviews/current2011-shear-forward-coordinate-map-independent/receipt.json

Both receipts reproduce. No Lean, build, staging or reviewed-file edit was
performed.
