# Import preflight for the 94-operation model endpoint

The ongoing 425-module rebuild was planned around the earlier compact
symbolic-model theorem. The later 94-operation model join also imports byte
assembly and sum-of-squares objects that were not in that inventory. This
preflight checks whether those added objects have a recorded selected-project
ancestor among the 425 modules being rebuilt.

`scan.py` compares the model join's 1,288-file selected union with the prior
2,616-object header inventory. Of its object paths, 1,252 are in the prior
inventory with matching recorded hashes; 36 are additional. It rechecks all
1,288 resolved files against the earlier manifest, checks the separately
compiled `SumSquaresModelIff` object, and uses the previously retained Lean
object-header reader on the 36 additional objects and that final object.
The reader captures **direct serialized import names**, not proof terms.

Following those names through the earlier recorded selected-object graph,
`SumSquaresModelIff` has 736 selected ancestors, of which **zero** are in the
425-module rebuild list. Its `CompactBytePortsModelIff`,
`CompactFourPortByteAssembly2`, and `FreeJSumSquares` subroots likewise have
zero rebuild-list ancestors. The top root reaches 44 names outside the
selected-project inventory, in `Foundation`, `Mathlib`, `Lean`, and `Init`.
These are not traversed or authenticated by this preflight. Full lists,
direct headers, input hashes and three reader commands are in
[`observations/attempt02`](observations/attempt02/). This stricter second
scan rejects duplicate or missing object-header records and requires each
selected ancestor to belong to the recorded model union or be the top object.
The initial scanner is preserved as `scan-attempt01.py`, with its captured
results in [`observations/attempt01`](observations/attempt01/). Both scans
report the same added objects, direct imports and complete root results.

Both scans exited 0. Each reader batch checked at least 8 GiB of available
memory and fewer than two pre-existing Lean processes immediately before
launch; none was present at those sampled instants. This does not exclude
subsequent overlap. Selected model files and the scanner inputs were rehashed
afterward. The historical graph is checked against its pinned receipt rather
than re-reading every historical object in this scan.

This evidence supports planning the 94-operation join after the rebuild: it
does **not** establish package or dynamic ancestry, authenticate all historical
source-to-object origins, prove compatibility of changed declarations, or
compile the proposed iPRA client. Those checks, the remaining rebuild, and
the formal file/PDF binding are still open.
