# Nine-variable peer replay: stages 16–20

The guarded peer completed stages 16–20. Both the peer and historical author
ledger checks passed; the five source hashes, normalized complete compiler
logs, and direct-input object hashes match. The peer reused the author's
source-bound warning baseline for stage 18. Stages 16, 17, 19 and 20 have
byte-identical output objects.

Stage 18 `ModelCoding` has different author and peer output hashes. Their
objects have equal size, and the respective source paths occur once in
equally sized NUL-padded regions. Replacing the three length fields and that
padded path region makes the complete author bytes equal to the peer bytes.
This is a byte-level observation, not a proof of Lean serialization semantics
or semantic interchangeability. No exact hash match is claimed for stage 18.

[`audit.py`](audit.py) verifies these observations and the raw direct-input
hashes. [`capture.py`](capture.py) retains both sides' source snapshots,
receipts, compiler and dependency logs, audit output, and terminal receipt in
[`observations`](observations/). Repeating these checks requires the live
`/tmp` overlays. The checks are sampled and inherit historical project,
package and dynamic ancestry; stages 16–20 do not establish a full closure
audit or a replay of either nine-variable endpoint.
