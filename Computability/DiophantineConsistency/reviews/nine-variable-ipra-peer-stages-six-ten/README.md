# Nine-variable peer replay: stages 6–10, object differences open

The guarded peer overlay completed stages 6–10. Both the peer and the
historical author ledger checks passed; the five source hashes and complete
compiler logs match after replacing only their respective source paths. The
peer reused the author's source-bound warning baselines. Stages 8–10 produced
byte-identical output objects. Stages 6 and 7 did **not** produce
byte-identical objects, so this packet does not report an exact paired match.

Stage 6 `ModelRatioBounds` has identical direct-input object hashes on both
sides. Its author and peer objects have sizes 2,874,224 and 2,874,216 bytes.
The absolute source path appears once at offset 2,862,400 in each, with
three preceding length fields. After replacing that record, including its
respective 96- versus 88-byte padded pathname, both files have equal length.
The remaining differences occupy 553 aligned 64-bit words; each author word
is exactly 8 larger than the peer word. This is **consistent with** relocation
from an eight-byte length change, but no Lean serialization semantics or
semantic equivalence of these objects has been proved. The discrepancy
remains open for purposes of an exact replay audit.

Stage 7 directly imports those different stage-6 objects. Its own two objects
have equal sizes, and replacing its three source-path length fields and
equally sized padded pathname makes the complete bytes equal. Stage 8 directly
imports the differing stage-2 objects described in the [first-five review](../nine-variable-ipra-peer-first-five/README.md),
but its own output matches byte-for-byte. Stages 9 and 10 have matching direct
input object hashes and matching output hashes. The raw direct-input hash
differences are retained; no substitution of these imports is assumed.

[`audit.py`](audit.py) reproduces these observations using the live `/tmp`
objects, both guarded runner checks, and exact source/log/direct-input hashes.
[`capture.py`](capture.py) retains the comparison output, terminal status,
source snapshots, receipts, compiler logs and dependency listings under
[`observations`](observations/). Both overlays still inherit their historical
project, package and dynamic ancestry. These sampled checks cover stages 6–10
only; they are not a full transitive audit, a proof of the binary format, or a
replay of either nine-variable endpoint.
