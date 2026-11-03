# Nine-variable peer replay: stages 21–25

The guarded peer completed stages 21–25. Both author and peer ledger checks
passed; the five source hashes and complete compiler logs match after
normalizing their source paths. The peer reused the author's source-bound
warning baseline for stage 24. Stages 21, 22, 23 and 25 produced identical
output object hashes. Stage 21 directly imports the different stage-2 objects,
and stage 22 imports the different stage-18 objects; the remaining three
stages have matching direct-input object hashes. These import differences
remain visible in the audit, not silently replaced or treated as byte equal.

Stage 24 `ModelJonesSyntax` has matching direct-input hashes but output object
lengths 746,648 and 746,640 bytes. The respective source pathname occurs once
at offset 736,808. Replacing its three length fields and the padded pathname
record makes both object files the same length; the remaining differences are
285 aligned 64-bit words, all eight larger in the author. This is consistent
with an eight-byte layout shift, but no Lean binary-format semantics or
semantic interchangeability have been established, and stage 24 remains an
object mismatch for an exact paired replay.

[`audit.py`](audit.py) verifies the byte-level observations, source/logs and
raw direct-input hashes. [`capture.py`](capture.py) retains source snapshots,
receipts, compiler and dependency listings, audit output and terminal status
in [`observations`](observations/). Repeating the audit requires the live
`/tmp` overlays. Guards are sampled and the historical project, package and
dynamic ancestry remains inherited. The first 25 stages do not establish
either nine-variable endpoint or an authenticated full project closure.
