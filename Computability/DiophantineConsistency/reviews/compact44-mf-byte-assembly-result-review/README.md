# Source and artifact review of the shifted MF byte assembly

The reviewed no-hypothesis Lean theorem states
`Nat.ofDigits 256 CompactShiftedHighByteWindow.bytes =
CompactFixedBeta.betaNat + CompactSymbolicPorts.highNat`. The selected
`shifted_value` source uses the generic repunit lemma to replace an initial
high digit 4 by 3 and append one high digit, accounting for **one** beta
addition. The selected byte-window source then uses that equality and the
two-digit bit-window lemma; the selected bound source proves the sum fits in
73,759 bytes, and the generic radix reconstruction supplies the assembly.

The successful single-author receipt records Lean exit 0, no warnings or
`sorryAx`, and the named metatheory report
`[propext, Classical.choice, Quot.sound]`. This review checks the exact
assembly source, log, live object and direct/companion guards, and checks the
selected source/object/receipt chains for the shifted digits, byte-window,
bound and two generic reconstruction/repunit modules. The generic
`ByteWindow` provider and other inherited transitive inputs remain outside a
complete source-origin audit.

The prepared union records 12 provider roots, 1,452 inventoried provider
files and 590 selected files. This review rechecks the selected path set,
hashes and targets, the recorded provider inventory and all 524 overlapping
relative paths; no differing common file hash or suppressed companion was
found. These are sampled filesystem checks, not a fresh Lean replay or a
full transitive, package or dynamic ancestry audit.

Independently of the author's Python transcription, the audit parses the
high-digit list in its Lean source, checks its 8,807 entries, constructs its
radix value and one repunit shift, checks the 8,808-digit shifted value and
size bound, and finds that all 73,759 little-endian bytes match the retained
parent `MF_source.bin.gz` after external decompression. It also reruns the
author's pinned external checker. This finite check and the Python parsing,
filesystem and gzip remain **external** to Lean; no theorem here identifies
file bytes, a PDF or an iPRA endpoint.

[`audit.py`](audit.py) performs these read-only checks; [`capture.py`](capture.py)
retains source/object/receipt hashes, outcome and terminal receipt under
[`observations`](observations/). Rerunning requires the live `/tmp` selected
objects and inherited providers. No mismatch was found within this scope.
