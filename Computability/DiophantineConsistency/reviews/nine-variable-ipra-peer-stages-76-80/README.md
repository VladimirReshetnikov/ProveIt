# Nine-variable peer replay: stages 76–80

The guarded peer completed `Carrier65`, `ModelCarrierScaled`,
`ModelCarrierSyntax`, `ModelCarrierCurrent` and `IPRANineCurrent`. Both
author and peer ledger checks passed; all five source hashes and complete
compiler logs match after source-path normalization. In particular the
stage-80 endpoint object has the same SHA-256 in both runs. This is not an
exact paired endpoint replay: stage 80 imports different-hash stage-70
`ModelJonesNine` objects, and its separate axiom-report client is stage 81.

Stage 77 `ModelCarrierScaled` reused the author's source-bound warning
baseline and has different output hashes despite matching direct-input hashes.
Its two output files have equal sizes, and their respective source pathnames
occur once in equally sized padded regions. Replacing the three path-length
fields and padded pathname transforms the complete author bytes into the
peer bytes. This is a byte-level observation, not a proof of Lean binary-format
semantics or semantic interchangeability. Stage 76 imports different-hash
stage-75 `ShortSystem` objects; stages 78 and 79 import the different-hash
stage-77 objects. Their output hashes nevertheless match. Raw direct-input
hash differences are retained, not treated as exact equality.

[`audit.py`](audit.py) checks both ledgers, complete byte observation,
source/log comparison and raw direct input hashes. [`capture.py`](capture.py)
retains source snapshots, receipts, dependency listings, compiler output and
terminal receipt under [`observations`](observations/). Repeating the audit
requires the live `/tmp` overlays. Checks are sampled and earlier project,
package-transitive and dynamic ancestry remains inherited; no full closure
audit or formal PDF binding is claimed.
