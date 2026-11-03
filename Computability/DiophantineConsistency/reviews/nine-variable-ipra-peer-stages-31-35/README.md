# Nine-variable peer replay: stages 31–35

The bounded peer replay compiled `ComposeRepresentation`,
`PairingRepresentation`, `Diophantine.Common.MRDPCore`,
`BoundedForallCertificate` and `PellRepresentation`. For each stage the
author and peer source hashes, output object hashes, complete compiler
output, selected direct dependencies and recorded candidate/companion guards
match after normalizing the two overlay-root paths. Both guarded ledger checks
pass. This is a scoped exact object match for these five stages, not for the
104-stage chain as a whole.

The initial comparison incorrectly required all compiler logs to be empty.
Stage 33's matching logs contain informational `Try this` suggestions; they
contain no warning, error or `sorryAx`. The rejected audit source and exact
output are retained under [`observations-rejected`](observations-rejected/).
The corrected comparison requires the complete logs to match and rejects
those diagnostic markers; its successful evidence is in
[`observations`](observations/).

[`audit.py`](audit.py) checks the live ledgers and per-stage records;
[`capture.py`](capture.py) retains source snapshots, receipts, dependency
listings, compiler output and terminal receipt. Repeating it requires the
live `/tmp` overlays. Guards are sampled at recorded boundaries, and the
earlier project, package-transitive and dynamic ancestry remains inherited;
neither nine-variable endpoint is part of these five stages.
