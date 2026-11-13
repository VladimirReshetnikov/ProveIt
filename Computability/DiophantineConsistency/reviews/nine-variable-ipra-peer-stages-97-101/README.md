# Nine-variable peer replay: stages 97–101

The guarded peer completed `ModelBoundedForallArith`, `ModelRepPrec`,
`ModelBoundedForall`, `ModelRepPell` and `ModelRepPower`. Both author and
peer ledger checks passed; all five source hashes and complete compiler logs
match after source-path normalization. Stage 97 has matching direct-input and
output object hashes. Each of stages 98–101 directly imports at least one
different-hash object, as detailed in the retained audit output.

Stages 98–101 reused the author's source-bound warning baselines and have
different output object hashes. Each pair has equal size, and the respective
source path occurs once in equally sized padded regions. Replacing the three
path-length fields and padded pathname transforms the complete author bytes
into the peer bytes. This is a byte-level observation, not a proof of Lean
serialization semantics or object interchangeability; no exact match is
claimed for those stages.

[`audit.py`](audit.py) checks both ledgers, complete byte observations,
source/log comparison and raw direct input hash differences.
[`capture.py`](capture.py) retains source snapshots, receipts, dependency
listings, compiler output and terminal receipt under
[`observations`](observations/). Repeating the audit requires the live `/tmp`
overlays. Checks are sampled; earlier project, package-transitive and dynamic
ancestry remains inherited. These stages do not include the final
enumerator-based nine-variable endpoint.
