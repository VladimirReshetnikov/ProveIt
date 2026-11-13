# Nine-variable peer replay: stages 87–91

The guarded peer completed `ModelEnumeratorStep`, `ModelSyntaxPipeline`,
`ModelRepCore`, `ModelRepBasic` and `ModelSourceModel`. Both author and peer
ledger checks passed; all five source hashes and complete compiler logs
match after source-path normalization. Stages 88, 89 and 91 have
byte-identical outputs. Stage 87 imports the different-hash stage-86 object,
stage 90 imports stage-82's different object, and stage 91 imports stage 90's
different object. Stages 88 and 89 have matching direct input object hashes.

Stages 87 and 90 reused the author's source-bound warning baselines and have
different output object hashes. Each pair has equal size, and the respective
source path appears once in equally sized padded regions. Replacing the
three path-length fields and padded pathname transforms the complete author
bytes into the peer bytes. This is a byte-level observation, not a proof of
Lean serialization semantics or object interchangeability; no exact match is
claimed for those two stages.

[`audit.py`](audit.py) checks both ledgers, complete byte observations,
source/log comparison and raw direct input hash differences.
[`capture.py`](capture.py) retains source snapshots, receipts, dependency
listings, compiler output and terminal receipt under
[`observations`](observations/). Repeating the audit requires the live `/tmp`
overlays. Checks are sampled; earlier project, package-transitive and dynamic
ancestry remains inherited. These stages do not include the final
enumerator-based nine-variable endpoint.
