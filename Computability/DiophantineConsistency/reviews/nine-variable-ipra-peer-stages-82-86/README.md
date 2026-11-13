# Nine-variable peer replay: stages 82–86

The guarded peer completed `ModelScalarPR`, `ModelOptimizer`,
`ModelDirectScalar`, `ModelEnumeratorCantor` and `ModelEnumeratorRows`. Both
author and peer ledger checks passed; all five source hashes and complete
compiler logs match after source-path normalization. Stages 83–85 have
byte-identical outputs. Stage 83 imports the different-hash stage-82 objects;
the other four stages have matching direct input object hashes.

Stages 82 and 86 reused the author's source-bound warning baselines and have
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
