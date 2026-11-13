# Nine-variable peer replay: stages 92–96

The guarded peer completed `ModelProgramLink`, `ModelBetaFunction`,
`ModelRepArith`, `ModelRepInterfaces` and `ModelRepFactorial`. Both author
and peer ledger checks passed; all five source hashes and complete compiler
logs match after source-path normalization. Stages 92, 93 and 96 have
byte-identical outputs. Each of the five stages directly imports an object
whose author and peer hashes differ; those raw input differences are retained
in the audit and are not treated as exact equality.

Stages 94 and 95 reused the author's source-bound warning baselines and have
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
