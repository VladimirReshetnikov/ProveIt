# Selected-checker historical matched-pair terminal observation

Launch session `92037` actually exited 0. Its complete tool-provided output is
in `outer-terminal-observation.json`; the coordinator printed both sibling
exits 0 and `MATCHED_SELECTIVE_PASS 10 affected modules`. The separate
coordinator observation records exit 0 and binds the pair-state SHA-256
`33007d02b39767faf32dfbd9ed930d0eb5f495b054ca2bc1e7f988784cf4aefd`.
The launcher, both process logs, freezer and preparer observations, and equal
before/after preparation HEADs are preserved here.

Both sibling states and all 20 module logs are copied here; each log was
rehashed against its state. Each sibling passed ten additions and recorded 16
selected diagnostics. The two selected tracked package source rows and frozen
source bytes are retained, together with source-choice control observations
and the successful launch-time check. The plan reported 15 workspace source
drifts relative to the historical parent. An initial evidence-packaging
attempt referenced a nonexistent control-observation filename; its failure
and successful continuation are recorded separately and did not modify the
original run artifacts.

The subsequent [independent complete-result audit](../ipra-selected-checker-historical-pair-independent-audit/README.md)
passed. The original run remains at
`/tmp/ipra-selected-checker-historical-paired-run-01`. The result inherits
historical parent, package-transitive, dynamic and between-observation limits.
The Foundation wrapper's outer exit was not captured, although its inner Lake
exit and the independent verifier's exit were observed as zero. Identifying
the selected checker and consistency statement with the desired external and
object-level notions remains separate mathematical work.
