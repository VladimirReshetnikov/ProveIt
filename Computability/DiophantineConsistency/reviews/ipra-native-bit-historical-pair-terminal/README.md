# Native-bit historical matched-pair terminal observation

Launch session `79106` actually exited 0. Its complete tool-provided output is
in `outer-terminal-observation.json`; the coordinator printed both sibling
exits 0 and `MATCHED_SELECTIVE_PASS 11 affected modules`. The separate
coordinator observation records exit 0 and binds the pair-state SHA-256
`8b53fc16f72ad88df86e6e8efcd902569e3ebe01e2edc6d986ee9435d89bc9ff`.
The exact launcher, both process logs, freezer and preparer observations, and
equal before/after preparation HEADs are retained here.

Both sibling states and all 22 module logs are copied here; each log was
rehashed against its state. Each sibling passed eleven additions and recorded
18 selected diagnostics. The two selected tracked package source rows and
frozen bytes are retained, together with source-choice observations and the
successful launch-time check. The plan reported 15 workspace source drifts
relative to the historical parent.

The subsequent [independent complete-result audit](../ipra-selected-native-bit-historical-pair-independent-audit/README.md)
passed. The original run remains at
`/tmp/ipra-selected-native-bit-historical-paired-run-01`. The result inherits
historical parent, package-transitive, dynamic and between-observation limits.
The Foundation wrapper's outer exit was not captured, although its inner Lake
exit and the independent verifier's exit were observed as zero. The external
alternate-checker and consistency-interpretation boundaries remain separate.
