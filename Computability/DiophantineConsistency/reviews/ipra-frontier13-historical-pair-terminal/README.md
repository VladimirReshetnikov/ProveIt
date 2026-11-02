# Joint 13-variable historical matched-pair terminal observation

Launch session `83295` actually exited 0. Its complete tool-provided output is
in `outer-terminal-observation.json`; the coordinator printed both sibling
exits 0 and `MATCHED_SELECTIVE_PASS 8 affected modules`. The separate
coordinator observation records exit 0 and binds the pair-state SHA-256
`bc1e548b6a35d05569cdf53c941a9f728e649edd0f29ea769dc691986fbc44a5`.
The exact launcher, both process logs, freezer and preparer observations, and
equal before/after preparation HEADs are preserved here.

Both sibling states and all 16 module logs are copied here; each log was
rehashed against its state. Each sibling passed all eight additions and 13
selected diagnostics, split between the square-sums and product endpoints.
The two selected tracked package source rows and frozen source bytes are
retained, together with the separate package-choice observation and its
successful launch-time check. The plan reported 15 workspace source drifts
relative to the historical parent.

The subsequent [independent complete-result audit](../ipra-frontier13-historical-pair-independent-audit/README.md)
passed. The original run remains at
`/tmp/ipra-frontier13-historical-paired-run-01`. The result inherits historical
parent, package-transitive, dynamic and between-observation boundaries. The
Foundation wrapper's outer exit was not captured, although its inner Lake exit
and the independent verifier's exit were observed as zero. The mathematical
identification of the selected translated consistency statement and the
display-to-Lean transcription boundary remain separate obligations.
