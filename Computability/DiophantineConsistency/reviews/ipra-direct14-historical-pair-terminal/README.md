# Direct-square 14 historical matched-pair terminal observation

The original launch session `9547` actually exited 0. Its full tool-provided
output is in `outer-terminal-observation.json`; the coordinator printed both
sibling exits 0 and `MATCHED_SELECTIVE_PASS 5 affected modules`. The separate
coordinator observation records exit 0 and binds the pair-state SHA-256
`4226646fca980a5f587b7760083000e8160a15ff09b076a301a63f6b1665af17`.
The exact launcher, both process logs, freezer and preparer observations, and
equal before/after preparation HEADs are preserved here.

Both sibling states and all ten module logs are copied here; each log was
rehashed against its recorded state during copying. Each sibling passed five
added modules and recorded all eight selected target diagnostics. The plan
reported 15 workspace source drifts relative to the historical parent.

The subsequent [independent complete-result audit](../ipra-direct14-historical-pair-independent-audit/README.md)
passed. The original run remains at
`/tmp/ipra-direct14-historical-paired-run-01`. The result inherits historical
parent, package-transitive, dynamic and between-observation boundaries. The
Foundation wrapper's outer exit was not captured, although its inner Lake exit
and the independent verifier's exit were observed as zero. The mathematical
identification of the selected translated consistency statement and the
display-to-Lean connection remain separate obligations.
