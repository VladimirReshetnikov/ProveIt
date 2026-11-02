# AQ16 historical matched-pair retry terminal observation

Fresh run-02 launch session `2984` actually exited 0. Its complete
tool-provided output is in `outer-terminal-observation.json`; the coordinator
printed both sibling exits 0 and `MATCHED_SELECTIVE_PASS 52 affected modules`.
The separate coordinator observation records exit 0 and binds pair-state
SHA-256 `e37d8bb577d7a2188929a9d8044eb48898c2f76191ce77d33237c149ae3e1e7b`.
The exact retry launcher, both process logs, freezer and preparer observations,
and equal before/after preparation HEADs are retained here.

Both sibling states and all 104 module logs are copied here; each log was
rehashed against its state. Each sibling passed 52 additions and recorded 127
selected diagnostics. The plan reported 15 workspace source drifts relative
to the historical parent. Fresh run-02 seeds were independently prepared from
the original parent; partial run-01 peer artifacts were not reused. The
earlier [run-01 interruption](../ipra-aq16-historical-interrupted-run-01/README.md)
remains a distinct exit-143 observation with unknown cause.

The subsequent [independent complete-result audit](../ipra-aq16-historical-retry-pair-independent-audit/README.md)
passed. The original run remains at
`/tmp/ipra-aq16-historical-paired-run-02`. The result inherits historical
parent, package-transitive, dynamic and between-observation limitations. The
Foundation wrapper's outer exit was not captured, although its inner Lake exit
and the independent verifier's exit were observed as zero. The mathematical
identification of the selected translated consistency statement and the
display-to-Lean transcription boundary remain separate obligations.
