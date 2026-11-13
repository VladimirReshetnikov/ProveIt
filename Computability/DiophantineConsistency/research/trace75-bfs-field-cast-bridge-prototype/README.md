# Direct-BFS field-cast bridge

This client adapts the existing generic direct-BFS lookup bridge
with the trace75 tile-match import. Its `lookup_row` and `lookup_matches`
theorems translate explicit finite row-field equalities into model lookup
equalities. Their hypotheses do not assert a graph zero. The author check
passed with tool-observed outer exit 0 and child, Lean and header exits 0.
Independent post-audit passed in `reviews/trace75-bfs-field-cast-result-independent/`.

The runner checks fifteen accepted regular client roots, the 1,977-object
fresh union, 80 outside providers and the captured BFS `CompactFieldCastBridge`
subtree (333 project objects), including companions. The exact log policy
requires both named axiom reports; read-only preflight and 20 controls passed,
including rejection of either missing report. The result
`observations/attempt01/result.json` has SHA-256
`a844c52fefb362b2ac6f6d97a328c270610e321b1d70723560a9c7a29dab52a8`;
`observations/outer-attempt01/terminal.json` has SHA-256
`f7f791d26e7049aa3a5cfb9894df72d85f03c4c586bd36a240e18e4f41370a4e`.
The object `/tmp/trace75-bfs-fieldcast-7s_1mnoi/Trace75BFSFieldCastBridge.olean`
has SHA-256 `5bdf2b8dce3c1dbbce5f62efc55a9d87df87e273ce4c985dac81d230e356aff2`.
Historical unrebuilt-source, package/dynamic ancestry and external
coefficient-file binding remain outside this check; this is not a machine-halt
or iPRA theorem.
