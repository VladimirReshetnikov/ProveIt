# Independent result review: trace75 BFS field-cast bridge

**PASS.** The captured author result for `Trace75BFSFieldCastBridge` has
child, Lean and serialized-header exits 0, both exact named axiom reports,
and matching source, output, logs, pins and two direct imports. The author
reports actual outer tool exit 0; the wrapper records child exit 0 and stable
hashes. This review did not replay Lean.

`lookup_row` uses the explicit table lookup hypothesis for any of the 943
finite indices. `lookup_matches` additionally uses N>0 and the explicit
quantified symbolic field equalities, and concludes the corresponding model
lookup equalities. Neither theorem asserts a graph zero. The bridge is not a
halting or iPRA theorem and does not bind external coefficient files.

The accepted result SHA-256 is
`a844c52fefb362b2ac6f6d97a328c270610e321b1d70723560a9c7a29dab52a8`,
and its outer receipt SHA-256 is
`f7f791d26e7049aa3a5cfb9894df72d85f03c4c586bd36a240e18e4f41370a4e`.
The regular output
`/tmp/trace75-bfs-fieldcast-7s_1mnoi/Trace75BFSFieldCastBridge.olean`
has SHA-256 `5bdf2b8dce3c1dbbce5f62efc55a9d87df87e273ce4c985dac81d230e356aff2`.

The actual recorded Lean search order selects output, 15 guarded client roots,
the fresh union and package. The check rehashes those roots, 1,977 project and
80 outside bundles, their targets and first resolutions, and the captured
`CompactFieldCastBridge` subtree (333 project/29 outside). Historical
source-to-object, unrebuilt, package/dynamic ancestry and external-file limits
remain; these checks do not establish full ancestry.

`check.py` SHA-256 `ac7c9b6d5574110188b53b2dda6fa7c665e65a7aab7c5486fc8f1ebfa6e8407d`;
`result.txt` SHA-256 `74887b8366b67088c7d7e8020995061d4aa03e65590f6c49eeada1612808b131`.
