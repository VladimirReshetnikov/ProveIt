# Failed compiler attempts

These receipts are preserved separately from accepted checks. The two unsplit
batch002 attempts exited -9; the shared environment reported memory-limit kills.
The second used one Lean worker. No false theorem was accepted.

The first six-block attempt used a 2 GiB process limit and default recursion and
heartbeat options. It returned an error whose pretty printer itself exceeded
recursion depth, so the underlying exception was not exposed in that log. We do
not identify it more precisely than the evidence permits. A separate untrusted
`#eval` diagnostic returned true for block24; this was not used as a proof.

An attempted diagnostic printer option was rejected at process startup. The
accepted configuration removes that flag and uses one worker, a 3 GiB process
limit, maxRecDepth65536, and maxHeartbeats8000000. The exact same half-batch source
then compiled successfully. Changing resource options does not add proof axioms.

The included failed log texts match the SHA-256 recorded by the corresponding
receipts. The unsplit source is included only to document the earlier resource
failure and is not a build input in source-pins.json.
