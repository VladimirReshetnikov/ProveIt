# Successful MF natural-sum port-cast diagnostic

`port_natural_cast` proves that the integer cast of the natural sum `CurrentMasks2011.highPort + CurrentMasks2011.beta` equals `CurrentWindowCarry2011.ports 3`. A small parametric lemma applies `Nat.cast_add` before specializing to the already checked port recipe. The declaration does not itself identify the explicit radix digit recipe or bytes with that sum.

Observed runner session 63979 and both Lean commands exited 0. The generic lemma reports `[propext]`; the port theorem reports `[propext, Classical.choice, Quot.sound]`. The inherited runner's message says `PASS current2011 MF shift identities`, but the compiled source has precisely these two cast statements. Its successful object `/tmp/current2011-mf-port-cast-probe-20261105/CurrentMFPortCast.olean` has SHA-256 `e129e4fd5e9d67b85a06268b31fc7cf54883e19565b93bbff7c23f5505d21c43`. The runner rechecked 180 direct/companion/shadow slots and source/base preflights before and after.

Lean ran with `-M2800`, one thread, nice 19, idle I/O and a 180-second foreground timeout, without an automatic process-group RSS or host-memory stop. The source-built base/provider ancestry is inherited; this is not an independent base rebuild or a full dynamic/package-transitive trace. A separate byte-decoder composition remains to be checked.

SHA-256: source `3671e374f9ff61a3e4f8fb62e7276b969eb650cdbf9e65911a05432d188a0f77`; runner `48194991ea4a326d5bd6b3fbafc0d83ea65fe3c2b7be592cdd4c835aad8a5b85`; state `198582049bf32060687651ef485b56e939003877de4b34e1c582a93350aa4b7d`; compile `0f370afc527e6dc08cfc7e159a2f0632d8f35916d8f31587ebbc7f36e4b88056`; outer observation `98284247cf8e00b87e49809be1754dd2783cc53edb87dcbd7707f23db94c439b`.
