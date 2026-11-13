# Rejected two-root compact/iPRA integration preflight

`run.py 5` was attempted once; it exited 1 before any theorem compilation.
The `lean --deps` output selected the first library root's nonexistent
`DiophantineConsistency/ArithmeticUnaryRecursion.olean`, even though the
selected object existed in the second overlay root. The script correctly
rejected the nonexistent dependency. The preflight's copied source, exact
`--deps` output and stderr are retained under `observations/stage-01/`.
The relevant observed diagnostic was:

```
RuntimeError: bad dependency: /tmp/compact12-ipra-coherent-endpoint-20261102/lib/DiophantineConsistency/ArithmeticUnaryRecursion.olean
```

The failed run produced no rebuilt object and makes no claim about the
correctness or coherence of either provider. A separate merged-root runner
will be used for any subsequent attempt; this directory is preserved as the
failed preflight and is not an input to that run.
