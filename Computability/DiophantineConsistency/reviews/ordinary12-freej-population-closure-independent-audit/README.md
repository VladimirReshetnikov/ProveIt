# Independent preliminary population closure review

This reviews the source scan committed in `5d45113961` and the provider
comparison correction `9c04a203e2`. It is a **source-only, point-in-time
plan**: it does not freeze sources simultaneously, build any module, verify
compiler-reported imports, prove all package-transitive/dynamic ancestry, or
establish a graph application or iPRA theorem. The scanned sources still need
an independently reviewed frozen replay before they become compiled evidence.

The review reruns the author scan normally (exit 0, byte-identical
`scan.json`) and optimized (exit 1, explicit fail-closed guard). Independently
starting from each requested import, it checks unique source paths, current
source hashes, parsed source-declared imports, missing-leaf resolution,
reachability, and topological order on both provider sides. The preferred
free-J-provider closure has exactly nine missing source modules ending in
`ArithmeticHalfBinomialCompat`; the alternative endpoint-provider closure
has 33 ending in `FreeJPowerFinish`. Source scanning is based on the checked
text import syntax; it does not replace Lean `--deps` or runtime ancestry
verification.

For each free-J side the audit independently hashes all 97 inherited objects
and compares every resolved path and hash to the scan, then checks its
standalone `FreeJPowerFinish` object against the pinned independent power
audit. Against each 342-module endpoint overlay it finds 64 common object
paths, of which exactly these two hashes differ:

```
BusyBeaver/ZFC/KZip.olean
DiophantineConsistency/ModelDifferenceRing.olean
```

The original plan mistakenly attributed a six-object comparison to these
free-J overlays; `9c04a203e2` corrects it. The earlier six-object comparison
concerned the distinct 24-module window and endpoint overlays. The two actual
free-J differences already require care to avoid silently combining providers.
The proposed graph replay still needs fixed port, positivity, beta/radix and
other graph hypotheses and independently reviewed compiled outputs.

Run from the repository root:

```
python3 -I -S Computability/DiophantineConsistency/reviews/ordinary12-freej-population-closure-independent-audit/audit.py
```

Actual session 38461 exited 0 and did not launch Lean. It reads current files
and original `/tmp` overlays; missing or changed inputs fail closed. Hashes
are point-in-time checks, not a simultaneous or continuous snapshot.
