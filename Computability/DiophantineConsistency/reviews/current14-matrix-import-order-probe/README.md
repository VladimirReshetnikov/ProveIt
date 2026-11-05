# Matrix import-order diagnostics

Two minimal, isolated Lean import checks were run against the same guarded Foundation/Mathlib package overlay used by the failed structured-endpoint client. **Both actual Lean processes exited 1**, with no monitor stop and no output object:

| Import order | Captured diagnostic |
| --- | --- |
| Foundation `Vorspiel.Matrix`, then Mathlib `InvariantBasisNumber` | Loading Mathlib `Matrix.Defs` failed because `Matrix.map` was already present from Foundation. |
| Mathlib `InvariantBasisNumber`, then Foundation `Vorspiel.Matrix` | Loading Foundation failed because `Matrix.map.eq_1` was already present from Mathlib. |

The second message matches the observed endpoint failure. Thus swapping import order cannot make these two exact provider closures coexist; this does not by itself identify the best repair or prove an endpoint theorem. The enclosing diagnostic runner's separate observed exit was 0 because it successfully recorded the two expected failure results, not because either Lean check succeeded.

The source snapshots contain two different definitions of `Matrix.map`: a finite-vector map in the Foundation `Vorspiel.Matrix` source and a matrix-entry map in Mathlib `LinearAlgebra.Matrix.Defs`. The comment-aware [source trace](trace-result.json) also checks direct declared edges for these two routes:

- The port assembly reaches `Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber` through `CurrentKernel2011`, `WangTiles942Core`, `Mathlib.Tactic` and further Mathlib imports.
- The standard iPRA endpoint reaches `Foundation.Vorspiel.Matrix` through its current ZFC/negative-translation chain and Foundation's logic imports.

The trace hashes each source file it reads. These are source-declared edges, not authentication that every transitive object came from those current sources. Direct selected provider objects and their companion paths/hashes are preserved in [result.json](result.json); full transitive, dynamic and between-observation provenance remains inherited.

The two [source files](foundation_first/Probe.lean), [opposite-order source](mathlib_first/Probe.lean), complete stdout/stderr logs, owned-session receipts, commands and resource observations are retained here. Each run used a fresh `/tmp` root, `-M3000`, one Lean thread, nice 19, idle I/O, a 60-second bound and sampled session-RSS/host-memory/disk guards. The captured runner is preserved for inspection but refuses to reuse its existing output roots. The observed enclosing exec-session exit is separately recorded in [outer-observation.json](outer-observation.json).

The read-only [checker](check.py) verifies copied source/log hashes, both exit-1 receipts and diagnostics, current direct companion guards and the source trace. It does not launch Lean.

```
python3 -I -S -B path/to/current14-matrix-import-order-probe/check.py
```

The deterministic result is frozen in `check-result.json`.
