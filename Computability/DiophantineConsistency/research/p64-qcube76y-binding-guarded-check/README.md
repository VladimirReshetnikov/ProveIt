# Guarded 76Y/77 ring binding check

The [bounded Lean check](observations/attempt01/result.json) exited 0 and
reported `[propext]` for all eight graph-binding declarations, with no
warnings or `sorryAx`. It checks the five residuals and output under the
signed `y=V+e` substitution, plus auxiliary/output invariance under replacing
`y` by another ring element with the same square. It does not prove that the
new `y` or reconstructed `e` are positive, either model-zero direction, or an
iPRA endpoint.

The runner pinned source, Lean executable, the accepted 76Y graph object and
77 parent object, their companions, and earlier-path shadow absences before
and after. The check used `-M2400`, nice 19, idle I/O, a 120-second bound,
sampled 3.5 GiB process-group RSS and 10 GiB `MemAvailable` stops, alongside
the separately managed current14 rebuild. It recorded 43 group-RSS samples,
sampled maximum 2,045,263,872 bytes, and minimum available memory
18,737,033,216 bytes; no stop fired. These are sampled observations, not hard
reservations. Captured-provider transitive and dynamic ancestry remains
inherited. The shared missing-child helper's finished/live controls are
recorded in the [graph check packet](../p64-qcube76-independent-y-guarded-check/README.md).

The object `/tmp/p64-qcube76y-binding-priority-check01/P64QCube76YBinding.olean`
has SHA-256 `e53974f19914918cc77be47082e842f33f334de4ff3821a5127f9d515ca75185`.
The exact command, input guards, timings and log hash are in the
[receipt](observations/attempt01/result.json); the eight reports are in the
[log](observations/attempt01/compile.log). The unchanged source SHA-256 is
`917aece0aa983dcd5947baed77eb80725d3f99e2b4fd5ca4cac0901c1adadfc6`;
the runner SHA-256 is
`6a5c8bd574ff1bf10a15e14032d0254c833ed2f11a014093ff750b8b5777aa68`.
