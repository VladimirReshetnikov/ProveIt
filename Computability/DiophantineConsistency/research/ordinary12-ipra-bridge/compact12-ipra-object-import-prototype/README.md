# Serialized-import metadata probe

The bounded single-object diagnostic in `observations/attempt01` used
`Lean.readModuleData` on the compact-selected
`AdaptiveEquationSyntax2011.olean`. It exited 0 in 2.03 seconds and printed
these actual direct import entries:

```
Init
Init
DiophantineConsistency.CurrentKernelData2011
DiophantineConsistency.NaturalExpressionSemiring
```

The helper source and target object hashes were unchanged across that
invocation. The exact source, output and command receipt are retained. This
is a metadata diagnostic, not a Lean theorem, source-to-object audit or proof
that the 59-module integration rebuild cone is complete. The previous, larger
`import Lean` probe stalled and was interrupted; its evidence is retained in
the neighboring integration-build packet.

The bounded batched `scan.py` inventory was subsequently run as
`python3 -I -B .../compact12-ipra-object-import-prototype/scan.py` and exited
0. It read the actual serialized imports of all 441 pinned endpoint objects
in 37 batches. Their `DiophantineConsistency.*` direct-import sets exactly
matched the corresponding pinned source sets; none escaped the 441-module
source closure. The union of those two sets gives 75 affected modules,
including 15 conflict seeds, with no additional stale nine-base endpoint
object beyond the 59 omissions in the prepared overlay. Each batch's output
and the full machine-readable result are retained in `observations/attempt02`.
The inventory recorded unchanged helper, pinned sources, chosen objects and
selected overlay bytes at its checks. `scan.py` SHA-256 is
`0e0cb295489f088e0463ad2b03e75af5950d74034dd2904cb860620483f4a830` and
`result.json` SHA-256 is
`909a5db211132e97f6ebe8787c87a8861e9b896a65a3ee183c17fe86ec1bf3d9`.

This is stronger evidence for the 59-module starting rebuild cone, **not**
a complete dependency audit or an integration proof. The analysis restricts
its graph to the `DiophantineConsistency.*` namespace and this endpoint's
441 source modules; other serialized imports include `BusyBeaver.*`,
`ZFCinPA.*`, `PAHF.*`, package and Lean modules. Their own ancestry, the
compact graph suffix, dynamic loading and source-to-object correspondence
remain to be checked. The run is an author-side point-in-time observation,
not an independently reproduced inventory.
