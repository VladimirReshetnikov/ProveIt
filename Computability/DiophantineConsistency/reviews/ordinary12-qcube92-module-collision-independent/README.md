# Independent audit of the FreeJRootBinding module collision

The first 92-operation halt join failed before elaborating its theorem. Lean
reported that importing `DiophantineConsistency.FreeJRootBinding` found the
existing declaration `FreeJRootBinding.rhs` already supplied by the distinct
top-level module `FreeJRootBinding`. The old 92 existence object imports the
top-level module. The 94-model import graph reaches the namespaced module;
both binding sources declare their definitions in the Lean namespace
`FreeJRootBinding`, so importing both modules can redeclare the same names.

The replacement existence source changes the binding import to
`DiophantineConsistency.FreeJRootBinding` and changes its own namespace; its
remaining bytes are unchanged. Its captured author run succeeded with the
same 1,292-object selected union that produced the failed halt attempt. Its
actual serialized header imports `QCube92Model` and
`DiophantineConsistency.FreeJRootBinding`, with no top-level binding import.
The imported namespaced binding object has SHA-256 `58860b9c…`, matching the
94 union and the earlier retained successful divisibility replay object. Its
newly read serialized direct imports match the earlier captured inventory.

Traversing the selected-project headers gives 38 names for the replacement
existence root, 734 for `CompactBytePortsModelIff`, and 700 for
`CompactSymbolicModelUnconditionalIff`, including each root. All three
closures reach the namespaced binding and exclude the top-level binding and
old existence module. Every selected project ancestor matches the recorded
union object and the object whose header was captured. Thus the replacement
removes the **observed selected-project duplicate-import cause**. It does not
by itself prove that a subsequently assembled halt endpoint compiles or that
all other imports are compatible.

The guarded reader ran once on the replacement existence object and the
namespaced binding object, with source, object and receipt hashes checked
before and after. It exited zero in approximately 0.34 seconds. The
pre-launch sample showed 18,681,460 KiB available and no Lean process; the
post-launch sample showed 18,711,340 KiB and no Lean process. Launch required
at least 8 GiB available and fewer than two existing Lean processes. The
reader had a 3-GiB Lean cap and a 60-second timeout. These point samples do
not exclude overlap or memory dips between observations.

The captured result is `observations/attempt01/result.json`, SHA-256
`d3f68298e20708297524c0e0e540091e184d451972fdb801ab9081c227779934`.
`audit.py` read-only reparses both captured headers and independently
reconstructs the three closures, checks all recorded selected objects,
compares the failed and replacement author unions, and verifies the exact
source rewrite. Run `python3 -I -S -B audit.py`; its successful captured
output is `observations/audit01.stdout`. Both scripts depend on the retained
absolute `/tmp` objects and providers.

The ancestor calculation inherits the prior selected-project header
inventory. The replacement root has 20 and the two 94 roots each have 44
outside names; package-transitive and dynamic imports were not traversed.
The receipts and selected hash matches do not establish complete historical
source-to-object provenance. This is not an independent kernel replay, a
proof of the final halt client, or an internal iPRA derivation.
