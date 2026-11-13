# Direct-import plan for a fresh-provider reverse replay

The read-only planner inventories the thirteen reverse-chain sources ending in
`Trace75BFSHaltGraph` against the retained fresh trace75/BFS provider. It checks
source order, resolves each direct non-stage import through that provider and
the package/core paths, and records source and object hashes. It does **not**
run Lean, inspect the serialized transitive closure, prove source/object
ancestry, or establish the model converse or iPRA endpoint. Any later replay
must separately authenticate and monitor its baseline, source snapshots,
companions, outside providers and actual selected closure.

The observed `plan-attempt01/result.json` passed with thirteen staged modules,
eleven distinct direct project inputs and four direct outside inputs. The
selected `ScaledReverseStart` and `ScaledAuxiliarySeed` objects have the same
hashes as the earlier mixed-overlay reverse-data check. This is evidence for a
concrete replay order, not evidence that those thirteen stages compile on the
fresh provider. One direct outside import, `Mathlib.Algebra.Order.Ring.Basic`,
is not among the parent BFS replay's 80 recorded outside names; a replay must
capture it separately. The earlier baseline, supplements and outside/package/
dynamic ancestry retain the limitations recorded in the parent replay.

**Provider correction.** The retained parent union replaces eight BFS baseline
objects with trace-specific supplements. All eight names occur in the captured
`DirectBFSHaltPellSeed` serialized closure. Consequently this thirteen-stage
plan is not, by itself, a repair of the combined halt chain. A static walk also
finds additional trace dependencies of those eight objects that were not among
the earlier 14 rebuilt stages. The held compatible-provider investigation is
in `../trace75-bfs-compatible-provider-rebuild/`.
