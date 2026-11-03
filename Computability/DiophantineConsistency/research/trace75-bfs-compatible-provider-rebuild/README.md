# Proposed trace75 replay preserving the BFS halt provider

This runner is a **held, unreviewed proposal** derived from the earlier
14-stage trace75 replay. That replay replaced eight BFS baseline modules with
trace supplements. A static walk of the captured `DirectBFSHaltPellSeed`
serialized closure found all eight names in that closure. Thus the earlier
trace union's successful carry check does not establish a coherent halt join.

The proposed runner now retains every selected BFS baseline object, adds only
supplements absent from the baseline, and rebuilds the 31 trace stages selected
by the [combined-seed plan](../trace75-bfs-compatible-provider-plan/README.md).
It intends to compare the selected `DirectBFSBandCarry` and
`DirectBFSHaltPellSeed` closures with the captured BFS companions. Four affected
modules already present in the baseline retain their inherited ancestry. The
read-only preflight passed with 1,931 baseline modules, 15 supplemental inputs,
80 outside providers and 31 stages. Fifteen actual-function policy controls
passed, including rejection of a same-byte symlink substituted for a copied
source. An [independent scoped review](../../reviews/trace75-bfs-compatible-provider-runner-independent/README.md)
also checked the outer child-status gate.

The reviewed replay at `observations/attempt01/` passed all 31 stages, and
the outer tool session 33900 actually exited 0. The selected closure contains
901 project and 44 outside objects. The BFS carry and halt-seed closures match
the earlier captured project companion hashes, with 46/6 and 855/44
project/outside modules respectively. The new trace endpoint's selected
closure has 241/27. The [independent result audit](../../reviews/trace75-bfs-compatible-provider-result-independent/README.md)
rechecks the stages, union, receipts and selected headers. The four affected
retained baseline objects, unrebuilt project source ancestry and package/dynamic
ancestry remain inherited. This replay does not yet include the trace75 reverse
chain, a joined iPRA endpoint, or an external file binding.
