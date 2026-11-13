# Historical producer-time import drift and rebuild cone

Six selected fresh-header modules have matching successful producer receipts
in the nine-variable prefix. `check.py` compares each retained producer
source, output, log, and individually recorded direct-import hashes with the
80 client's final selected closure. Five modules have nine differing
producer-time direct-import hashes; one has none:

- `ModelArithmetic`: `ModelDifferenceRing`.
- `ModelExponentialCongruence`: `ArithmeticPellPowerRecovery`.
- `ModelRatioBounds`: `ArithmeticBinomExpansion`,
  `ArithmeticHalfBinomialSandwich`, and `ArithmeticPellCongruences`.
- `ModelProductPell`: `ArithmeticPellHalfIndex` and
  `ArithmeticPellStrongDivisibility`.
- `ArithmeticPellPigeonhole`: `ArithmeticPellRecurrence` and
  `ModelDifferenceRing`.

`DiscreteOrderedRingFacts` has no recorded direct-import mismatch. The exact
producer receipts, old and final paths and hashes, current state of each
producer path, source hashes, logs, and warning-policy data are recorded in
`observations/attempt01.json`, SHA-256
`d7e307b0d07e1856ebdedfbc598239450472cb40471c8576742f5875c38d2bb9`.
`observations-failed01.stderr` retains the initial strict comparison failure.
The absence of differing candidates in the earlier final search-path scan
does not rule out this drift: these are objects selected when the older
modules were originally produced. Lean did load the final client, but that
does not establish a coherent historical source-to-object rebuild. The hashes
alone do not establish that a mathematical theorem is unsound.

`survey.py` computes reverse reachability from those five modules in the
captured selected import graph. The resulting plan-only cone has 114 modules,
all with freshly read headers rather than reused 90-join closure headers, and
includes the fixed 80 endpoint. Each has one source file matching its module
basename outside observation snapshots; this is only a candidate source
location, not a checked source pin. The topological candidate order and paths
are in `observations/survey01.json`, SHA-256
`72ffa98b7c0762efbb5558668c3af4e1a84513e650302476821f6126a0d6303c`.

A coherent rebuild should first validate source/object associations and all
direct dependencies, build a fresh single provider union from the final
selected base, rebuild these five modules and every affected dependent in
serialized topological order, and pin sources, direct objects and companions
before and after each stage. It must then rescan the actual new closure and
recheck the endpoint axiom reports. The remaining 18 older unmatched producer
modules and any additional drift discovered by a complete audit may enlarge
the cone. Warning policies, package-transitive and dynamic dependencies, and
historical ancestry need their own explicit treatment. The survey is not an
authorization to run an unchecked rebuild, and it does not bind any external
PDF or JSON.
