# Fail-closed direct-provider observation for the 72/46 source plan

This read-only checker examines the exact 15-draft selection in the separate private-Extraction/ModelArithmetic alternative. It verifies each selected source hash and declared direct import list, observes direct named `.olean` files in the eleven explicitly listed roots, records their paths, realpaths, hashes and two companion-presence flags, and reports multiple observed paths and same-basename inert draft alternatives. It compares the four historical 71/60 `.olean` hashes with recorded terminal values. It inspects simple first-namespace declaration names for lexical duplicates, without claiming to parse Lean or resolve every possible declaration scope.

The output status is deliberately **NOT_READY** and `--require-ready` exits 2 even if all bounded observations happen to look favorable. It does not select a provider, materialize drafts, prove that any source produced an observed object, inspect transitive/project/package/dynamic ancestry, enumerate all possible roots, determine actual Lean search precedence, or launch a build. Missing in these eleven roots means only unobserved there. Existing byte matches and symlink aliases are observations, not proof of compatible environments. `.olean.private` and `.olean.server` presence flags are incomplete companion checks and do not cover IR, shared libraries, plugins or toolchain state.

The selection deliberately uses the independently reviewed **private** `ArithmeticCarrier94Extraction` source snapshot SHA `415e74…`, matching the source recorded for the historical object `51fb88…`. The current workspace source SHA `5e7ef8…` differs by two omitted unused simp arguments; that object must not be represented as built from the current workspace bytes. The producer record remains inherited historical evidence, not a new source/object authentication. The model-arithmetic magnitude alternative removes `ZRows.CoprimeSquares` only as a **direct** import; its transitive closure has not been scanned.

A viable future preflight would have to pin a single ordered source/object search path, reject actual same-logical-name collisions or validate every allowed shadow, authenticate exact source/object producers and transitive/implicit/package/runtime dependencies, account for sidecars and toolchain, then build the unelaborated drafts in an isolated guarded environment and review the actual results. This script does not implement such authorization and will never claim readiness. No Lean/build/staging was performed.

From `Computability/DiophantineConsistency`, while the recorded local roots exist:

```
python3 -I -S -B research/current2011-shear72-bounded-provider-inventory/inspect.py > /tmp/shear72-provider-observation.json
python3 -I -S -B research/current2011-shear72-bounded-provider-inventory/inspect.py --require-ready
```

The second command intentionally exits 2. `observation.json` is a local point-in-time observation; later filesystem changes can change it. The source and selection pins are fail-closed.
