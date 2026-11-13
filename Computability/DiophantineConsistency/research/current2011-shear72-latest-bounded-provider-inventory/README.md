# Fail-closed provider observation for the latest 72/46 source selection

This separate read-only observation reruns the previous bounded direct-name scan against `current2011-shear72-local-nozero-bridge-selection/selection.json`. That selection contains the qualified-literal forward rewire, the ModelArithmetic magnitude alternative, the retained private Extraction source, the lighter Carrier65/order alternative, and the local no-zero bridge. Relative to the earlier private-Extraction selection, the **direct draft frontier** removes `HAExpressionNoZeroEquiv` and `ModelCarrierSpheres` and adds `Carrier65`, `Mathlib.Tactic.ByContra` and `Mathlib.Tactic.Linarith`. This says nothing about transitive imports.

The eleven sampled object roots are byte-identical to the prior inventory's explicit root list. The observer rechecks selected source hashes and import headers, exact logical names, bounded `.olean` presence/hashes/realpaths and two sidecar-presence flags; it reports same-basename inert draft alternatives and limited lexical declaration collisions. Four historical 71/60 object hashes are compared with their recorded values. It does not make these roots a future Lean search path, determine implicit or dynamic imports, inspect every companion, verify package/transitive ancestry, or prove source-to-object production. It is not exhaustive: no observed candidate means unobserved in these roots, not globally absent.

At the captured observation, all latest direct frontier names had a candidate in these roots, but all 15 selected draft objects remained unobserved. The newly direct `Carrier65` has two distinct observed object hashes: `10608a…` in the 71/94 overlay and `50fcfd…` in the workspace build root. Those distinct bytes are a concrete shadowing boundary, not by themselves proof that Lean would accept or reject either object. The observed Mathlib and tactic duplicates are aliases of the same real paths in this sample.

The selected Extraction source is the previously reviewed **private** `415e74…` variant; the observer separately reports the different current workspace source `5e7ef8…`. The observed historical Extraction object is not a workspace-source build. Removing the direct `ModelCarrierSpheres` edge does not establish that its old sphere provider's different `ModelDifferenceRing` object is harmless or eliminate every possible transitive overlap. The alternative source and all 15 draft modules remain unelaborated.

The checker is intentionally fail-closed: it always reports `NOT_READY`; `--require-ready` exits 2, regardless of favorable observations. This is not authorization or a launch plan. A future preflight still needs one fixed ordered provider map, conflict handling, source/object and complete package/runtime ancestry checks, sidecars, toolchain and separately reviewed guarded builds. No Lean/build/staging was performed.

From `Computability/DiophantineConsistency`, while the named temporary roots exist:

```
python3 -I -S -B research/current2011-shear72-latest-bounded-provider-inventory/inspect.py > /tmp/shear72-latest-provider-observation.json
python3 -I -S -B research/current2011-shear72-latest-bounded-provider-inventory/inspect.py --require-ready
```

The second command deliberately exits 2. `observation.json` records one point-in-time filesystem state and can change later.
