# Isolated model-arithmetic alternative for the 72/46 magnitude source

The previous selected magnitude source imports `ZRows.CoprimeSquares` only for `abs_eq_ι z`. That theorem's actual body is exactly `nonneg_iff.mp (abs_nonneg z)` with the same witness orientation. `ModelArithmetic.lean` directly imports `ModelDifferenceRing`, which declares `nonneg_iff`, and also imports the model arithmetic and order/tactic dependencies plausibly needed by the whole magnitude source.

The inert alternate source here makes exactly three textual substitutions: its import changes from `DiophantineConsistency.ZRows.CoprimeSquares` to `DiophantineConsistency.ModelArithmetic`; it removes the now-unused `ZRowsCoprimeSquares` namespace from `open`; and it replaces `abs_eq_ι z` with `nonneg_iff.mp (abs_nonneg z)`. All other source bytes, including the older discrete-f client and the generic magnitude/square interfaces, are identical. The original is not modified. All these Lean declarations and the sufficiency of the new import remain **unelaborated**.

The independent selection snapshot changes only that draft entry and its direct frontier: it drops the **direct** `ZRows.CoprimeSquares` edge and adds `ModelArithmetic`. Every other selected draft, the qualified literal reconciliation, original forward pin, and frontier entry are byte-for-byte unchanged. This does not show `ZRows.CoprimeSquares` is absent from the **transitive** imports, that `ModelArithmetic` or its dependencies have matching objects, that a coherent provider exists, or that any build will succeed. The previous selection remains intact.

The deterministic checker verifies exact substitutions and selection delta, source hashes and direct import declarations, all selected-draft edges/topological order, and source declarations for `nonneg_iff` and `abs_eq_ι`. It does not run Lean, evaluate tactics or authenticate compiled objects. From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/current2011-shear72-magnitude-modelarithmetic-selection/check.py | cmp - research/current2011-shear72-magnitude-modelarithmetic-selection/receipt.json
```

No Lean/build/staging or historical-file mutation was performed.
