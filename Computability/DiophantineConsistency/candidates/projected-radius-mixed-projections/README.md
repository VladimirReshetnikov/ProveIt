# Projected integer quartics after signed Pell comparisons

Four complete equations improve the frozen862/863/865/891 direct-source
integer companions. Each has exact degree4 and uses every listed
coordinate.

| Directory | Integer variables | Quadratic rows | Collected terms | Height |
|---|---:|---:|---:|---:|
|`support32`|706|406|10465|2445790974704|
|`support16`|707|407|9129|2445790974704|
|`support8`|709|409|9034|2445790974704|
|`support4`|735|435|6017|63905891|

Each directory contains the literal equation, complete expanded
coefficient list and entire signed integer restoration certificate.
The frozen mixed994 parent, its109 guards and ordinary signed-index
proof are pinned. Restoration is over the integers first; the mixed
sign ledger and explicit positive-comparison lift apply afterward.
See `PROOF.md` for the complete proof order.

Reproduce from the repository root:

```
python3 -B Computability/DiophantineConsistency/candidates/projected-radius-mixed-projections/build.py --check
python3 -B Computability/DiophantineConsistency/candidates/projected-radius-mixed-projections/check.py
```

Both also pass with `-O`. The independent checker imports no optimizer.
All frozen parents, original archives and canonical pages are preserved.
These remain ordinary mathematical constructions with explicit source
dependencies; no new Lean/internal-ZFC endpoint or global minimum is
claimed.
