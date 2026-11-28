# Import record for the readable edition of grh-lean

The proof now lives in [`Lean/grh`](../../Lean/grh/README.md).
On 27 November 2026, ProveIt imported all 818 files of the upstream `grh`
directory byte for byte from commit `72fead102f663d5c7a407964a13dc0cf9d977207`
(25 November 2026). The reports merged into the [article](../../Article/README.md)
use this revision. The upstream repository also provides a compact edition.
[Original source tree](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh)

The [theorem statements](../../Lean/grh/src/Statements.lean) and
[proofs](../../Lean/grh/src/Main.lean) cover RH and GRH for Dirichlet
L-functions. The [package README](../../Lean/grh/README.md) gives build and
axiom-check commands for the separately pinned Lean 4.35.0 and Mathlib.
Run those commands from `Analysis/GeneralizedRiemannHypothesis/Lean/grh`.
The repository's `GRHArticle` target uses Lean 4.32.0.

The proof was imported under the Apache License 2.0.
[License](../../Lean/grh/LICENSE) · [Notice](../../Lean/grh/NOTICE) · [Attribution](../../Lean/grh/ATTRIBUTION.md)
