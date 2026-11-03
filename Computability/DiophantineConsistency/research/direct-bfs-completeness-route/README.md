# Direct-BFS 80-row completeness route

This note tracks the direct-enumeration BFS symbolic kernel used by the retained 80-row JSON graph. Its coefficient is different from the original-table symbolic kernel used in the other 80-operation completeness route. External byte reconstruction matches the direct symbolic recipe to the retained JSON coefficient, but there is no Lean theorem binding that file's bytes to the symbolic expression.

The checked direction from a positive graph zero to an internal decimal215 halt is `../direct-bfs-80-model-halt-prototype/`. It goes through a direct local tiling word, a finite checked color/row conjugacy and its model-valued inverse, an original-table local word, and the selected marked-word and Wang soundness modules. Its selected-header and prior-provider reconciliation has been independently reviewed in `../../reviews/direct-bfs-model-halt-serialized-independent/`; the remaining historical, package-transitive and dynamic ancestry limits are recorded in `../direct-bfs-80-model-halt-serialized-audit/`.

For the converse, the following author-checked steps now work in every IΣ₁ model:

- An internal machine halt yields a Σ₁-definable direct local word by original→direct color/row transport (`../direct-bfs-halt-word-prototype/` and `../direct-bfs-model-forward-word-prototype/`).
- One such row and geometry supports a family of positive bounded selector/copy/dummy packed words for every Σ₁-definable dummy pulse, with exact digit recovery (`../direct-bfs-halt-packed-family-prototype/`).
- With a zero normalized origin dummy, the direct word satisfies the concrete low-mask origin and per-cell fields (`../direct-bfs-word-low-fields-prototype/`). The direct kernel product bound, block-size sum and positive-block lemmas are checked in `../direct-bfs-cell-product-prototype/`, `../direct-bfs-kernel-block-size-prototype/`, and `../direct-bfs-word-block-positive-prototype/`.
- For a direct local word with positive stride below its length, ordinary high-mask no-carry at all indices implies both the adjusted origin and non-origin high fields (`../direct-bfs-origin-block-residue-prototype/`).

The conditional composition deriving `PackingInput` from all-index high-mask safety is checked in `../direct-bfs-high-only-packing-prototype/`; its all-index premise is not established. The sharper direct-cell bound is checked in `../direct-bfs-cell-sharp-size-prototype/`. The direct high-padding size and phase-zero no-carry are checked in `../direct-bfs-high-padding-size-prototype/` and `../direct-bfs-phase-zero-high-prototype/`. The direct symbolic and temporal product-carry inputs are checked in `../direct-bfs-constructed-carry-prototype/` and `../direct-bfs-temporal-constructed-carry-prototype/`. The other high-mask phase classes remain open.

The checked `../direct-bfs-active-phase-packing-prototype/` reduces the high-mask premise to six explicit remaining active phase classes; proving those direct-family classes remains open. The remaining work also includes selecting a supported dummy pulse with calibrated rank on the same row, deriving the compatible Pell and graph witnesses, and joining both model directions to the iPRA proof-existence adapter with a coherent, audited provider. Each step also needs the precise scalar geometry and mask assumptions required by the relevant theorem. No direct-BFS model equivalence, iPRA endpoint, or formal JSON binding is claimed by this note. The previously checked theorem packets are author checks with the ancestry and no-independent-replay qualifications stated in their individual READMEs.

Subsequent work proves the direct high-mask packing under explicit scalar bounds and derives a canonical packing from a halt under the same bounds; see `../direct-bfs-halt-canonical-packing-prototype/`. A [later join](../direct-bfs-halt-packing-prototype/README.md) discharges all three scalar bounds for the fixed symbolic masks; it still assumes a definable dummy whose value at zero is even. The [conditional controller unit](../direct-bfs-controller-unit-prototype/README.md) and [chosen-rank construction](../direct-bfs-generic-chosen-rank-prototype/README.md) apply to any model kernel with the stated BFS residue. The [halt-to-chosen-rank join](../direct-bfs-halt-chosen-rank-prototype/README.md) supplies the initial packing and proves stability for every admissible pulse, producing packing and the calibrated rank for the same canonical row and pulse under the explicit **model-side** kernel-residue premise. Deriving Pell and graph witnesses remains open; the next paragraph records the later symbolic-residue specialization. The [independent controller review](../../reviews/direct-bfs-generic-rank-unit-independent/README.md), [packing review](../../reviews/direct-bfs-halt-packing-independent/README.md), and [chosen-rank review](../../reviews/direct-bfs-halt-chosen-rank-independent/README.md) audit selected inputs and receipts, not new Lean replays or full ancestry.

The later [halt-to-rank client](../direct-bfs-halt-rank-prototype/README.md)
discharges that model-side residue for the exact same symbolic BFS kernel,
using a separate natural-to-model residue theorem. Internal halt is its only
theorem hypothesis; Pell witnesses, a graph-zero construction, formal binding
of the retained coefficient files, and a coherent complete ancestry audit
remain open. Its author check is recorded.
An [independent source and receipt review](../../reviews/direct-bfs-model-residue-independent/README.md)
checks the natural-to-model cast and exact-kernel join, without a new Lean
replay or full ancestry audit.

A [later seed and transport join](../direct-bfs-halt-pell-seed-prototype/README.md)
constructs the outer and auxiliary Pell seed families and a positive shifted
transport witness from the same internally halted, calibrated BFS packed word.
The [first-carrier join](../direct-bfs-halt-first-seed-prototype/README.md)
also produces its positive first-carrier equations on that same word. The
graph valuation remains open, as do the external coefficient binding and
coherent combined provider audit.
An [independent source and receipt review](../../reviews/direct-bfs-halt-pell-seed-independent/README.md)
checks the common word and pulse throughout this join, without a new Lean
replay or full ancestry audit.
