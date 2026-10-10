# Integration notes: mixed-point elimination

## Checkpoint and safe destination

Repository: VladimirReshetnikov/ProveIt.
Inspected commit: `afed07429d3d37eceb6c8e9e54cf4da2d3f39d53`.
Inspected chapter: `Analysis/Polylogarithms/docs/manuscript/chapters/04-depth.tex`.
Chapter blob: `6171912ff7724784cabb789a066c61223ab298bc`.

No remote writes were performed. Prefer an additive directory
`Analysis/Polylogarithms/docs/articles/mixed-gap-reductions/` for this bundle.
Before editing the unified manuscript, compare its current version against
this pinned checkpoint. Preserve concurrent research and editorial history.

## Label-level changes

| Existing label or passage | Proposed mathematical update |
|---|---|
| `gauss:eq:g51`, `gauss:eq:g42`, `gauss:eq:g33`, `gauss:eq:g24`, `gauss:eq:g15` | Promote the five displayed identities from numerical candidates to proved corollaries of the explicit parity solver. Retain the equations; add the analytic proof or the five-by-five determinant-eight certificate. |
| `gauss:eq:wt5-sporadic` | Promote to a theorem and explain that its row is 960 times shuffle(1,4) minus 224 times shuffle(2,3). Both shuffle rows give a spanning bound of two for the four Gaussian imaginary coordinates, modulo single products. |
| `mixed:eq:gauss-w2` | Prove with D11 = F11 + Li2 and Landen's dilogarithm identity, on the stated branch. |
| `mixed:eq:eis-w2` | Prove directly from D11 = F11 + Li2 and the elementary root-of-unity single values. |
| `mixed:thm:parallel` | Replace the additional-generator interpretation by the all-weight no-extra-mixed-directions theorem. Both real weight-five and imaginary weight-six proposed survivors reduce to single values. |
| “exactly two new constants” in the level-three and level-four mixed discussions | Remove as a mathematical claim. An explicitly defined historical bounded-search residual count may remain, provided the new identities are stated to eliminate it. |
| `mixed:sec:eisdim` and `mixed:sec:gauss` quotient summaries | Do not derive new exact numerical dimensions. Certified non-mixed upper bounds remain upper bounds after reciprocal mixed points are added; the historical non-mixed ranks are not replayed here. |
| `mixed:sec:eval` | Add the positive-measure midpoint evaluator and its explicit geometric tail as a rigorous alternative to empirical acceleration. |

## Supplement

`manuscript_supplement.tex` is a self-contained mathematical section fragment
using AMS math and existing `theorem`/`proof` environments. Its local polylog
macro and `gapcont:` labels avoid the existing labels. It can be inserted into
Chapter 4 or adapted as a replacement section. It includes the general gap
formula, the span statement, the four final mixed-target formulas, and the
all-angle last-index-one formulas.

The standalone article contains the complete parity solver, the five Gaussian
weight-six reductions, exact certificate construction, and further research
questions. Do not silently remove the old numerical receipts; classify them as
historical evidence, distinct from the current proofs and exact certificates.

## Statements that must remain qualified

The results do not prove independence, minimal depth, or transcendence. No
proof-assistant formalization has been performed. The general parity theorem is
known and credited to the literature. This continuation does not claim
literature-wide priority for all specializations. It does supply explicit proofs
for the selected repository targets and correct the proposed mixed extensions.
