# Independent round 5 proof review

Review target: local candidates against `e1c8914bc7064d9a8e7c06171a18069a949badd0`.
Status: **source-level review only; no Lean executable, compilation, kernel check, axiom print, or timing run.** No installation or remote execution was requested. No upstream file or branch was changed.

## Closing novelty update

The late proposal scan at `91dce223cda86c0755b8a9b2504f84be04443fce` excludes the separately reviewed PhysicalOrder candidate as an exact duplicate of packet `zh`, also addressed by `zj`. The source-level correctness evidence remains useful but its 24 lines are not new. The closing baseline reviewer read the seven newly substantive reports plus 37 pointers/notes at `91dce223cda86c0755b8a9b2504f84be04443fce` and retained the other three small families: **9 new lines total**. See `ADDITIONAL_CANDIDATES.md`.

## Findings available now

1. `IterationSize.iterate_depth`: accept as a small source-level simplification. `Rep.depth` is defined as `r.expression.depth` (`RepresentationSize.lean:112`). The old proof establishes equality of the two expressions by `rfl` and applies `congrArg Expr.depth`; applying the same function to definitionally equal expressions is itself definitionally equal. The direct `rfl` preserves the statement and all representation constructors. The local irreducibility setting on `Nat.unpair` is unchanged. Full file: **163 → 161**, net 2 lines.
2. `SidonPositions.weight_injective`: accept at source level. Applying `congrArg (fun n => n + n)` to `h : weight m i = weight m j` establishes equality of the diagonal pair sums. `weight_sum_eq_iff i i j j` returns `(i = j ∧ i = j) ∨ (i = j ∧ i = j)`; either first projection proves the goal. Repeated indices are explicitly allowed by that theorem, including `m = 0`.
3. `SidonPositions.pairWeight_injective`: mathematical argument is sound; exact tactic elaboration remains untested. In the swapped case let the first/second indices of `p` be `a,b`, and those of `q` be `c,d`. The hypotheses are `a = d`, `b = c`, `a ≤ b`, `c ≤ d`, so all four indices are equal. After `Subtype.ext`, `Prod.ext`, and `Fin.ext`, both goals are natural-valued equalities. The proposed `omega` uses the local order hypotheses and the swapped equalities. Official Lean `v4.32.0` frontend source explicitly processes `Fin` equality via `Fin.val_congr` and `Fin` ordering via `Fin.val_le_of_le` (lines 440–459); see `OmegaFinSupport.txt` and its Git-blob binding receipt. This closes the source-level question of whether those hypotheses are supported. No nonlinear weight calculation is reopened. This is an automation tradeoff, not a new theorem or a performance claim.

The two Sidon wrappers form **one small family**, not two independently novel mathematical directions. Their combined net reduction is 4 physical lines.

## Assumed-applied Sidon baseline: composition checked

The prior Sidon polarization proposal changes only `weight_sum_eq_iff`, adding `Zify` and `LinearCombination` imports and replacing its internal product-reconstruction path. It does not change the public statement or either injectivity wrapper.

Prior source:
- Self-contained copy: `fixtures/sidon_assumed_prior.patch`; original workspace provenance is `lean_simplification_round4_20261026/late_novelty_review/remote/archive_further_extracted/diophantine-lean-further-deltas-2026-10-26/arithmetic/patches/sidon-moment.patch`.
- the same archive's `report/report.tex:524–538`.

The two patches were applied in both orders with `patch --batch --fuzz=0`. Both orders succeeded and produced **byte-identical** files. Run `python replay_composition.py` or `python -O replay_composition.py`; both regenerate `composition_check.json` and `SidonPositions.assumed_applied_plus_round5.lean` using only the included fixtures and the standard `patch` executable. The new receipt contains no absolute external paths.

Important accounting:
- Pinned source to our isolated candidate: 168 → 164 (compatibility metric only).
- Prior assumed-applied Sidon module: 168 → 161, already excluded; **none of those 7 lines are newly claimed**.
- True additional round-5 delta after that prior change: **161 → 157**, net 4.
- Total new reduction across the initial two candidate files: **6 lines**.

## Structural/source checks

`check_sources.py` regenerates `structural_check.json` from the self-contained `fixtures/` snapshots and independently verifies source SHA-256 values and Git blob SHAs against the immutable source manifest. It records every changed region and verifies all three theorem statements are byte-identical. Inspection confirms the only differences are proof bodies. Imports, definitions, type signatures, theorem names, assumptions, instance declarations, and data are unchanged.

These checks establish patch scope and source identity, **not Lean acceptance**.

## Novelty review

The baseline reviewer independently screened the prior proposal corpus, then completed the final closing screen, and reported:
- The nearest Sidon proposal is the polarization change above. Earlier `2026-10-26t/report/sections/03_coefficients.tex:68–75` consumes the unchanged pair-sum theorem; it changes coefficient-fiber calculation, not these injectivity endpoints.
- `IterationSize.iterate_depth` appears in baseline inventories, not as a proposed simplification. The nearby V03 `2026-10-26b/report.tex:269–282` changes import placement for small witness-count projections; it is not this direct expression-congruence reduction.
- The freshly added incoming A–F families concern periodicity, coprime ratio cancellation, geometric sums, square intervals, signed-borrow prefix/concatenation, and native-rank comparison. They are distinct from these wrappers.

This is a narrow novelty finding under the supplied corpus, not a claim that the general techniques (`rfl`, specializing a theorem, or arithmetic automation) are new.

## Remaining verification

When a suitable authorized Lean environment is available, compile the complete candidates atop the full assumed-applied baseline and run their ordinary checks. In particular, the `omega` handling of projected `Fin` equalities is source-supported but has not been executed here. No timing, axiom-set parity, or complete-module success is claimed.

The finite-order-rigidity and current-controller endpoint candidates are reviewed in `ADDITIONAL_CANDIDATES.md`; the regenerated structural receipt covers all four files and all six changed theorem proofs.
