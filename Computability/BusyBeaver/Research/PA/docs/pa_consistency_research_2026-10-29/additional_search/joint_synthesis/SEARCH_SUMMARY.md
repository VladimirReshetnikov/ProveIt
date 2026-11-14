# Complementary reduction research: exact scope and outcome

No accepted literal table below 208 states was found by these screens. The positive result is a provable source specialization, incorporated into the separate 3,904-primitive certificate. All local-table screens below are finite candidate searches and are not lower bounds.

## Joint synthesis of both representative rows

`synthesize_both.cpp` deletes one state q, redirects its incoming targets to a retained representative r, and synthesizes both rows of r simultaneously. It compares one original step against a positive child macro, preserving the complete represented tape and head, and projecting only q to r at the endpoint. Row assignments are generated lazily during symbolic execution, so the reported branch count counts explored partial assignments, not distinct complete machines.

The action alphabet in this particular program includes both write bits, both directions, and every retained working-state target. It excludes new direct halt targets. The tag extension below additionally includes the halt target.

| Screen | Ordered deletion/keeper pairs | Partial assignment branches | Survivors |
|---|---:|---:|---:|
| Radius 5 observed contexts, macro limit 31 | 42,849 | 427,880,592 | 0 |
| Deleting initial state 0, radius 5, limit 31 | 207 | 667,368 | 0 |
| Radius 9 observed contexts, macro limit 63 | 42,849 | 798,315,372 | 0 |
| Radius 5, every canonical spare equal to 1, limit 31 | 42,849 | 428,229,180 | 0 |

The context corpora include a 48,140-step blank startup and exact primitive executions. The radius-9 collection covers 15,252 primitive cases and 6,778,830 literal primitive steps; it collects 234,318 state/window pairs over all 208 states. Each finite window is embedded in a 64-cell tape both with zero exterior and with one deterministically pseudorandom exterior. These synthetic exterior tapes need not themselves be reachable. Thus rejection is relative to the strengthened finite local-contract screen, not proof that a quotient cannot work on the unique blank trajectory. A potential macro leaving the represented 64-cell tape is rejected.

For compilation and CLI details, the C++ files accept positional arguments `table contexts output [macro_limit [deleted_state [radius]]]`. Use `-1` for all noninitial deleted states. For the initial-state screen use `0`. The TSV context files contain `state integer_window`, with the current head bit at the specified radius.

## Head offsets and reversible tape tags

`head_offset.cpp` tests plain aliases with a head displacement of minus twice the common direction of all incoming edges to the deleted state. It reverses those incoming moves, without changing tape symbols. On the finite radius-5 corpus, all 36,639 eligible pairs failed with macro limit 63.

`synthesize_tag_both.cpp` allows a reversible origin tag: each incoming transition to deleted q flips its written bit. If all such edges have direction d, an old q configuration at head h maps to a keeper configuration with the cell h−d complemented. The mapped head is either h or h−2d; the latter also reverses the incoming move. Both keeper rows are synthesized jointly. The candidate endpoint applies the same conjugacy when the old successor is q.

Across both head placements, this tested 73,278 eligible deletion/keeper/placement combinations, explored 1,315,355,392 partial assignment branches, and found no survivor, with radius 9 and macro limit 31. The action alphabet includes halt. The same finite-corpus and synthetic-exterior limitations apply.

## Canonical spare invariant

Blank startup creates 43 spares, all equal to one. Canonical `CI` appends a spare equal to one; other source primitives preserve the spare vector. Hence every canonical source boundary on the intended run has only one-valued spares. `collect_spares1.cpp` specializes the finite corpus to this invariant: 15,252 primitive cases and 6,771,724 literal steps. The restriction removed only a modest number of local contexts and did not produce a one-row or both-row fold. It is a useful exact invariant for future searches, not by itself a state reduction.

## Source invariants

The joint nine-register category abstraction `{0,1,at least2}` found 4,513,459 reachable abstract control/vector pairs. Its independent closure checker verified 5,066,797 abstract edges. This strengthened an earlier zero/positive analysis and found additional dead ordinal 3892: its predecessor `CD 6` at 3891 always sees zero. A still finer `{0,1,2,at least3}` abstraction found 32,843,273 pairs but no additional dead source sites.

The large joint analyses were discovery tools. The final source certificate needs only two much smaller single-register abstractions: 6,430 zero/positive pairs for register 1 and 9,651 three-category pairs for register 6. The resulting removal of five source occurrences is documented and independently reviewed in `source_optimization_review.md`; the source agent's portable certificate is the authoritative reproduction artifact. The large intermediate bitsets need not be distributed.

## Attempted repair of the rejected source rotation

The self-contained `rotation_repair/` directory rebuilds and searches the rejected 207-state rotation/fold of native states 85 and 154. It bundles its original inputs, finite interpreter adapter, rejected table, and reproducible bounded failure diagnostics.

The single-row repair search performed 89,748 mutations over 108 chosen rows; the two-row heuristic extension performed 516,051 evaluations over 19 promising first patches. No candidate passed all 5,084 guarded finite contracts. Best first patches advance the first failing source ordinal from 25 to 70; best second patches advance it to 311. The search is not exhaustive over all two-row modifications. In particular, candidate second rows were selected from a bounded trace footprint.

An intermediate visit to dispatcher state 84 can contain a transient, invalid program address. The first such visit must not be mistaken for the macro endpoint. The portable failure replay therefore distinguishes first-visit diagnostics from failure to attain the exact expected whole-tape frame within the stated 100,000-step bound. It makes no unbounded or blank-halting inequivalence claim.
