# Incoming archive comparison

## Scope and provenance

The eleven ZIP archives were downloaded from `VladimirReshetnikov/ProveIt` at pinned commit `239b7a406e24405d464edc526e09d402abce5bc5`. Each archive's Git blob SHA-1 was checked against both its downloaded bytes and the pinned GitHub directory listing. `incoming_comparison_manifest.json` records the exact paths, sizes, Git blob identities, SHA-256 hashes, ZIP member counts, descriptions, designated outputs, and proof status. The repository's root `LICENSE`, fetched at the same commit and copied as `ProveIt_LICENSE`, is the MIT No Attribution License (MIT-0), copyright 2026 ProveIt Contributors. No separate LICENSE/COPYING file was found inside the extracted archives.

Five main construction packets provide nine designated output tables in two rooted graph classes, A and B. The later `pa208_research` archive also supplies eighteen proved 208-state helper variants. These eighteen are pairwise nonisomorphic and distinct from A and B; all eighteen supplied local equivalence checks were freshly replayed successfully. Thus it would be incorrect to describe the entire incoming collection as only two distinct 208-state machines.

The directly visible literal-table census has 545 `.tm` files. Of these, 316 contain 208 working states and represent 142 distinct rooted action-preserving graphs. This larger inventory includes rejected and exploratory machines; filename or state count does not establish an accepted construction. Nested provenance ZIPs were not all recursively expanded, so these numbers describe direct extraction of the eleven top-level archives.

## Archive-by-archive findings

| Archive | Classification | Contribution and status |
|---|---|---|
| `Below_U208_Research_2026-10-29.zip` | Research retaining bases A/B | No accepted smaller machine. Boundary projection, head-offset quotient lemma, source pruning, and explicitly bounded negative searches. |
| `ConPA_below208_research_2026-10-29.zip` | Research retaining bases A/B | No accepted smaller machine. Two-element source/output-role-collapse model; 279,936 parameter permutations; local merge and conditional-source searches. |
| `U208_ConPA_2026-10-29.zip` | Construction A | One designated 208-state output. Applies the same native 172/211 conditional-history fold as the other main submissions, retaining 172 and using helper 217 in Joint labels. |
| `U208_ConPA_Conditional_Context_2026-10-29.zip` | Constructions A/B | Primary A, alternative B. Deletes 172 and keeps 211; the zero branch tests predecessor context through helper 217 for A or 214 for B. |
| `U208_ConPA_Entry_Context_2026-10-29.zip` | Constructions A/B | Primary and alternative dense tables are byte-identical to the Conditional Context outputs. Reorganizes the complete local proof and calibration audit. |
| `U208_ConPA_History_2026-10-29.zip` | Constructions A/B | Keeps 172 in Plain labels and uses helper 214; yields the same two rooted machines, with a finite-history proof. |
| `pa208_research_2026-10-29.zip` | Research plus eighteen proved 208-state helper variants | Retains both base classes and adds eighteen distinct graphs through one-state deletion plus one-helper addition. Complete local checks prove all-initial-tape equivalence. Other source rotations, direct negation, fixed-role emitters, and shortened MP padding do not yield an accepted sub-208 table. |
| `pa_consistency_research_2026-10-29.zip` | Source optimization retaining bases A/B | Specializes 3,909 primitive sites to 3,904 while preserving halting from the canonical seed. No physical state-count reduction. Includes a rejected 207-state rotation and further context research. |
| `pa_unary_power_cover.zip` | Theory and abstract numerical algorithm | Unary Theory U with one binary relation and one covering schema; mathematical interpretation and PA consistency calibration arguments. No compiled literal TM. Its dyadic positive theorem stream is distinct from the native Cantor-coded 208-state source. |
| `u208_comparison_research_2026-10-29.zip` | Comparative research | Identifies two graph classes among the nine main outputs. Includes a rejected 207-state canonical-return counterexample, schema comparisons, and bounded searches. No accepted smaller machine. |
| `u208_research_2026-10-29.zip` | Constructions B/A | Primary B and Plain alternative A, using the same 172/211 fold. Includes complete symbolic runtime receipts for both final tables, with 5,084 primitive contracts each. |

## The common 209-to-208 reduction

The main 208-state submissions share one reduction, not independent savings that can be added. In the relevant 209-state native layout, entry to state 172 has predecessor cells `10`; entry to state 211 while scanning zero has predecessor bit one. Their context-sensitive fold uses a shared helper to distinguish those histories. Four exceptional positive blocks have lengths 7, 1, 3, and 1, while the other 414 rows commute through the state projection. The result preserves halting for every initial tape. The exact elapsed-step identity is

`T_208 = T_209 + 6 N_(172,0) + 2 N_(211,0) <= 7 T_209`.

The concrete labels and dense numbering differ among packets, but canonical breadth-first renaming from the start state shows the designated outputs fall into classes A/B. This exact fold does not transfer to current PA196: both native roles 172 and 211 disappear in its replacement AX construction.

## Transfer and implementation checks against PA196

Current PA196 uses a 68-node binary AX macro DAG for a 201-token word. Six independent opposite-predecessor folds compress its 202-state unfolded decoder to 196 states. `compile_ax.py` reconstructs that decoder, verifies each complete two-cell positive block, reapplies all six folds, and obtains exact equality with every original native transition. This is stronger than merely matching the state count.

The same-count helper idea was tested on PA196 in a restricted family: two disjoint opposite-tag state pairs merged using one fresh shared helper. A total of 8,061,300 candidates were screened through explicit local tapes with a 35-step limit; no candidate survived. This is a bounded negative result, not a state-count lower bound.

Actual-cost DAG rotation searches also found no machine below 196. The initial randomized run priced 46,294 layouts. A breadth-first catalog priced 13,139 layouts and retained 275 tables with 196 states, 1,247 with 197, and 3,153 with 198. A second search required full-source paths to have at most six consecutive zero bits; it priced 18,922 layouts and retained 129, 839, and 2,284 tables at those respective counts. These are candidate layouts whose local folds are checked; source grammar equivalence alone does not certify the complete physical execution. In particular, the origin scanner and blank-tape startup must still be checked.

## Corrected source invariants

`source_invariants.py` now starts at the actual source seed: ordinal 25, with logical register vector `[2,0,0,0,0,0,0,0,0]`. This is grounded in `PA196/Arithmetic/Machine/EndpointInternalStartupFrame.lean`. The logical-to-physical permutation is `[6,2,0,4,3,7,8,5,1]`; therefore candidate register N is logical 0 and physical 6. An earlier exploratory receipt confused these indices; it has been replaced and must not be cited.

The corrected, independently checked inductive closure in the categories zero, one, and at least two yields two forced zero decrements: site 3773/register 1, in the already investigated MP zero-push block, and site 7/register 6 in the front comparison. Replacing the subtree at path `00011` by `breakTo 1` removes sites 7–8, and the remaining source CFG agrees exactly under ordinal projection. However, the number of distinct internal source DAG nodes grows from 159 to 161 because shared comparison subtrees split. This is a source simplification, not a physical state reduction. `site7_specialization.json` records the exact tree and checks.

## Why source-level changes need a physical audit

The proposed clear-T Shift change, combined with an outer tree rotation, preserves the intended abstract CFG outside the modified loop and keeps the longest zero run at six. Nevertheless, its first literal implementation halts on the blank tape after 43,563 steps. The exact finite counterexample is retained in `clearT_rotation_blank_counterexample.json`. Subsequent work isolated a mismatched continue control path. The rejected table must not be presented as a consistency machine.

Similarly, changing eleven primitive leaf entries can implement a physical-register permutation on canonical frames, but the same entries participate in blank startup. Merely failing to reach the old exact seed does not reject a permutation: a different gap and spare-tail length may work. The companion history investigation found such a canonical seed for the 0/1 swap. For the 2/7 swap, a bounded scan of one million steps found no canonical source-25 seed with N at least two, all other logical registers zero, and a one-valued spare tail. This is only a bounded startup screen.

## Recommended representative artifacts

`accepted208_representatives/` contains twenty small literal tables: bases A and B, plus the eighteen accepted helper variants. `provenance.json` maps every copied table to its archive/member, pinned commit, raw SHA-256, and canonical graph hash. `helper18_recheck.json` records the freshly replayed exact local checks. The root ProveIt license is preserved alongside them. These twenty machines all have 208 working states; none is a new sub-196 construction.
