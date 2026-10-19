# Batch 168: three 242-state folds and a 241-state predecessor-bit reduction

Sources 72 and 73 arrived in `8c41b1fb7d7bb8cd0612e37848181fe4a2f5d569`. They continue the exact Combined243 machine and its unchanged QT logical source. Source 72 presents three alternative 242-state reductions. Source 73 composes the recommended one with a further fold to 241 working states. These are additions to the existing report under the reconciliation-note workflow, leaving the seeded article, its PDF and all delivered bytes unchanged.

Placement `696c150e84` preserves **151 ancillary files**, with **12 manuscript, PDF and delivery-README members archive-only**, for **163 recoverable outer members**. Source 72 accounts for 118 members, of which 110 are placed; Source 73 has 45 members, of which 41 are placed. Its nested 242 ZIP exactly equals the separate Source 72 archive and is retained as one dependency artifact, not another source. Twenty-three older Git blobs account for 31 inherited member occurrences; neither new main manuscript has an earlier exact-blob hit. The host now has 73 sources and the collection remains 290 reports. Six later arrivals are outside this batch, leaving 26 other ZIPs queued at placement.

The [placement map](data/intake168-placement.json) records every outer member and exact destination. The source dossiers for [72](intake-168-source-72.md) and [73](intake-168-source-73.md) distinguish new proofs from inherited material. [Recovery and reproduction](intake-168-reproduction.md) restores original nested paths before any replay. Delivered scripts were flattened for preservation, so their unchanged relative paths must not be run directly from the host's `code/` directory.

## Source 72: control folding with unchanged source semantics

The base is Combined243 at ProveIt `e58338db7545909907e07a7603e8eb88625c527a`, inherited-table hash `4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300`. All three alternatives have 242 working states, 484 binary rows and a separate halt. Their inherited start, dispatcher and halt are 95, 96 and 254. Canonical start is 0 and halt is 242; dispatcher is 86 for A and B, and 87 for C. Every action writes one binary symbol and moves one cell left or right; initialization is counted.

Candidate A deletes old state 27. It changes `15/0` from `0R21` to `0L32` and redirects `18/0`, `47/0` and `65/0` from 27 to 15. The old-side invariant requires left 0 at controls 15, 18, 47 and 65, and current 0 at 27. The complete incoming inventory proves this invariant from inherited start 95 for every head and tape. At `15/0`, the new three-step path through 32 and 45 reaches 21 with the same head and entire tape as the old single step. The invariant forces read 0 at mapped old 27. All other rows match in one step. Both clocks advance positively, proving halting equivalence without a consistency or source-reachability premise.

Candidate B deletes old 50, changes `27/1` to `0L20` and redirects its four callers to 27. Additional old guards ensure left 1 or current 1 at 50. Candidate C deletes old 171, changes `27/1` to `1R202` and redirects `150/0` to 27, using its left-0 entry guard. Their ordinary proofs use separate checkpoint relations and short positive blocks. The three reductions are alternatives; their savings cannot be added without another compatibility proof.

The simplified principal A proof and the separate three-fold proofs use different relations. The principal mapped proof records 7,696 invariant implications and 7,696 endpoint blocks. The common three-fold formulation records 7,640 invariant implications and 512, 768 and 256 exceptional footprint assignments. These are distinct decompositions, not inconsistent totals. Explicit footprint checks establish that block identities leave every exterior cell untouched. The ordinary theorem covers arbitrary two-way function tapes from inherited 95, not merely selected frames or a finite blank trace.

## Source 73: a predecessor bit distinguishes two roles

The 241 construction uses the exact primary 242 inherited table `c8ef2f44d25fee6813164cc59ec05061799397da8cf7f0ea7baab63d32d76e02`. It deletes old 39, changes `17/0` to `0L106` and `17/1` to `1L37`, and redirects `46/0` and `50/0` from 39 to 17. Both retained rows are synthesized; neither merely selects its corresponding old row.

The sole old 17 caller is `12/1`, which writes 1 and moves right. Old 39 has only `46/0` and `50/0` as callers, both writing 0 and moving right. Thus the old invariant is left 1 at 17 and left 0 at 39. This already-present tape bit chooses the role of new 17 without adding a cell or control state.

Four exceptional paths match one old step. Old `17/0` uses five new steps through 106, 92, 107 and 125 to 25. Old `17/1` uses three through 37 and 55 to 20. Old `39/0` uses three through 106 and 93 to 57. Old `39/1` uses three through 37 and 25 to 69. Other rows match in one step. The endpoint head and entire tape agree; the invariant is required at old checkpoints, not every intermediate new state. Positive clocks prove both halting directions. Each of the two independent finite-local formulations records 7,712 invariant implications and 7,712 endpoint comparisons.

Directly relative to Combined243, the patch deletes 27 and 39 and changes eight distinct retained rows; the semantic proof still composes through the exact 242 intermediate. Relative to routed245, the deleted labels are 26, 27, 39 and 122. Canonical241 has working controls 0–240, start 0, dispatcher 85 and separate halt 241. Its canonical hash is `c5278eaf0561cd12d676b3e9c030ffe46d5bc7ec94d29d705dee31a72ea95158`; inherited hash is `1fa8526c3c971d5a48868599eaed890f614c5a79256e51622d3e32a64229f3a3`.

Source 73 credits supplied neutral-edit and sequential-background research for discovery guidance. The final table removes all incidental background edits and is proved directly against the primary 242 baseline. Earlier negative searches restricted to copied overlays or one synthesized retained row did not cover this two-row mechanism. This is a scope distinction, not a claim of global minimality or historical priority.

## Runtime, initialization and replay status

All four new tables retain the exact 6,459-leaf QT source, hash `3ee984818f0bdfd2c4daae72aeb14340572e34d73f5cdb5616b6d29d78fcd7f4`, with 8,390 guarded cases. The delivered runtime contract quantifies independent arbitrary natural registers, extra gap and a nonempty finite spare list. Its 4,000-rule construction cap does not bound register values, spare length or actual runtime. The ordinary local simulation, unbounded runtime proof and 133 concrete dense/sparse instances per candidate have separate roles.

| Table | Delivered blank steps | Delivered expanded rules | Guarded cases | Rows |
| --- | ---: | ---: | ---: | ---: |
| 242 A | 407,979 | 2,314,880 | 8,390 | 484 |
| 242 B | 408,291 | 2,318,402 | 8,390 | 484 |
| 242 C | 407,985 | 2,314,880 | 8,390 | 484 |
| 241 primary | 408,419 | 2,319,442 | 8,390 | 482 |

Each delivered boot result identifies the complete tape: 351 one-cells and zero elsewhere, old dispatcher 96, head −5, marker −6, header 176, logical seed `(3,0,0,0,3,0,0,0,0)` and 167 value-one spares. For 241, old-prefix visit counts 15, 3, 132 and 55 yield 440 extra transitions, agreeing with the separate whole blank simulation. The all-tape theorem does not depend on that trace.

Root's [fresh substantive replay](data/intake168-fresh-replay.json) passed all 19 jobs: 14 local/boot/concrete jobs and five complete universal jobs for 242 A, B and C, inherited 243 and primary 241. Every universal job checks 8,390 cases, with its complete emitted case array equal to the delivered array. The terminal status is `ROOT_SUBSTANTIVE_LEAF_REPLAY_PASS`. The exact executed runner, raw per-job records and stdout/stderr are preserved in [replay history](data/intake168-replay-history.json). Delivery manifest wrappers were not invoked; this replay includes no Lean, PA, TeX or discovery-search execution.

## Current formal scope and attribution

The manuscripts pin an older snapshot. Since then, the concrete rotated-source bridge and `CalibratedRotation244` have passed; the five source-interface/calibration units have 34 probes and 40 typed callers. Rotation244 runtime, exact source tree and bootstrap frame are also checked. Complete decoder-site coverage and final binary composition remain pending; the earlier 64-unit coverage checkpoint is historical and the family is continuing. The new local folds preserve this work rather than discharging the missing coverage premise.

`PositiveBlockBisimulation` and the exact `TableCombined243` provider support two small new Core simulations, 243↔242 and 242↔241. Those relations can eventually compose with the existing Rotation244↔Combined243 theorem and a completed Rotation244 endpoint. New source drafts are not passed proofs. Core's finite-support tape domain suffices for blank input; the reports' ordinary arbitrary-function-tape theorem has broader scope. Neither ordinary local equivalence nor an external kernel theorem supplies internal PA calibration.

No unconditional nonhalting, absolute consistency, global minimum or two-sided independence from bare consistency is asserted. Credits remain with Mira-Cult for the original calculus/program, Jeff Ketchersid for verification, Andrew James Wade for compilation, ProveIt for previous source/routing/initialization work, and the compensated/QT contributions for the inherited machine. The new contributions are the three local folds and the subsequent predecessor-bit reduction and certificates. No extra individual author is inferred from a delivery prepared for Vladimir Reshetnikov. All inherited notices remain unchanged.
