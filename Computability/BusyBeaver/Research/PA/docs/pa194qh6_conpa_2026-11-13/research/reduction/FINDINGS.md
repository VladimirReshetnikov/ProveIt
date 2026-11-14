# Reduction experiments on QH6 and the primary PA194

These experiments establish no machine below 194 states. Finite search failures are not lower bounds.

## QH6 row-choice quotients

Input: `machine/machine.native.tm` in the release, SHA-256 `6ee047dc2d01faf550e83f40c85b5ac50a74c1699f15211e329047e51d979a4b`.

The inherited symbolic executor verifies 4,876 outcomes (1,601,532 abstract steps, maximum 499). We then repeated the PA194HS whole-source merge procedure on this new input. It considers every unordered pair of 171 controls outside the arithmetic-box set with each survivor row chosen from either old row (58,140 candidates), plus all 171*23 identifications into an unchanged protected box control (3,933). Every changed incoming target is redirected. Contracts unaffected by the changed states need no replay; affected contracts are tried, with a 1,024-operation bound. Result: **0 of 62,073 survivors**, elapsed 32.54 s on this run. The receipt is `recorded/search_qh6.json`; this is a bounded failure, not a claim that all possible quotient simulations have been excluded.

## Arbitrary first actions and contractions

The source executor and exact 58,088-transition initialization produced 16,937 radius-five windows at the 171 non-box controls. The PA194NS `action_merge_future.cpp` and `eliminate.cpp` programs, with a 150-step detour bound, found no merge or single-state deletion. These searches permit the first action to choose either write symbol, either direction, and any retained target. They require a bounded join to an original future local configuration and impose their published changed-row avoidance conditions. Receipt: `recorded/local_search_qh6.json`.

A second run used the independent literal executor instead of abstract register-box oracles. The derivation visits all 4,876 source outcomes, derives the four arbitrary-list traversal identities, includes intermediate positions of accelerated unary scans, and adds the exact startup. It produced 30,761 discovery windows for all 194 controls, including the 23 arithmetic controls. Unknown list contexts and affine correlations are deliberately relaxed. No merge or deletion was found. Receipt: `recorded/box_contexts_qh6.json`.

The local merger was additionally run with the initial control 74 permitted as a merge participant. This also returned no candidate. Its empty result is `recorded/QH6-all-action_merge_start.jsonl`. Native 74 is not startup-only: its incoming row `(64,0) -> 0 R 74` is part of the recurrent register increment engine. Both its rows participate in the ordinary register routines.

## Why shortening the scanner is a source-encoding problem

The native seven-zero scanner uses states 2,3,5,9,15,23,34. The source interpreter's initial all-zero address has length six. The scanner and this address interact during intermediate marked-register configurations: the all-zero dispatch prefix is reused by a generic arithmetic excursion. Changing only the scanner therefore misaligns the interpreter.

We tried a source-preserving reassociation of the outer program:

`((node7,node20),(node170,node23))`

becomes

`(node7,((node20,node170),node23))`.

The complete resolved 3,673-site source graph is exactly unchanged, as verified by direct comparison of every source instruction and successor. The first all-zero address shortens from six to five bits. At the literal table level the former source controls 53,84,310 can be reused for these new internal nodes, and deleting control34 yields a 193-control *experiment*. It does not validate: **52** of the old 4,780 symbolic outcomes fail to close within 1,024 abstract operations.

There are two concrete obstructions. First, `node20` changes from a right child to a left child. Its existing native control69 is contextually shared with `node72`, so its old preceding-bit discriminator is no longer correct. Second, long six-zero paths remain inside AX; shortening the outer address alone does not remove those internal alignments. Splitting control69 restores distinct reader contexts but costs back the saved state. No compatible additional fold was found by the existing three-transition contextual-fold template.

A more local reassociation of `node6` lowers the first all-zero address too, but changes four copies of the comparator's forward break: the original target is cleanup, whereas the rotated break targets halt. It was rejected semantically before any claimed construction.

The portable `source_rotation.py` repeats the source-preserving outer experiment. It does not define an accepted machine. The simpler node6 rotation was rejected as a semantic idea and is not part of the exhaustive search counts.
