# Discovery and certification of the coordinated 239-state reduction

The successful table is `machines/zfc239_old.tm` in the integration bundle. It deletes old state 169, sends the sole incoming edge `(147,0)` to 80, changes `(80,0)` to `0 L 106`, and changes `(91,1)` to `1 L 167`. The original source program and register mapping remain unchanged. All claims about the finished candidate rely on the exact block, blank-prefix, and unbounded runtime certificates described below. Finite profiles served only to find the edit.

## What made the search succeed

Single-state folds did not find a candidate in the families tested. We therefore searched a joint edit: reuse two states as one while changing a third state's transition row. The helper row was required to be behaviorally neutral in its original observed contexts, but the merged state could enter it in another context. Here old state 91 has the left pattern 011. Its new role after a state 169/read 1 entry has a distinguishing zero two cells left. The same helper transition can serve both roles through different return paths.

The discovery search first tries a candidate merged row and collects failing traces. A helper edit can repair a trace only if that row is reached before failure, so these traces narrow which helper rows need consideration. The search then checks every represented context for the complete coordinated edit. It allows positive blocks of up to 65 old and 65 new steps, including return to the reused state before synchronization. This avoids requiring literal row equality or equal step counts.

The resulting three tables differ only in the leftward target of row 80/read 0: target 12, target 106, or target 142. All three have 239 states. Target 106 has a short local proof and is the main deliverable.

## Finite searches, with their scope

An all-tape finite-window fixed point is seeded at old 95 with arbitrary tape windows. This is a sound overapproximation of old reachable local contexts. The radius-five domain has 92,397 state/window pairs. It proves useful predecessor-bit invariants but also admits contexts incompatible with well-formed runtime frames. Rejecting an edit in this overapproximation does not show that the edit fails from blank.

The successful discovery instead used the parent search's concrete runtime-plus-blank radius-five profile. It has 28,247 state/window pairs from 33,545 finite runs and 18,741,196 literal steps. Window bit positions are little-endian from head−5 through head+5. This profile is an underapproximation: an edit surviving it is only a candidate requiring independent proof. No unbounded behavior is inferred from finite coverage.

Recorded searches include:

| Search family | Result within that family |
| --- | --- |
| Same-head arbitrary-row coupled folds, all-tape windows of widths 4+4, 8+4, 6+6, positive old/new blocks up to 65 | No candidate |
| Per-incoming-edge state elimination, without a helper edit | No candidate |
| Coupled fold with an individually neutral helper, radius-five all-tape domain | No candidate in 619,962,169 helper checks |
| One-common-branch pair fold with an arbitrary helper row, radius-five all-tape domain | No candidate in 1,608,861,958 helper trials |
| Coupled fold without a helper, concrete valid-runtime profile | No candidate |
| Coupled fold with a neutral helper, concrete valid-runtime profile | Exactly 3 candidates: targets 12, 106, 142 |

The successful run considered 28,680 unordered state pairs, 54,836,160 base row options, 696,381,960 helper checks, and 1,534,411,163 context tests. Its recorded elapsed time is 127.16 seconds. The profile admits 650 individually neutral helper edits, compared with 627 for the all-tape domain. Row 91/read 1's successful helper change is also neutral in the old all-tape contexts; the stronger valid-frame information is needed for the merged role, specifically the old 169/read 1 right-neighbor guard.

These counts describe implemented search families and bounds. They establish neither minimality of 239 states nor impossibility of a different 238-state construction. The investigation of head offsets, tape complementation, source transformations, and physical register permutations is documented in the adjacent research directories.

## Reproducing discovery

The self-contained C++ programs use only the standard library. A representative invocation from `research/search/local_folds` is:

```sh
c++ -O3 -std=c++17 neutral_domains.cpp -o neutral_domains
c++ -O3 -std=c++17 helper_domains.cpp -o helper_domains
./neutral_domains ../../../inputs/zfc240_old.tm 5 5 65 65 ../head_offset/profile_r5.txt > neutral_reproduced.out
./helper_domains ../../../inputs/zfc240_old.tm 5 5 65 65 neutral_reproduced.out ../head_offset/profile_r5.txt > helper_reproduced.out
```

The arguments following the table are the left and right window radii, maximum old and new block lengths, and (for the helper search) the neutral-helper proposal file. The optional final argument replaces the all-tape domain with the supplied discovery profile. Compiler and machine speed affect elapsed time; the emitted tables and symbolic premises provide the reviewable result.

`helper_profile_r5.log` and `helper_profile_r5.out` are the original successful receipt and proposals. The neighboring `coupled_*`, `incoming_*`, `neutral_*`, `helper_*`, and `free_helper_*` sources and logs preserve the unsuccessful families as research artifacts. Temporary numerical fixtures and physical-layout screenings are supplementary experiments.

## Independent certification

The proposed table was first screened on 41,930 finite instruction fixtures. Its acceptance then used unbounded mathematics:

1. `verification/verify_guarded_fold239.py` verifies the exact table edit, all syntactic predecessor guards, four finite-footprint blocks, 476 ordinary commuting old rows, and every blank-prefix checkpoint. This is a standard-library script with explicit input/output arguments.
2. `verification/certify_guard169.py` replays all 8,386 old instruction cases with independent natural parameters and arbitrary finite spare lists. It proves the additional old 169/read 1 right-neighbor-one guard and checks that no such visit can be hidden in an accelerated unary or list traversal. The final portable driver pins the exact old table, source, unchanged checker, and helper hashes.
3. A separate complete runtime pass on the literal 239-state table closes all 8,386 cases, with 2,330,575 symbolic rules, positive durations, and all 478 rows covered. This is an additional route to the unchanged source instruction semantics.
4. Separate local-block and blank-clock checks were independently written by another agent. Their receipts are in `research/source_compression`.

The original guard instrument and its completed receipt are preserved under `history/guard169_original` in the working research checkpoint. They contain historical workspace paths. The final deliverable uses the portable driver and its freshly executed receipt; the original is provenance, not the recommended reproduction entry point.

The local proof requires old state 169/read 1 to have a one immediately to the right. The unbounded certificate records 32 symbolic visits and a minimum one-run constant 21, which implies that guard. This is a run of ones produced by the interpreter's phases; no zero-padding assumption is made. The ordinary syntactic invariant is required only for old configurations, and may fail at new intermediate states where the helper intentionally serves the second role.

## Attribution and claim boundary

The reduction builds on ProveIt's Rotation240 candidate pinned at commit `13ec39ed43148b1807f51ed6e6528e1c84659562`, its earlier source and compiler reductions, and the supplied incoming 80 universal affine/list checker. The prior ZFC-equiconsistent calculus, proof-search source, compiler framework, and state-label conventions are inherited work; the integration bundle retains the corresponding notices, licenses, and source pins. Earlier incoming 78/80 finite-window, coupled, and stuttering searches informed the exploration.

The contribution made in this investigation is the coordinated helper-row reuse yielding the concrete 239-state table, its four short local block identities, the universal right-neighbor guard audit, and the exact 144-step initialization clock difference. These are ordinary mathematical proof artifacts executable with Python assertions enabled. They are not a new proof-assistant kernel endpoint, and this search does not establish a global state minimum or a historical priority claim for every underlying idea.
