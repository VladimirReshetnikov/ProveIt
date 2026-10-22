# Round 13 runtime: factor at the first empty-left Home boundary

## Result

The owned finite replay discovers a strictly simpler contract than round 12:

- 1,422 control guards factor through 35 fixed local templates: 1,326 continue guards and 96 break guards.
- Only three control guards remain literal: `001/CB1`, `1000111/CC3`, `11011/CB1`.
- Keep all 1,900 increment guards, 2,850 decrement outcomes and one halt guard literal.
- Candidate expensive execution obligations: 35 + 3 + 1,900 + 2,850 + 1 = **4,789**, versus 4,831 in round 12 and 6,176 without templates. This is 42 fewer than round 12, and 1,387 fewer (22.46%) than the literal residual family.
- All 6,176 source-coverage instantiations still remain, with cheap exact routing/action/frame checks. These numbers are not a measured build-speed or net source-size improvement.

The main gain is not the extra 42 checks. No opaque segment constructor, new symbolic interpretation, new normalizer, global executor extension, or prefix-crossing Home theorem is needed. All 35 bodies use the existing symbolic step relation and stop at exactly `(2, true, [], R')`: state 2, head on the left, **empty explicit left fragment**. The caller appends the preserved PC prefix and existing marker. The already-proved Home theorem then finishes the operation.

This is a proposal supported by owned finite checks, not a compiled Lean or Rocq result. Neither compiler is available in this environment. `LeftFrameContract.lean.proposal` contains the exact generic statements and uncompiled implementation sketch; it must be compiled and integrated before claiming a replacement theorem.

## What is already upstream, and what is new

Pinned repository revision: `6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95`.

The existing `shared-invariants/decoder-residual` contribution already provides all-leaf semantic residual coverage. Its published validation receipt reports all 51 component modules checked with Lean 4.32.0, covering all 4,751 leaves and 6,176 outcomes; the final named theorems include `covered` and `source_halts_iff`. This is not merely the old two-outcome `000` example. Its receipt explicitly says that the complete ZFC endpoint was not rebuilt. The maintained `KEndpoint` still consumes `KSim.Covered`, the Boolean whole-site interface. This report does not claim the existing semantic coverage as new, or confuse it with a fresh endpoint build.

The current maintained `KRuntimeCore`, `KHome`, `KHomeReady`, `KSim`, and `KDecoderPrefix215` bytes are identical to the prior inspected references; `CURRENT_RUNTIME_AUDIT.json` records their hashes. Current reference files and exact URLs are in `reference/PINS.json`. The final residual theorem's current source hash agrees with its published final-recheck receipt, recorded in `UPSTREAM_STATUS.json`. No upstream build script was executed here.

New work in this round is the empty-left decomposition, weaker prefix premise, 35-template discovery, exact source-action/gap checks, and reduced generic proof surface. Round 12 needed 76 control templates for 1,421 guards and proposed a new opaque segment and crossing lemma. We first replayed that family to show every admitted run has one terminal Home, then removed the unnecessary prefix-end-one restriction. Among the 1,422 new instances, 721 prefixes end in zero. The extra admitted occurrence is `010111/CC3`.

## Native and formal labels are not interchangeable

The discovery uses the pinned native table `9683d6ed…`. The maintained Lean table renames native 301 to 102, native 302 to 120, and native halt 254 to 230. Native 302 actually occurs in the 35 local traces. Therefore an unchanged native trace must NOT be presented as a literal certificate for `tm215`.

`check_label_mapping.py` independently parses the current `KTable215.lean`, verifies equality of all 430 transition rows under that mapping, rebinds all 4,751 inherited source ports against the current formal `K215Decoder` role graph, and translates/rechecks all 444 local steps. `FORMAL_TEMPLATES.json` contains the correctly relabeled template keys, entry and exit configurations, and every intermediate state. Use that data for the Lean certificate. The same exact label binding is required for whichever Rocq table is selected. `LABEL_MAPPING.json` records hashes and the passed finite checks; these are not a kernel proof.

## Exact universal contract

Fix one of the 35 templates after the explicit table-label translation: routed state `q`, nonempty literal suffix `S`, control operation `op`, literal result suffix `E`, and local-step count `j`. Let `P` be any finite Boolean word satisfying the **existing** checker premise

`KHome.scanBound 0 (P.reverse.map Seg.bit) = some k`

for some `k`. Quantify over every natural `n`, every valid register file `vs` (including every nonempty spare tail), and blank far-left exterior. Set gap `g = n + 16`.

Entry: state `q`, left list `reverse(P ++ init(S)) ++ [true]`, right list `last(S) :: 0^g ++ [true] ++ sepsR(vs)`, with the head on that last suffix bit.

Exit: state 84, left marker `[true]`, and right list `P ++ E ++ 0^(g + |S| - |E|) ++ [true] ++ sepsR(vs)`.

The contract is `Reach1` between these **whole** configurations. It is not an observation of a window or just an agreement on register values. Both prefix orientation and every unchanged cell are preserved. Arbitrary nonblank far-left exterior is not allowed: Home uses the standard blank-left boundary.

The exact source-action premises are:
- Continue `k`: `S` contains at least `k` ones and `stripPath true k S = E`.
- Break `k`: `S` contains at least `k` zeros; stripping those zeros stays inside `S`; incrementing that stripped suffix has no overflow; its result is exactly `E`.

These premises imply the source action on `P ++ S` is `P ++ E` for every `P`; matching concrete source endpoints alone would not suffice. There is no carry into the opaque prefix and no marker overflow. All admitted templates have unchanged register file and gap delta exactly `|S|-|E|`.

The source coverage step instantiates the template gap with `n' = n + 48 - |pc|`, because the original gap is `n + (64 - |pc|)` and all source PCs have length at most 48. Thus the existing gap equals `n' + 16`. The equal-length prefix cancels from the endpoint gap delta. The finite coverage audit verifies exact routed state, operation, argument, suffix, prefix scan premise, and gap delta at each of the 1,422 occurrences. All 4,751 current source PCs avoid eight consecutive zeros.

## The small proof to add

1. Define `addLeft F (q,on,l,r) = (q,on,l ++ F,r)`.
2. Prove the algebraic lemma: if an original `sstep` succeeds and not `(on=true and l=[])`, then `sstep` commutes with `addLeft F`, preserving its output state and progress Boolean. The one rejected case is essential: original `sstep` invents a blank when it reorients an empty left list, which would read the appended frame instead.
3. Check a fixed number of guarded local steps. A short induction and existing `sstep_sound` give `Reach` between framed concrete endpoints. There is no need for local positive-progress accounting. The existing final Home supplies `Reach1`, and `Reach.trans_reach1` composes them.
4. All 35 local endpoints have empty explicit left list, so after appending `reverse(P) ++ [true]` the existing Home starts scanning `P` from counter zero. Apply existing `scanBound_sound`, append the existing guard reset, and use existing `home_word`. No new crossing proof, prefix-last-bit condition, or new unbounded scanner invariant is needed.
5. Compare only the right endpoint using existing `norm`/`flatT_norm`. Do not use `normL` on an unframed left fragment: dropping its trailing zeros would be invalid when a nonblank frame is appended later.
6. Instantiate exact source routing and the source-action frame premises, then use the already available semantic suffix/coverage interface. Retain the literal fallback family.

The 35 local bodies total 444 symbolic operations (maximum 39): 251 literal steps, 178 reorientations, 10 run scans and five box-edge steps. No new arithmetic oracle lemma is needed. The observed local bodies happen to be positive, but the proposed theorem correctly does not require that extra premise.

Rocq should prove the same append-frame lemma and bounded local-run induction in its own maintained zipper/step semantics, reusing its Home boundary theorem. Share the finite template/coverage data, not a new Lean-to-Rocq semantic bridge. There is no claimed Rocq compilation here.

## Reproduce and inspect

All replay dependencies are included under `deps/`; no sibling directory or network is needed.

1. `python check_framed_templates.py`: replay the former 76-template family, showing one terminal Home and no ordinary frame reads.
2. `python discover_left_frames.py`: rediscover the 35-template family and all assignments.
3. `python check_label_mapping.py`: check all 430 table rows, all 4,751 routed ports, and all 444 translated local steps; generate the formal-label certificate data.
4. `python test_negative_mutations.py`: verify exact occurrence coverage and reject unsafe empty-left continuation, wrong target word, wrong gap delta, wrong routed state, and an eight-zero prefix. It also admits a safe prefix ending in zero and performs 2,220 finite append-frame step smoke checks.

All replay scripts reject Python optimization, since disabling assertions would invalidate the diagnostic. The resulting JSON is deterministic. `LEFT_FRAME_DISCOVERY.json` records every local step and every source-guard assignment; `BOUNDARY_TESTS.json` records the negative/coverage checks. `fetch_references.py` is an optional owned read-only retrieval script for exact pinned text/receipts; it does not execute fetched code.

## Remaining work and stop line

Kernel-check the append-frame lemma, fixed local-run soundness, all 35 local equations, source-action framing lemmas and all exact coverage instances; adapt the semantic endpoint, then rebuild the full endpoint in each assistant. Until then, 4,789 is a concrete candidate proof-obligation count, not the number of newly compiled formal certificates. This round changes no machine, source program, theorem assumptions, or published repository files.
