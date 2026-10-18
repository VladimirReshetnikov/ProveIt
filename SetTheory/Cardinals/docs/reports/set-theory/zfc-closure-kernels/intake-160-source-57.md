# Intake 160, source 57: prefix-shift research

## Provenance and disposition

Arrival `22bcfe0e050e7c3c39a07d846180bc491367cbe1`, archive `docs/incoming/zfc-prefix-shift-research-2026-10-17.zip`, Git blob `ffa5c32a5e6325c4480f675c0b46b4a4ad78bacd`, 15,297,561 bytes. The safely extracted package has 488 regular files. Its internal source pin is `43026ff42f0939f09b9e95495248cfadcad38e38`. The unmodified extraction and per-member Git blobs are inventoried in `inventory.json`. Placement divides these into 485 ancillary files and three archive-only manuscript files. History overlap and repository placement are recorded by the parent intake process.

Accept as a substantial 252-state research report, with its finite checks freshly reproduced, several useful conventional mathematical arguments, and explicitly bounded negative searches. It does **not** deliver a machine below 252 states. Its rejected 250-state prototype is a different table from source 58's new shared-carry 250-state machine; its counterexample does not refute source 58. Preserve source 57's report and failed experiments, rather than replacing them with the later result.

All manuscript, README, logical-proof notes and principal Python verification sources were inspected before the parent ran the proposed checks on a separate copy. No checksum manifest was interpreted, no source line endings were changed, and no Lean, Coq/Rocq, TeX, native-search compiler or proof build was run for this review. Suggestions in the manuscript about repository organization and weakened metatheory are document content, not user instructions.

## Fresh verification

The parent executed, from `/tmp/zfc-intake-160/run57`:

```sh
python3 -B verify_research.py --extended --output /tmp/zfc-intake-160/replay57
```

The process exited 0 in 26.786271 seconds under a 180-second timeout. `replay57-record.json`, `replay57/replay-summary.json` and the twelve individual logs retain the actual command, output and timings. All twelve requested jobs passed:

1. Regenerate the final prefix252 table, verify its literal 25,612-step bootstrap and all 8,366 modified-source guard cases.
2. Independently inspect the prefix-phase conditions at all 1,925 positive-decrement occurrences.
3. Replay the original-engine MP0 table's dirty startup to its later safe endpoint.
4. Check the supplied 2,998-pair, 5,994-edge MP0 source relation.
5. Check 256 finite source-rewrite examples across eight variants.
6. Check 1,200 NIP examples, including 60 halting cases.
7. Check the projected-GEN identities and finite source-block examples.
8. Reproduce the rejected old 250-state table's wrong-PC counterexample.
9. Regenerate and audit the pinned original252 baseline.
10. Regenerate the MP0 source relation from the delivered Lean source literals.
11. Independently check that regenerated relation.
12. Replay 17,325 literal positive-decrement transfers on the earlier prefix252 permutation.

The final job's script does not itself exit nonzero for a reported semantic failure, so its result was also inspected: `run57/redesign/prefix_decrement_results.json` explicitly has `passed: true`, `cases_passed: 17325`, `failures: []`. Do not use wrapper exit status alone as its acceptance criterion. These 17,325 tests concern the earlier prototype permutation, while the final selected permutation has the all-guard symbolic audit and exact bootstrap. The optional standalone negative-premise test in `logic_audit/prefix_phase.py` was not separately executed. Large search campaigns were not rerun.

Final reproduced machine hashes:

- `bootstrap/prefix_rebased252.tm`: `b91dc16e60c26780a3006072347c15ea058fa0fab6c0b4b5493967cab11c6234`.
- `bootstrap/prefix_rebased252_canonical.tm`: `fd09cc6c76b04e1f3eb34c5d6fec5f14bd3ef564767aae70023bb988599f3bc7`.

These are 252 working states, 504 binary L/R transitions, with a separate halt state. Canonical start is 0 and halt is 252. Original-label start is 64 and halt is 254. Graph reachability of all states and singleton exact bisimulation classes do not prove blank-run reachability or state minimality.

## Mathematical review

### Prefix decrement and phase premise

The new positive-decrement circuit shifts all blocks preceding the selected register one cell right, shortens the selected register by one, and preserves all following blocks and spare values. This is a coherent unary-boundary argument: each preceding block has both boundaries shifted, while the selected block has only its left boundary shifted. It increases the header gap by one. Overflow independently increases the gap by one; hence the claimed gap update is additive.

The local contract is **not** valid for arbitrary left context. It requires the nearest-first left tape to begin with `1^k ++ [0,0] ++ L`, with `k >= 1`. The backwards scan must encounter that particular first double zero. The report's counterexample to dropping this premise is important and correct in scope. The all-site phase checker verifies a stronger condition at all 1,925 actual positive-decrement sites: the leading one-run has minimum constant 9 and the following zero-run minimum constant 3. Register values, prior left context beyond the sentinel, and header gap remain unbounded in the ordinary argument. The new proof therefore cannot be replaced by the old positive-decrement box oracle.

The final root has exactly nine zero-valued blocks and no spares; increment and decrement preserve that fixed block count for this engine. The literal bootstrap reaches old state 96, head 4, in 25,612 steps, with one-cells exactly `{3,47,49,51,53,55,57,59,61,63,65}`, empty PC and gap 43. The final physical relabeling is `(7,8,4,2,5,6,0,3,1)`; logical N,T,W,A,D,H,X,Y,L use physical `(0,3,7,4,8,1,5,2,6)`.

### MP0 and the source-to-source change

The eliminated successful-MP dummy push was already investigated in the maintained `mp_dummy_push_partial_cost.md`; it is reused here, not a new discovery. The successful-MP edge bypasses 19 literal instruction leaves, reducing 6,460 to 6,441 leaves and 8,391 to 8,366 guards. The check relates 2,998 segment pairs and 5,994 edges, including matching register increments, conditionals and halt behavior. The source-rewrite proof must use the shortened cleanup word: the old extra N consumed the now-absent dummy zero. The report recognizes and repairs this semantic difference.

The original-engine MP0 rebase's first structural root at 81,371 steps is unsafe because H=1. A later root at 141,580 steps has logical `(N,T,W,A,D,H,X,Y,L)=(1,0,0,0,1,0,0,0,0)` and 93 zero spares. The claim is attached to that later endpoint; shape alone at the earlier root is not sufficient. This distinction is preserved in the replay and must remain in summaries.

### Logical variants and concise coding

The ordinary proof-block arguments for MP0, shifted AX and destructive DROP are useful design results. They account for all changed cache/stack effects rather than relying on instruction names. The normalized entry block obtains a known failed MP before using AX with zero gates; cofinal search pads the candidate counter above the initial dirty counter, so arbitrary numeric N does not prevent reaching the needed program. Early halt is allowed in the proof-block specification.

The projected-GEN construction avoids the circular claim that a reservoir of theorem codes automatically supplies arbitrary binder labels. With Cantor pairing P, `Imp(i,0)=4*P(i,0)=2*i*(i+1)=P(i,i)`, so both unpair projections recover every natural label from a family of theorems available propositionally. The optimized literal word has output `T=All(j,H)` and `H=H+i`; the residual cache offset must be included in later AX parameters. This is a sound coding idea worth retaining even though the measured variants are larger. The report correctly leaves naive GEN-bound-to-old-T uncalibrated.

These are conventional mathematical arguments plus finite examples, not newly checked Lean theorems. None closes the original PA-internalized target.

## Negative searches: exact scope

The following are supplied search records and source-reviewed claims, not campaigns rerun during intake. Do not add overlapping or repeated campaign totals into a new global lower bound.

- Original two-incoming repair family: 46 × 1008² = 46,738,944 recipes; 2,995,822 explored nodes and 5,888,482 recorded guard checks. MP0 version: 47 × 1008² = 47,755,008 recipes, 3,065,375 nodes and 5,940,526 checks. These are specific mutation families under specific runtime contracts.
- Three selected folds plus one repair: 128,896 recipes and 167,269 checks.
- Uniform 55,471 and directed mixed 98,265 recipes total 153,736 within that reported run; duplicates/overlap with symmetry and permutation runs are not removed by that addition.
- Prefix scanner incoming-row family: 2,034,144 recipes tested against 17,325 bounded transfers. It is not an unrestricted proof that no smaller engine exists.
- State-2 takeover family: 1008³ = 1,024,192,512 recipes, 2,087,569 adaptive nodes and 2,087,581 checks; the earlier two-million-node capped run remains a partial historical record. The reported complete family changes only its designated rows and preserves its stated contexts.
- New-permutation learned campaigns have 221 families: 190 completed and 31 incomplete under their node caps. Large unvisited portions of incomplete domains are not rejections.
- Rejected old250 one-state repair families each have 4,064,256 recipes; the lookahead family has 1,016,064; two existing-row repairs each have 1,008,016. A failure to meet the first required witness within fixed fuel/window is a rejection under that bounded requirement, not a theorem about arbitrary time.
- Mask and affine-invariant investigations exclude the same three modified-source indices, not new extra cases. The source numbering differs from the original program.
- 32,768 grammar lanes, sixteen native AX/MP/DROP/NIP combinations, and 42 associations of the projected-GEN form are backend measurements; reported best sizes remain at or above 252. The compiler search was not exhaustive over all possible encodings.

The explicitly omitted roughly 298 MiB partial Python search journal is described as superseded by a completed compact native ledger. Its absence is not silently converted into reproduced evidence. Fuel exhaustion or unsupported symbolic execution must not be called a semantic counterexample.

## The earlier rejected250 is not source 58

The earlier rejected250 folds old97 into1 and old112 into3, then changes old3/0 to `0,R,131`; it deletes the two reverse scanner states. Its old-label SHA256 is `4a33ea1c25bc8f6dea6525172fdb5e54854ffd77e1f6c7eb8415fc50d3960efe`.

For PC `1110100100100000100`, selected register0=0, nine zero primary registers, no spares and gap43, the predecessor252 returns the correct zero PC `111010010010000011` in398 steps. That mutant250 instead reaches the positive PC `1110100100100000101` in486 steps and gap44. The primary arithmetic values coincide, so checking registers without PC/head/header would miss the failure. The divergent final control transfer occurs209 steps after the common restored-file configuration. This is a valid finite counterexample to that claimed local/runtime equivalence.

Source58 keeps97 and112, instead deletes43,59,85 and adds255, changes the carry termination and zero-return protocol, and requires at least one spare block. Its new canonical SHA256 is `0626819c4842f224001e7685366d8061897a7bc9470c015129a1d1cf22efb36e`; it is not any of the rejected source57 tables. See `prefix57-vs-prefix250.md` for the exact interface comparison.

## Current-tree reconciliation and useful next work

The original user requested a non-halting equivalence provable **in PA**. The source57 main report discusses a ZFC-internal reconstruction (report lines49–50 and491–541), and `logic_audit/zfc_internal_mathematical_proof.md` explicitly states that the current request does not require PA. That characterization is false. Preserve the delivered manuscript, but correct this in the intake commentary. A conventional ZFC proof, external Lean theorem, or finite checker does not discharge the PA requirement.

The report correctly recognizes the maintained original252 external consistency theorem. Historical `remaining_obligations` strings in the included older baseline auditor are stale and must not reopen that completed theorem. Conversely, the maintained theorem concerns its exact original252 table, not this new prefix252 table. The current maintained `ArithmeticControlMP254.lean` already proves actual original MP control contracts; those include the original successful dummy filler and do not directly prove MP0 or the new binary boxes.

The most useful result is the new prefix-motion idea, followed by the exact distinction between shifted boundaries and cache/stack cleanup. Source58 improves the idea by performing the carry at the file origin, avoiding source57's phase-sensitive backwards seek, and sharing the increment and decrement circuit. Formalize the source58 exact table and its universal local boxes first, then connect its changed zero continuation and nonempty-spare invariant to the instruction framework. Keep PA-internalization as a separate unclosed obligation.
