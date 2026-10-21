# Certificate refinements: audited results and a smaller lookup proof interface

Reviewed on 2026-10-21. This is source inspection, receipt verification, ordinary mathematical reasoning, and newly owned Python corroboration. **No Lean, Coq, or Rocq compiler was available or run. No received executable was run.** Earlier sealed research directories were not changed.

## Main conclusions

1. The packet supplies a credible new checked **Rocq/Coq balanced source-checker refinement**, not a new Lean production endpoint. The exact source theorem has successful recorded Coq 8.18 compilation and closed assumptions. The separately recorded recursive audit covers the generic checker, not the concrete source theorem.
2. Its shared **two-marker finite checker** is genuinely more reusable than three handwritten instance proofs. All three native-table instances have source-bound compilation receipts and a recorded recursive audit. A dense/zipper bridge and full endpoint replay remain missing.
3. The **concrete Cantor credit proof** really discharges the earlier abstract codec and literal-schedule hypotheses. It does not prove that the physical ZC215 table implements that schedule.
4. A further simplification is available: **abstract lookup soundness by checked membership, then use a positive trie with a checkpoint at every node**. This removes ordinal-size witnesses and their proof machinery from the semantic checker. Exact finite reindexing reduces lookup node visits from 54,514 to 45,591, with maximum 12 instead of 13. This new design is not compiled.
5. The 21-table state search reports no successful fold in its restricted family. Its 133,827,040 action tests are not distinct complete machines, and its negative result supplies no lower bound.

## Provenance and receipt audit

Archive: `docs/incoming/K215_Certificate_Refinements_2026-10-21.zip` at commit `aa66d0a33f1f8237a348899eb8095b045a502832`.

- Git blob: `7e969e67dfbd88a8b6aca044ce1541115de2f897`, recomputed from downloaded bytes.
- SHA-256: `ae5edcd5fa0496d3fa13178a27b38108ad33a2301d970ebb5f22b968b1f6db0e`.
- 540,989 compressed bytes; 106 safe regular files; 1,073,294 uncompressed bytes.
- Every one of the 105 top-manifest records matches its actual bytes and hash. The manifest is the sole intentionally excluded file.
- All 14 balanced compilation source/log pairs match their receipts. The `RMEquiv.v` compiled hash is correctly reconstructed from the retained Rocq 9.1 source by inserting the documented Coq 8.18 compatibility import. This does not change its executable definitions.
- The balanced generic `coqchk` invocation has exit 0 and a matching empty silent log. The receipt explicitly excludes `Source215Balanced`.
- Marker source hashes match, command exits are 0, and the logs contain exactly six closed-assumption reports. The concrete `MarkerInstances` recursive check is recorded.
- Credit source hash matches, both commands have exit 0, and its log contains exactly nine closed-assumption reports. The `CantorCredit` recursive check is recorded.
- No `Admitted`, `admit`, custom `Axiom`, or `Parameter` token occurs outside comments in the packaged `.v` sources. This static scan is not a replacement for an assumption audit.
- Compiled objects are intentionally not packaged, so their recorded hashes cannot be independently recomputed here. The evidence establishes internally consistent supplied receipts, not an independently rerun proof.

The packet was originally prepared against `53269bc...`. I separately refetched the current `Prog215.v`, `DagPerm.v`, and primary `k215.native.tm` at the archive-intake commit `aa66d0a...`; all three are byte-identical to the packaged inputs. Their Git blobs and exact URLs are in `CURRENT_SOURCE_BINDINGS.json`. Thus no drift was found in these principal bindings.

Canonical archive link: <https://github.com/VladimirReshetnikov/ProveIt/blob/aa66d0a33f1f8237a348899eb8095b045a502832/docs/incoming/K215_Certificate_Refinements_2026-10-21.zip>.

## 1. Balanced source checker: exact theorem and remaining cost

The formal chain in `balanced_lookup/BalancedBisim.v` is sound as written:

- A tree's stored cut must equal its left subtree's actual size at every node (`valid`). No balance hypothesis is needed for semantic correctness.
- Under `valid`, `lookup_flatten` identifies its binary-indexed lookup with `nth_error` on the flattened certificate, including out-of-range inputs.
- The branch, entry, and whole-checker refinement lemmas preserve the inherited `Bisim230.check` exactly.
- `checkTree_halts_iff` uses both `validb = true` and `checkTree = true`, then invokes the ordinary one-sided/symmetry theorem.
- `Source215Balanced.p215_dagPerm_balanced` concludes, for every register file R, the exact unchanged `rm_halts p215 ([], R) <-> rm_halts dagPerm ([], R)`.

The concrete data has 2,240 checkpoints, 2,239 decrement checkpoints, and one halt at index 25. Our independent source parser and segment interpreter replay all 4,479 semantic branch obligations. It reproduces 5,018,706 list visits versus 54,514 balanced-tree visits, maximum 13.

There is no new mathematical endpoint hypothesis hidden in this optimization. In particular, it does not change raw numerical-calculus soundness or the ZFC-refutation predicate. Exactness with the old certificate is useful for provenance, but the theorem would be sound for any certificate passing the checked conditions.

The single recorded source-module times, 33.103 s versus 24.772 s, do not establish an end-to-end improvement: the new tree construction/exactness module costs another 13.159 s in that run. Coq 8.18 is not the maintained Rocq 9.1 lane. The packet does not rebuild either complete binary/ZFC endpoint. The 1,426-checkpoint normalized proposal cannot simply be substituted into this raw-pointer checker; its canonical-path theorem must be used or ported first.

## 2. Marker checker: hypotheses that must survive integration

`marker_certificate/MarkerFold.v` uses totalized native semantics: a missing row leaves the configuration fixed, and `Halts` means reaching designated label `halt`. It is not the partial-transition system of the separate terminal-drain research proposal.

For old/new tables O,N and roles a,b, its checked contract requires:

- Equal table lengths, a and b noninitial and distinct, and neither equal to halt.
- Every old incoming edge into a moves right and writes true; every incoming edge into b moves right and writes false.
- Outside a,b, every new row equals the old row after applying the state identification `phi(b)=a`.
- Exact old role rows, new selector/provider rows, and missing new halt rows for both symbols.
- Conditions for every finite row and both symbols; table-length equality extends ordinary-row equality to all out-of-range labels.

The invariant is precisely `state=a -> tape(head-1)=true` and `state=b -> tape(head-1)=false`. It holds from state 0 on **every** complete tape because a,b are noninitial, and is inductive because of the incoming-row checks. No blank-tape or register invariant is being assumed silently.

The exceptional zero block makes three new steps, restores the entire tape, ends one cell right, and selects the proper old successor. All other old steps use one new step. This proves `n <= m <= 3n` and exact boundary tape/head equality.

Reflection under these totalized semantics depends on the checked absorbing-halt property and `phi q = halt iff q = halt`. It cannot be replaced solely by the separate partial-system positive-block argument. The missing-row model also needs the exact working-state closure audit before interpreting designated-halt reachability as the conventional literal TM behavior. That audit passes for these tables.

Our owned checks independently verify all four native `.tm` files against all 303 slots of the literal Coq tables: exactly 215 complete working states, 430 rows, and no transition to a nonhalt hole. They verify M125's dense renaming bijectively, all finite contract rows, and 32 framed local tape cases per variant. The complete startup replay for each variant reproduces 95,714 parent steps, 95,840 target steps, 63 three-step blocks, state 84, head -8, and the same full set of 95 one-cells. These are corroboration, not the arbitrary-tape proof.

M124, FM215, and M125 differ only in provider1, respectively 59,109,125. Provider125 was already suggested in earlier work. None is a 214-state result. The representation bridge is the meaningful remaining integration work, not another handwritten native marker argument.

## 3. Concrete credit proof: what is closed and what is not

`zero_credit/CantorCredit.v` uses the actual Cantor pairing `P(x,y)=((x+y)(x+y+1))/2+y`, the literal tags DROP=0, NIP=1, MP=2, AX=c+3, the actual AX field order y then x, and residual zero/one-plus-tail conventions. A word is nonempty and `encode [DROP]=0`.

The file proves residual descent, executable decode round trips, unique words for all naturals, strict lowering when a selected NIP becomes DROP, and occurrence-level injectivity by restoring that position. Its final schedule is literally all candidates 0,1,2,...; it does not assume an abstract scheduler obeys this order.

The abstract intermediate count theorem still correctly requires `NoDup` occurrences and complete earlier-candidate closure. The final `schedule_cut` construction proves both. Position identity must not be erased, and arbitrary repeated candidates or skipped predecessors cannot be treated as covered. Allowing j beyond the current word's length merely adds positions with no command, which count neither way.

Our separate arithmetic decoder checks 10,000 complete candidates / 15,677 command occurrences, all round trips, 1,606 distinct lowering images, and strictly positive available credit before every NIP. At the end there are 4,045 DROP and 1,606 NIP, surplus 2,439. This is finite corroboration of syntax, not source/TM execution.

The exact physical decoder, candidate refill and control return, theorem-head invariant, initialization, binary simulation, and inherited logical calibration remain endpoint obligations. A physical run that skips a lower candidate would not be repaired by this parser theorem.

## 4. New proposal: replace ordinal lookup refinement by checked-lookup coverage

### 4.1 The actual semantic dependency is smaller

In the inherited `Bisim230.v` soundness section, `getc_in` is the only place list indexing enters the semantic argument. It establishes that a returned checkpoint is among the entries checked by `forallb`. The subsequent `branch_sim`/`sim` proof uses that coverage fact, not ordinal arithmetic or an ordering of entries.

Generalize the interface to:

1. A finite collection of checkpoints C, each with the same two program paths and two successor keys.
2. A lookup function G from keys to optional checkpoints.
3. Every successful G lookup returns a checkpoint covered by the finite all-entry check.
4. The initial segment check and all checkpoint checks use this very same G.

For a target checkpoint, coverage supplies its local check. Induction on a source terminating run then repeats the inherited decrement/segment argument. Every decrement consumes a source step, yielding the strict induction decrease; segment blocks need not be individually positive. Symmetric local checks give the reverse implication without a second expensive finite evaluation.

This yields the same all-register source theorem. There is no requirement that G match `nth_error`, no cardinality/ordinal-size invariant, no uniqueness of checkpoint values, and no required equality to a legacy flattened list. A direct `AllGoodTree -> lookup-success -> EntryGood` lemma is enough; the production theorem need not introduce flattening or list membership at all. The old exact-identity audit can remain separate from the production soundness dependency path.

Coverage is mandatory. Checking only the initial entry or checking a set different from G's possible outputs would allow an unchecked mismatched decrement/halt pair to enter the simulation. Also, the lookup used inside every branch must be the same lookup whose coverage is proved. The proposal does not claim the current compiled `checkTree_halts_iff` already permits dropping `validb`; it needs a newly proved generalized soundness theorem.

### 4.2 A better concrete representation than cut-bearing trees

Use a finite trie `Empty | Branch(entry,left,right)`. Every nonempty node holds one checkpoint. A positive key is inspected structurally:

- xH: return this node's checkpoint.
- xO p: recurse left on p.
- xI p: recurse right on p.

The finite all-check visits the payload at every nonempty node and both children. By structural induction, a successful lookup necessarily returns a checked payload, for every trie shape and every positive key. There are no stored sizes, balancing certificates, binary comparisons, or subtractions.

Use new key j+1 for old ordinal j, including initial key 1. Emit the literal trie untrusted and check its source semantics directly. The new helper draft `PositiveTrieCoverage.uncompiled.v` states and proves the pure coverage and probe-bound lemmas, with no custom axioms or holes. It is only a draft: neither it nor the generalized bisimulation theorem has been compiled here, and the latter is not yet implemented.

Our preferred full data is `positive_trie_certificate.json`. All 2,240 exact checkpoints and successor relations were reindexed. The same 4,479 semantic branches pass. An independent artifact reader checks all 16,383 positive keys through 14 bits and rejects seven corruptions, including swapped children, omitted coverage, old zero-based references, and changed source paths.

Concrete indexing comparison:

| Quantity | Incoming balanced tree | Preferred positive trie |
|---|---:|---:|
| Queried references | 4,479 | 4,479 |
| Lookup node visits | 54,514 | 45,591 |
| Maximum successful visits | 13 | 12 |
| Stored size/cut fields | 2,239 | 0 |
| Successor binary digits, all rows | 45,567 | 45,592 |
| Stored cut binary digits | 4,275 | 0 |

This is 8,923 fewer lookup visits, or 16.37%, beyond the incoming balanced layout. The binary-digit payload total drops by 4,250 when counting successor digits plus removed cut digits; this excludes structural constructors, sharing, serialization, and proof-object overhead. It is **not** a memory or compiled-file-size measurement.

Successful lookup uses one positive constructor per visited node; there is no O(log N)-bit compare/subtract at each level. The usual linked-inductive-constructor model therefore needs O(log N) destructor steps for these keys rather than the balanced arithmetic-routing O(log-squared N) bit-operation upper bound. This is not a kernel runtime measurement or an end-to-end speedup claim. Direct literal emission, checking, and proof-term elaboration all need benchmarking.

An earlier leaf-only routing prototype is retained as `radix_certificate.json` for transparency. It removes cuts but keeps 54,514 visits and inflates successor digits by 8,959. It is strictly less attractive than the payload-at-every-node version and is not the recommendation.

### 4.3 Acceptance gate

1. Compile the generic coverage lemma and prove the generalized source checker soundness using the exact existing segment and path semantics.
2. Compile the reindexed 2,240-row concrete check and exact all-register theorem. Keep the old/new correspondence as an independent audit target, not a semantic axiom.
3. Preserve the public `p215_dagPerm` statement, maintained generator, and exact machine bytes; rebuild both maintained endpoint clients with fresh assumption reports under their pinned compilers.
4. Benchmark ordinary list, incoming balanced tree, and direct positive trie on the same clean/incremental build protocol, including generation and concrete data elaboration.
5. Only then combine with the 1,426-checkpoint normalized lane through its proper canonical-path checker correspondence. The raw and normalized local-check interfaces are not interchangeable by assertion.

This is separate from the pending q2 home macro, terminal drain, canonical WF fold, and sparse lower-calibration proposals. None of their claims is being counted again here.

## 5. Search scope and integration priority

The per-table search receipts sum to 21 tables, 155,277 eligible pairs, 133,827,040 replacement-action tests, and zero surviving pairs. The screen uses backward histories of depth four, bounds local blocks to 45 steps / 200 symbolic nodes, and requires each changed row's block to avoid the other changed row. Mutually dependent replacement rows, longer/deeper contexts, arbitrary extra edits, and source changes remain outside its scope. No search binary or script was rerun here.

For the current task, prioritize the unchanged primary endpoint: the source-checker representation can be simplified without any new machine-level invariant. Keep marker variants and ZC215 as useful independent lanes, but do not present their native or syntactic theorems as complete integrated endpoints. The delivered 1,426 normalized proof and existing ordinary production lane are stronger baselines than old offset certificates when assessing any claimed reduction.

The subsequent `CANDIDATE_BRIDGE_ADDENDUM.md` refines that comparison: M124 and FM215 already have native Lean all-tape proofs, and the generic Core table/renaming bridge already exists. Their remaining integration work is precise semantic-interface matching and finite literal-table compatibility, not automatically a new Lean port. The strict two-marker variants have the simplest local invariant; CM215 has the shortest presently demonstrated exact dense-machine integration. Neither observation establishes a global winner or a fresh full endpoint replay.

## Reproduce this review

Run only the newly owned scripts:

    python -I -B audit_refinements.py
    python -I -B verify_positive_trie.py

They read received files as data and write only this new review directory. `AUDIT_RESULT.json`, `POSITIVE_TRIE_INDEPENDENT.json`, `CURRENT_SOURCE_BINDINGS.json`, and `INTAKE.json` distinguish local checks from supplied compiler receipts. The incoming packet remains intact.

Both scripts reject `-O`, `-OO`, and any `PYTHONOPTIMIZE` environment entry, including when `-I` or `-E` would otherwise ignore it. `OWNED_CHECKER_MODE_CONTROLS.json` records normal runs and 14 rejection controls. Outputs do not probe locally installed proof-assistant tools, so those portable audit results are independent of tool availability. This review did not run a proof assistant.
