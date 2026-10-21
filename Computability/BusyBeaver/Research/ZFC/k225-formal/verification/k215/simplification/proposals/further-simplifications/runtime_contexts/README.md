# Context factoring and a universal return-to-dispatch contract

## Useful new result

The strongest new opportunity is a small, table-certified **return scanner**, not a full new interpreter or an unqualified DAG quotient. One generic word contract replaces **1,532,123 old symbolic steps by 15,673 contract applications** in all 6,176 existing branch runs. The accelerated owned interpreter, actually resuming from each macro's new normalized output, passes all 6,176 original endpoint tests with **926,351 dispatches instead of 2,442,801**, a reduction of **1,516,450 (62.0783%)**.

These are abstract symbolic dispatch counts, **not Lean reduction counts, runtime measurements, kernel proof sizes, or formal certification**. The macro still inspects the symbolic left list; its proof and guard are not free. All original 4,751 leaf obligations, 6,176 branch outcomes, arbitrary-natural register/gap semantics and endpoint targets are retained.

No Lean or Rocq executable was found. `HomeReturn.uncompiled.lean` is a proposal, not a compiled theorem. No incoming Python/Lean/Rocq code was executed and no sealed or repository file was changed.

## Exact source identity

All newly downloaded files are pinned to `beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc`, with exact Git-blob and SHA-256 verification in `INPUT_PINS.json`. The primary runtime `KSim`, `KRuntimeCore`, and `KTable215` blobs equal the earlier checked snapshot. `symbolic_owned.py` is an owned independent transcription adapted from the earlier audit, not the incoming packet's checker. Every executable imports its input-pin verification. All programs reject optimized Python.

The new `fm215-compression` packet's decoder certificate is read as data. Its native labels are translated only by the declared formal relabeling 301→102, 302→120, 254→230. The complete source leaf list is independently compared to the literal current Lean `t215`, and all local transitions are checked against literal `KTable215`.

Primary anchors at this pin:
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KRuntimeCore.lean`: `StepOk`, `sstep_sound`, `exec_sound`, `sMatches_conc`.
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KZip.lean`: `zL`, `zR`, `zl_padl`, `run_add`, `Reach.trans`, `Reach.trans_reach1`, `Reach1.trans_reach`, `scanL`, `scanR`.
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSim.lean`: `start`, `tgtConf`, `runTo_sound`, `Covered`, `sim_step`, `halts_iff`.
- `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/fm215-compression/evidence/decoder_context_certificate.json`.

## 1. The return contract and its proof

Write lists in zipper order: a left list is read leftwards, a right list rightwards. Let W = U ++ [true], and assume W contains no eight consecutive false cells. For every right list R and natural k,

    zl 2 (W ++ replicate k false) R
       reaches positively
    zc 84 [true] (reverse U ++ R).

The left exterior must be blank. It is NOT an arbitrary left frame. The marker is the final true cell of W, hence the leftmost one of this finite left list. The entire right frame R is arbitrary and unchanged. No source-path, register, branch, gap-lower-bound or box-oracle hypothesis is needed for this word theorem.

The only required table facts are these 18 rows:

    q_i = [2,3,5,9,15,23,34,50][i], 0≤i<8
    M q_i true = some (true, left, 2)
    M q_i false = some (false, left, q_(i+1))       for i<7
    M 50 false = some (false, left, 75)
    M 75 false = some (false, right, 75)
    M 75 true = some (true, right, 84).

Starting specifically at state 2, i records the number of consecutive zeros most recently scanned. Reading a true resets i to zero. The no-eight-zero predicate keeps the scan in these eight states until it reaches the final marker, which also resets to state 2. All writes preserve the scanned cell.

After W, the head is immediately left of the marker in state 2. Eight blank-left steps enter state 75 nine cells left of the marker. Nine blank-right steps reach the marker, and one true-right step enters state 84 just right of it. Thus the **physical exact clock is |W|+18 = |U|+19**. The mathematical word theorem gives this exact number by counted induction; the present uncompiled helper deliberately states only `Reach1`, sufficient for the existing endpoint. A formal exact-clock theorem would need a counted `LeftWord` helper or direct `run` equation, not just the existing existential `Reach` lemmas.

`HomeReturn.uncompiled.lean` supplies a generic unchanged-word `LeftWord.sound` draft, with both frames quantified, then the home composition and a `StepOk` wrapper. The concrete 18-step boundary proof and symbolic guard proof remain explicit theorem hypotheses, not axioms or `sorry` placeholders. Their full kernel implementation is the next gate.

## 2. A guard valid for every natural gap

The macro only considers state 2 with `onl=true`. It removes trailing blank segments from the left list and requires the remaining last segment to be a literal true marker. Let W be the remaining segment list.

- False segments removed at the far left are blank padding of arbitrary length, including lengths depending on n. `zl_padl` justifies their removal for every n.
- Inside W, a false run with positive n-coefficient is rejected. A constant false run contributes its exact length to the zero streak.
- A true run `a*n+c` resets the zero streak if c>0. If c=0, the guard conservatively treats it as empty. Increasing n only inserts true cells, which cannot introduce eight consecutive zeros. This proves n=0 is the worst case for this predicate.
- Boxes inside the scanned word are rejected. The right side is entirely opaque and may contain any register box; the macro never enters it.

Consequently the guard does not introduce a hidden bound on n, register values or register-file size. For all n and vs, successful `home s = some t` must prove `Reach1 M (conc n vs s) (conc n vs t)` independently of `Valid br vs` and `BoxLemmas M`.

Two real candidates are conservatively rejected: path `11011`, brk 1; and path `1111110`, decnz-zero. At both, state 2 is already left of the marker: the left list is empty and the right list begins true. The current macro intentionally falls back to the old executor. A separate 18-step boundary macro could cover them, but they are not counted as successes or treated as counterexamples to correctness.

## 3. Concrete checks and limitations

`profile_home.py` replays every candidate using the old symbolic step function until the next right-facing state 84. It compares complete normalized symbolic configurations, confirms positive progress, and records all cuts. It resumes the raw original output so the cut ledger remains exactly the old execution.

Separately, `verify_home.py` actually resumes the macro-produced normalized output. It reaches all 6,176 original branch targets and has the same dispatch counts:

- 15,673 macro applications.
- 910,678 ordinary symbolic steps.
- 926,351 total enhanced dispatches.
- 1,516,450 fewer than the original 2,442,801 dispatches.

A second, absolute-coordinate interpreter checks complete finite-support tapes, not just local windows. It verifies 32,444 exhaustive safe-word/right-frame cases (word prefixes of lengths 0 through 12), plus 1,485 symbolic-run instantiations at n = 0,1,2,7,31. It checks the exact physical clock and output head. Five negative guards reject eight zeros, a missing marker, a wrong entry state, an unbounded internal false run, and a disappearing true run that joins eight zeros. These finite checks test the design; the all-input conclusion rests on the mathematical induction above and still needs kernel formalization.

## 4. Reuse the current proof pipeline

The low-risk integration is one shortcut in front of the existing `sstep`, retaining the old function as fallback. Its success bit is true because the shortcut proves `Reach1`, not merely `Reach`. Prove the new shortcut's `StepOk`, then reuse the induction already in `exec_sound` unchanged. `sMatches_conc`, `runTo_sound`, register `BoxLemmas`, exact site targets, `SiteCoverage`, and the final halting argument remain semantically the same.

For a generic evaluator accepting arbitrary M, the 18 row conditions must be checked or supplied by a certified table-specific interface. Do not assume every table has this scanner. A runtime row guard is safe but may add repeated lookup overhead; a table-specific proof configuration can avoid it. The existing balanced-table equality proposal is complementary.

If the existing `sstep` definition is extended while preserving its signature, the current public `checkEdge` and `Covered` types can stay unchanged, and all site checks are rerun with the new evaluator. If instead a separate enhanced checker is introduced, semantic reachability alone does NOT imply the old Boolean `checkEdge = true` with its fixed fuel. One must either use the enhanced checker consistently or expose a semantic site-spec interface. There is no completeness theorem in the existing soundness direction that permits silently converting a macro proof back into the old Boolean certificate.

A semantic `SiteSpec M Q e` should include Q.length≤48, r<9 where relevant, and the exact old `start`/`tgtConf` `Reach1` contracts for every n and `Valid br vs`; halt carries the corresponding `Halts`. `checkEdge_sound` follows from existing `runTo_sound` and `runHalt_sound`. The current `sim_step` proof can consume these facts directly, preserving its path/overflow/growth arithmetic and register lemmas. This refactor is especially useful for shared decoder contracts, but is not necessary merely to add the home shortcut to the existing step function.

Acceptance gates: compile the generic and table-specific lemmas under the pinned compiler; compare one small and one large site batch; compile all nine batches, coverage, both closed endpoint clients and their original axiom audits. Benchmark old, fast-lookup-only, home-only, and both on the same machine/compiler with serial clean and incremental builds. No 62% wall-clock claim is justified by these operation counts.

## 5. Further decoder factoring without erasing continuation context

The incoming certificate has 234 `(node,state,two-bit-suffix)` roles, 371 internal bindings, and 97 primitive bindings. Its suffix contexts cannot simply be discarded.

An owned independent checker finds that every group with the same exact `(source subtree, entry state)` has identical successor roles. Keeping its suffix set as an admissibility predicate yields:

- 180 `(node,state)` roles with explicit admissible suffix sets.
- 287 internal graph bindings and 73 primitive graph bindings.
- 371 guarded references to only 281 independently checked local TM contracts.
- Of those 281 contracts, 252 read no predecessor cell, 25 read one, and 4 read two.
- All 4,750 expanded internal occurrences are covered. The full literal source leaf list equals the current Lean tree.

`decoder_factored_certificate.json` materializes this graph and its local contract table. The incoming packet had already observed 281 distinct traces; the new result here is uniform-successor role factoring with the guards retained and explicitly referenced local contracts. This verbose JSON prototype is 45,686 bytes versus the old certificate's 33,084 bytes, so no raw-storage reduction is claimed. Every local contract restores its entire finite read window, moves exactly one cell right, and stays inside that window until exit. It therefore frames arbitrary exterior tape. Guard inclusion and suffix-update closure are checked on each graph edge. This reduces stored interfaces and local replay duplication; it does not claim to eliminate the 371 finite guard-reference checks or establish primitive runtime contracts.

The 73 primitive bindings still represent the already-known 68 distinct `(entry state, bit, source edge, first action)` signatures. A first transition is NOT a complete primitive action/return contract. The appropriate missing primitive interface quantifies the entire preceding path P, gap n, register list vs and branch, and maps the exact leaf-entry configuration to the exact `tgtConf` using the whole Q=P++[b]. Crucially, P must belong to the role's accepted prefix language, defined by following the checked role graph from the root. The two-bit suffix predicate is sufficient for the short internal decoder blocks, NOT asserted sufficient for primitive action/return: actual primitive runs can revisit dispatch with modified path/register-marker data.

More explicitly, for a primitive binding `(role,b,e)`, require `RolePath role P`, `|Q|≤48`, and the branch's original `Valid br vs`. Its entry is

    zc q (reverse P ++ [true])
      (b :: replicate (n + (64 - |Q|)) false ++ true :: sepsR vs).

For each e/outcome this reaches the old `conc n vs (tgtConf successor overflow effect)` positively; halt instead establishes `Halts` there. The internal decoder theorem reaches this entry from `conc n vs (start Q)` without changing the tape. `Reach.trans_reach1` composes them; `Halts.of_reach` handles halt. Here `RolePath` preserves exact continuation semantics while still allowing a proof by induction over the finite shared role graph. It is a specification for the missing primitive theorem, not a claim that 73 closed simulations already establish it. Break/continue targets, overflow and growth must retain their old formulas. The newly identified home contract factors a large, box-independent part of these returns without pretending a bare DAG node determines the continuation.

## Replay

From any location with this directory intact:

    python -I -B factor_decoder.py
    python -I -B profile_home.py
    python -I -B verify_home.py
    python -I -B test_rejections.py

Only the standard library and bundled exact data are needed. There are no references to another research directory. `inputs/decoder_contexts.py` is retained solely as incoming source evidence and is NEVER imported or executed. The four owned entry points and their helper are the only executed code; test_rejections.py invokes only the first three with optimization flags or in a temporary modified-input copy. See `decoder_factored_result.json`, `home_profile.json`, `home_independent_result.json`, and `home_cuts.json` for results.
