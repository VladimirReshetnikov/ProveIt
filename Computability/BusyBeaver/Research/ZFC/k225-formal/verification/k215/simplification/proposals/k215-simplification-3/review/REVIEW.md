# Independent technical review

Reviewed on 21 October 2026. Scope: the evolving report, supporting technical reports, finite checkers, and uncompiled Lean/Rocq drafts. This review did not run either proof assistant and does not certify a new endpoint.

## Result

The principal research conclusions are supported at the stated finite/structural level:

- The original ordered primitive CFGs are not equal. Their only differences are 256 adjacent increment swaps, attributable to two structured DAG nodes. Reversing nodes 188 and 190 makes the ordered CFGs equal. The unmodified increment-count block CFGs already agree.
- The 2,240 raw checkpoint rows quotient to 1,426 canonical paired test/halt sites, leaving 814 aliases. The proposed `Related` predicate supplies the exact consumed-path equations required by existing `EntryGood`; it can reuse `Bisim.halts_iff`. Deleting aliases without changing the relation would not work.
- Reusing the existing transition trie at symbolic sites is a plausible small refactor. Both proposed patches apply separately to the inspected source and preserve all 105 public block theorem statements. They remain uncompiled.
- CM215 has a short incremental proof route. It does not reduce the inherited proof dependency closure. No 214-state correctness endpoint or calibrated new 214-state table is established.

## Issues found and disposition

1. **Generic stuttering theorem omitted halt preservation. Corrected in report source.** Halt reflection alone proves only the converse direction. The theorem now explicitly requires the map to preserve and reflect halt. The exact CM checker already checks both, so the concrete finite result was not affected.

2. **Rocq Python validation could accept corrupted inputs or run without assertions. Hardened; independent retest recorded separately.** Initially, all three Rocq scripts ran under `-O`. Changing the first offset from zero to one was accepted under `-O`; replacing a Boolean token by `FALSE_NOT_A_COQ_BOOL` was accepted even without optimization. The latter occurred because every non-`true` token was parsed as false. The revised scripts import `validation_guard.py`, enforce literal hashes for all three source inputs before parsing, reject optimized execution, and validate Boolean tokens. The earlier negative-control logs are retained as historical evidence, not as the current status.

3. **Latest versus historical evidence required explicit separation. Corrected in report source.** The published 185-module phase-four receipt is incremental: 10 fresh modules and 175 hash-bound reused objects. It is not a fresh full replay by this investigation. Current Lean sizes 30,114 / 7,563 / 14,916 bytes supersede the earlier rho8/AX/site-facade sizes. Earlier compilation times remain historical measurements.

No further substantive mathematical blocker was found in the reviewed source. Compiler acceptance remains an outstanding gate, not a review pass.

## CM transport proof check

The three-clause invariant is genuinely state-local. The extra clause at state 156 makes the old-176 zero-branch marker condition one-step inductive. The five-cell enumeration checks every newly exposed neighbor, not just blank exterior cells.

The finite simulator checks the read position before each transition; writes occur at that same checked position. It compares the complete represented tape support and final head, not just the scanned symbol. Therefore the proposed whole-tape frame theorem is the correct remaining semantic bridge: exterior cells are never read or changed by these blocks. This is an ordinary mathematical argument still to be formalized, not a consequence of a hash or a Python success flag.

For total absorbing-halt semantics, positive block lengths give `f(n) >= n`. If the target halts at time `t`, it is halted at `f(t)`, and halt reflection makes the source halted at `t`. Forward halting uses halt preservation. Noninjectivity of the control map is harmless. Extend halted-source schedules with one absorbing target step. Strict interior nonhalting is checked for the concrete nonterminal blocks.

The warning about Lean tape representation is essential and correct: equal tape reads are needed, not equality of the order-sensitive finite-support lists. A Lean theorem over its finite-support configurations should not be advertised as quantifying over arbitrary infinite-support tapes.

## Static draft review

- `CanonicalRows.uncompiled.lean`: the semantic relation and `rows_bisim` construction match the inspected `RMBisim` interfaces. The Boolean checker soundness lemmas, concrete row instantiation, and compilation are explicitly absent. No obvious static interface error found.
- `IncrementPairSwap.uncompiled.lean`: sequencing, the distinct-register side condition, update commutation, and total deterministic node contracts match the inspected `RMDag`/`RMTransfer` signatures. Actual overlays, finite closure facts, and compilation remain absent.
- `KFastSites215.uncompiled.lean`: existing pointwise `fast215` equality is lifted using Lean's existing function-extensionality theorem; no new axiom is postulated. The two independent patches overlap in import headers and should be integrated deliberately rather than assumed to compose mechanically.
- Rocq packed-path drafts preserve both ends of paths through positive binary constructors. The existing ordinary `check_iff` signature matches the proposed application. The runtime proposal correctly uses pointwise evaluator rewriting/induction instead of adding functional extensionality.

## Independent executed checks

All replay work used disposable copies; report/source snapshots and sealed machine packets were not modified by this review.

- Normal replays: CM transport; candidate-interface audit; three Rocq graph/certificate checkers; all four Lean profiling/canonical-row scripts; full runtime differential replay. All passed.
- Both patch dry runs passed against inspected source, and all 105 block statements were unchanged.
- CM negative controls rejected a weakened marker mask, a missing mask, wrong halt, zero-step rule, `-O`, and `-OO`.
- All 40 window-abstraction certificates passed independent closure and exact-leastness checks. Each retains 215 controls and 430 read rows. The supplied window negative controls also passed.
- Rocq hardening retest: see `rocq_hardened_retest.log`. The historical failures are documented in `rocq_negative_controls.json` and associated logs.

Replay receipts are under this directory. Recorded Python replay durations are only review execution diagnostics, never Lean/Rocq benchmark measurements.

## Remaining acceptance gates

Compile every new draft with the pinned toolchain; prove canonical-checker soundness and concrete row facts; prove the CM locality and positive-stuttering library; bind exact native/dense tables; check both endpoint directions and assumption reports; run the required clean closure audit. Benchmark clean and incremental work separately. None of those obligations is replaced by this review or the Python checks.

## Final report and visual QA

The final report incorporates the GC-ZC215 comparison with explicit attribution of overlapping incoming prior/parallel ideas; the conditional, fixed-word AX-first positive-code argument for literal cutoff 1; the bounded 1426-to-1423 labeled minimization result; and the preferred existing-Bisim/tsite adapter. The stuttering statement now restricts the simulated source steps to nonhalting configurations, while requiring both halt preservation and reflection. Freshness is limited to the three explicitly checked upstream files.

All 11 pages of the final PDF were rendered and visually inspected after rebuilding. Document QA passed, with no final TeX log warnings or box errors. Exact report hashes and checks are recorded in `report/QA.md` and `report/qa/final_qa.json`. This does not add any Lean/Rocq compilation or 214-state construction claim.
