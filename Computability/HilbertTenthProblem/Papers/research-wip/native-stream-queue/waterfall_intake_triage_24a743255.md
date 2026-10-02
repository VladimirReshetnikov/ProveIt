# Waterfall intake triage (24a743255)

**Status: triaged, not fully reviewed.** The archive is promising because it supplies a concrete universal-machine matrix, a raw two-half-tape input recipe, and an explicit event-to-macrostep compression. Its README clearly states that its quadratic certificate still has an externally fixed source-machine horizon. No proof, universality transfer, receipt, or operation reduction is newly certified by this intake pass.

Archive: `/home/codex/.codex/worktrees/2a71/Proofs/docs/incoming/Waterfall_Diophantine_Certificates.zip`, SHA-256 `b5d3ee90f9631695afc3c6f34f765b617eb9c631c65ab32705cf3d0e8811a9fc`. The 31 members were safely extracted to a private directory, rejecting traversal, absolute/duplicate names, and symlinks. All 30 supplied manifest entries match. `waterfall_intake_triage_24a743255.json` contains every member's name, size and digest. The archive is unchanged; this note and its inventory preserve the intake handoff.

Read scope: README, source provenance, replay/build scripts, section/theorem outline, the main/input/macrostep statements, displayed polynomial construction, common-column statement, and the first 120 lines of the grouped compiler to locate one bounded follow-up. This was not a complete proofread or code audit. No supplied checker was run, no external citation was independently verified, and the PDF was not rebuilt or visually audited.

## Claims and interface to review next

The credited Iijil matrix has 46 actual clocks; its source serialization is 47 by 47 because one row/column is metadata. Trigger rows in the source are transposed to the article's source-column convention. The claimed increment bound is 12. The underlying Neary–Woods machine has 15 states, two symbols, 29 defined instructions and one missing instruction `(J,1)` as halt. The report expressly flags a primary-paper prose/table inconsistency and says it follows Table 16 and the displayed halt configuration; this attribution/transcription deserves verification in a full review.

Waterfall semantics are strict unique minimum of deadlines `a+Mp`. A minimum tie is undefined, halt occurs before the halt-clock update, nonhalt self-resets are positive, and the halt trigger is zero. The proposed canonical interface starts at state A and head bit 0, with both half tapes supplied as natural integers L,R. The two varying clock values are `2+2L` and `2+2R`: four binary arithmetic operations under the stated free-constant/copy model. A valid serialization bound adds two operations, giving six. The report explicitly excludes the cost of encoding an arbitrary external program convention into L,R.

The macrostep statement describes all internal event blocks, including zero-repeat boundaries, using popped `X=2Q+r` and other half tape Y. Its event count is `c=6+3Q+r+3Y`; its normalized timestamp increment is `2c+7`. The symbolic frontend reportedly verifies 58 instruction/residue cases through strict every-prefix inequalities. A full review should independently inspect those loop-domain/cone checks and final-coordinate identities before accepting the all-input tie-free claim; the reported finite 2,842 concrete macrosteps are supplementary.

For each external k>=1, the exported first-halt certificate has parameters `(L0,R0,C,tau)`, 35k natural witnesses (29 selectors and two direction triples per step), 5k+4 affine squares, and 2k unsquared nonnegative products. It claims an empty or singleton natural fibre. The four terminal constraints require halt state/head, total prehalt firing count C and timestamp `tau=1+2C+7k`. The seven-step delivered fixture has 245 witnesses, 39 squares, 14 products, C=189 and tau=428; these are delivered claims, not newly replayed results.

The resource statement compresses potentially exponentially many Waterfall events into k source-machine macrosteps. Witness bit length can still grow with tape magnitude. The unbounded sequence of macrostep choices and tape recurrences has not been put into one fixed-dimensional Diophantine representation. The report states this limitation explicitly and does not claim to improve the universal 75/87-operation frontier. Factor/witness counts are not a complete optimized arithmetic gate ledger.

A separate common-column class has columns `b_i*1+d_i*e_i`, with relative diagonal d_i>0. Subtracting a common shift yields arithmetic-progression event streams. Its horizon-free companion and 22-operation natural / 26-operation positive-witness three-clock examples belong to a decidable residue-separated class. They must not be reported as universal-machine costs. Parameterizing previously fixed coefficients can raise the degree from two to four, as the report notes.

## Most promising bounded follow-up

After the macrostep frontend passes full review, specialize the forced first instruction before considering an unbounded-history encoding. In the displayed natural system, first-step one-hot/state/head constraints force exactly A0. It moves right, writes 0 and enters B. Consequently the 29 first selectors are constants; the inactive left triple is zero; the active right group's Y equals L0 by input balance. Only `QR0,rR0` remain supplied at the first step.

A literal graph substitution therefore appears to remove 33 supplied coordinates, four identically zero initial squares and both initial complementarity products: candidate counts `35k-33` witnesses, `5k` squares and `2k-2` products. This retains the count/timestamp interface and leaves `R0=2QR0+rR0` plus the later head/terminal constraint that forces the popped bit. For k=1 the terminal state condition remains inconsistent (A0 enters B, not J), so the empty-fibre boundary must remain explicit.

This is an **unimplemented scout**, not a completed optimization. Follow-up obligations are a both-direction natural graph/projection proof, a complete off-zero substituted polynomial identity, coefficient-level export and exact arithmetic ledger, and tests at k=1, zero half tapes, the delivered seven-step halt, malformed inputs, and arbitrary false witnesses. More general selector elimination or unbounded packing should not be inferred from it.

## Outline

The main sections are results/scope; fixed substrate and loader; exact macrostep; one quadratic for a fixed TM horizon; seven-step halt example; compression/semilinearity limits; decidable common-column class; failure of endpoint counts as a general history replacement; reproducibility. Appendices give the complete compact matrix and finite affine-gap certificate. The strongest full-review targets are the macrostep every-prefix proof, the first-halt converse, and the source/loader universality handoff, rather than rechecking only the sample halt.

## Author commands (not executed)

Run in an isolated copy because the scripts regenerate receipts/logs:

```sh
sha256sum -c SHA256SUMS
sh run-replay.sh
```

The runner uses `${PYTHON:-python3}` and Python standard library only, and invokes:

```sh
python3 replay/verify_matrix_definition.py
python3 replay/verify_frontend.py
python3 replay/verify_frontend_independent.py
python3 replay/grouped_quadratic.py
python3 replay/verify_quadratic_independent.py
python3 replay/verify_halting_example.py
python3 replay/verify_certificates.py
python3 replay/verify_release.py
```

Assertions are proof obligations; the README excludes `python -O`. The frontend, grouped polynomial and independent-source evaluators should all be read before running them. `sh build.sh` is the optional three-pass PDF build and is unrelated to the arithmetic checker's correctness.
