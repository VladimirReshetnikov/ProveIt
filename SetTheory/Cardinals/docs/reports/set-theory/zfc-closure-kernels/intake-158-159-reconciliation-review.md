# Independent reconciliation review, batches158–159

Source/evidence review only,17 October2026, at HEAD `901dd500563669f9e398084cc9695ede6a29e4b0`. Read the entire `/tmp/zfc-intake-158/appendix.md`, all five complete-source intake dossiers, the partial-source dossier and placement records, and the current maintained declarations/records needed for the two stale-note corrections. No compiler, version query, test, recovery helper or experiment was executed. The reviewed appendix bytes and input fingerprints are pinned in the companion JSON.

No mathematical or proof-status blocker was found. The appendix correctly retains PA as the original goal, separates the closed external252 endpoint from unfinished internalization, counts the shared target2 completion only once, and keeps conditional local181-contract success distinct from a complete smaller machine. The source51/52/54 and salvaged56 summaries agree with the respective review dossiers; this reviewer did not independently rerun their suites or redo archive recovery. Existing placement records support812+321=1133 ancillaries and34+6=40 archive-only files.

Three narrow appendix wording corrections are warranted:

1. **Line190: physical versus logical register numbers.** The worked countdown transfers **physical** register8 into physical register7, namely logical X into H. Without saying physical, `R8` can be read in the logical `[N,T,W,A,D,H,X,Y,L]` convention used elsewhere. Replace “transfers entry register8 into register7” with “adds the entry value of physical register8 (logical X) to physical register7 (logical H)”; then say “clears physical register8” and use `3*R8(entry)+2` for the successful-source-step clock. The matrix is `(R7,R8)↦(R7+R8,0)`; it does not overwrite the old R7.
2. **Line138: not every semantic control is strictly larger.** Deterministic MP costs302/305 versus281, and the nonbaseline first-production controls284/285. The primitive-bottom/dual controls also include a281-state tie. Replace the unqualified “Deterministic MP and other semantic controls are larger” with “Deterministic MP is larger; the other semantic controls do not improve the measured backend.” No state improvement follows in either case.
3. **Line127: define the proxy being bounded.** “Their additive proxy” has no definition in the appendix. Use “For four pairwise-disjoint progressions with positive integer moduli and nonnegative offsets, the additive proxy `Σ_i(m_i+t_i)` has minimum22, attained by uniform four-way residues.” This preserves the precise restricted statement and prevents reading22 as a TM-state lower bound. The surrounding text already correctly separates281 backend states from the optimized252 table.

The planned addition of218 selected source cases/1738 regenerated matrix targets is supported by `/tmp/zfc-intake-158/replay-55-countdown/target-regeneration.json`. Retain the word *source*: these are source-reference targets, not1738 binary macro proofs. The181 positive contract replay is separate. The dossier already preserves the initial reviewer-adapter metadata-shape failure and corrected exact-cases comparison; it need not be recounted in this short appendix if the full dossier remains linked.

## Exact minimal corrections to current notes

**`Computability/BusyBeaver/Research/ZFC/safe_initializer_families.md:12–16`.** The pending3010-entry check is stale. `Bisim254.lean:3155` quantifies over every common register file and relates literalProg254 to the path DAG at empty pointers. `results/bisim254-optimized-verification.json` records the full3010-entry PASS,555.41s build and successful audit. `DirtyProgram254.lean:66` supplies the safe-state path endpoint. Replace the sentences beginning “The prepared literal…” through “claimed here” with:

> The checked `Bisim254.prog254_halts_iff` transports every common register vector between literal `Prog254` and the path DAG at empty instruction pointers. Its full 3,010-entry kernel check has passed; see [the verification record](../../../../../../Computability/BusyBeaver/Research/ZFC/results/bisim254-optimized-verification.json).

Keep “The generic statement supplies no binary frame theorem.” The bridge is a register-program theorem and does not itself construct a binary startup for arbitrary safe seeds.

**Related stale wording at `safe_initializer_families.md:37–39`.** The same note calls `Good 3`, `Good 9`, `Good 18` and `Good 21` prepared callers for a “pending path-certificate audit.” The full current audit is no longer pending, but its saved audit source does not contain these four specific caller probes. Do not claim those probes passed. Minimal accurate replacement:

> The small positive instances `Good 3`, `Good 9`, `Good 18` and `Good 21` follow from the same construction.

**`Computability/BusyBeaver/Research/ZFC/permutation252_frame.md:72–74`.** The external Choice comparison is also closed. `BinaryZFC252.lean:28` and `choice_calibration254.md:3,16` give the unconditional external endpoint; `choice_calibration254.md:22` keeps PA internalization separate. After the existing sites-verification link, replace the final stale sentence with:

> The [standard-ZFC Choice comparison](../../../../../../Computability/BusyBeaver/Research/ZFC/choice_calibration254.md) is also closed externally. [PA internalization](../../../../../../Computability/BusyBeaver/Research/ZFC/pa_internalization.md) remains open.

These are documentation corrections only. They neither add a fresh proof check nor weaken the remaining PA obligations. No repository file was edited by this review.

Publication note: three relative project links have been adjusted for this report-host location; the review record identifies the original scratch draft.
