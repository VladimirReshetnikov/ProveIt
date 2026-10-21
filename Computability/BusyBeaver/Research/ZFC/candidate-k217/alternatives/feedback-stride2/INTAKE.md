# Intake note: feedback scheduling and a corrected stride-two 217-state machine

Source archive `Feedback_Scheduling_and_Corrected_217_2026-10-21.zip`, arrival commit `1083e2b5ff`;
pinned ProveIt commit `f5b2db607f` (`provenance/UPSTREAM_PIN.json`).

Placed in batch 203 as delivered and complete: every staged file is byte-identical to the archive
(search logs stay out by the root ignore rules). Nothing was rerun or reviewed at intake; the claims
below are the delivery's. The delivery README is `README.md`, its one-page status `STATUS.txt`. The
archive is recoverable with
`git show 1083e2b5ff:docs/incoming/Feedback_Scheduling_and_Corrected_217_2026-10-21.zip > Feedback_Scheduling_and_Corrected_217_2026-10-21.zip`.

**Why it was kept.** Batch 203 preserved unique alternatives and discarded essential duplicates.
`companion217/global217.tm` is a working 217-state constant-bias/stride-two machine: its own
6,153-case universal runtime, exact source binding, independent startup and written calibration
(`companion217/CALIBRATION_REVIEW.md`, `CONSTANT_BIAS_THEOREM.md`). It is not a state renaming of
the accepted [K217](../../README.md) or of any other table in the repository (rooted breadth-first
canonical form; intake check). It does not improve on K217's state count; it is a different
scheduling construction. The packet's main positive result, the abstract feedback scheduler with
cofinally many adjacent pairs of halting candidates (so candidate gaps of one or two are complete),
is what the stride-two design rests on.

**Not a 215-state alternative.** `machine/feedback215.tm` is the earlier scratch-biased
short-transfer experiment (it appears in the comparison corpora of the batch-202 packets). Its
primitive runtime passes, but its CC3 return reaches selector ordinal 23 instead of scheduler
ordinal 0, so it halts unconditionally after the first AX; `evidence/` replays that
counterexample. `formalism/` tables and `physical_search/source200/provisional222` are pricing and
search records, not calibrated machines. No exact-table Lean or Rocq endpoint is claimed.
