Arithmetic proof-refactoring evidence
====================================

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 60e9c5d620c6c387d932876cfa2d9376f64ea56c
Lean: 4.32.0
mathlib commit: 81a5d257c8e410db227a6665ed08f64fea08e997
Source directory:
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/

Checked replacements
--------------------

1. NativePellStepDown.lean: remove redundant Nat-to-Int cast witnesses in
   eq_of_residues; omega discharges the same linear argument directly.
   Declaration: 15 -> 8 physical lines. Whole file: 248 -> 241 lines.
   This is a small proof-only simplification with no new heartbeat cap.

2. NativeCoefficientBounds.lean: factor all 22 row-bound proofs into one
   conditional-leaf tactic, and shorten published_large_scale using pow_add.
   Row-bound block: 566 -> 15 physical lines (including option/comment).
   Whole file: 679 -> 122 lines. The combined proof needs the scoped
   maxHeartbeats 4000000 option. It is an OPTIONAL source-maintenance tradeoff:
   observed full-file wall time increased from 24.42 to 111.37 seconds.
   Do not interpret its shorter source as an elaboration speedup.

Both complete original and replacement files passed Lean with exit code zero.
All public theorem signatures are text-identical (8 coefficient, 7 Pell).
The audited declarations in both baseline and candidate depend only on the
same standard axioms: propext, Classical.choice, Quot.sound.

These patches touch separate modules and can be applied independently. Both
jointly passed git apply --check against the pinned checkout. Clean full
sources in lean/ contain the same proof bodies used for validation; only
review-only #print axioms commands were removed. No source checkout was
modified during this review.

Verification and reproducibility
--------------------------------

The original project toolchain and lake-manifest pin should be retained.
After fetching the project's pinned dependencies and building the original
imported modules, a candidate can be checked from the repository root by:

  lake env lean -M3000 -j1 /absolute/path/to/lean/NativeCoefficientBounds.lean
  lake env lean -M6000 -j1 /absolute/path/to/lean/NativePellStepDown.lean

For the axiom audit, append to temporary copies:

  #print axioms DiophantineConsistency.NativeCoefficientBounds.abs_rowCoefficient_le_envelope
  #print axioms DiophantineConsistency.NativeCoefficientBounds.weighted_rowCoefficient_lt_published
  #print axioms DiophantineConsistency.NativeCoefficientBounds.published_large_scale

or for the Pell file:

  #print axioms DiophantineConsistency.NativePellStepDown.eq_of_residues
  #print axioms DiophantineConsistency.NativePellStepDown.source_index
  #print axioms DiophantineConsistency.NativePellStepDown.source_index_of_strong

The evidence logs include these audits and exit codes. metrics.json gives
exact source hashes, physical-line/byte counts, commands, versions, scope,
and individual run timings. These are single runs on a shared host, not a
controlled performance benchmark; timings include lake env startup. The
Pell baseline and candidate both exceeded the artificial 3 GB import cap
before succeeding at 6 GB. This was not a proof failure in the candidate.

Examples and future proposals
-----------------------------

examples/BasicNat.lean passes with Std alone. It demonstrates short proofs
of the existing wholeShift identities using named natural-number lemmas.

examples/SmallArithmetic.lean passed Lean and includes a Finset.sum_le_one_iff
proof of the copied zero-or-selected statement, the Pell and exponent proofs,
and generic cyclic residue lemmas for ZMod (N * L). The zero-or-selected and
cyclic residue examples are theorem-level checks; their original full Current
modules were not rebuilt with these changes.

evidence/coefficient-basis-audit.json is an exact-integer Python audit of the
coefficient-table polynomial basis. It supports a future certificate design
but is NOT a Lean proof or certificate. That design still requires a general
bound theorem and kernel-checked equalities tying vectors to original rows.

Rejected experiments
--------------------

The combined coefficient proof failed the default 200000 heartbeat budget;
the delivered candidate scopes an increased budget to that one declaration.
Per-row repeat-driver and split_ifs variants also failed default resource
limits and are not provided as working alternatives. They are summarized in
metrics.json. No native_decide or new axioms were used to bypass a failure.
