FOUR FURTHER LEAN PROOF SIMPLIFICATIONS FOR DIOPHANTINECONSISTENCY
Reviewed 26 October 2026

Reviewed repository:
  https://github.com/VladimirReshetnikov/ProveIt
Pinned revision:
  9bd29079d5e1c6cc1c0bcaee6cb57d59b835cba9
Compiler:
  Lean 4.32.0

START HERE

Read report.pdf, or edit and rebuild report.tex. The report contains the full
mathematical arguments, concrete source targets, novelty comparison, and
integration requirements for four ideas:

1. Compare Pell coordinates directly across bases to simplify index ordering.
2. Use a natural-number perturbation/majorant kernel for both ratio estimates.
3. Recover the half-binomial value from an exact integer quotient.
4. Describe all rule schedules once and compile both their numerical and
   supplied primitive-recursive interpretations.

The earlier six placed proposal packets and five incoming ZIP archives were
treated as already applied. The archive includes the exclusion audit and its
hashed corpus inventory. Optional and unselected earlier ideas were included
in that audit. Novelty is scoped to that directly inspected corpus.

WHAT WAS VERIFIED

Four independent Lean files, using only Std, compiled with the pinned compiler.
Their logs and exact axiom lists are in evidence/checks/. No sorry, admit,
added axiom declarations, native_decide, or unsafe declarations are used.
Some results use ordinary Lean foundational axioms; see the logs, rather than
interpreting 'no added axioms' as 'every axiom list is empty'.

StructuralSchedule includes all 17 actual rules and the invalid-tag default.
An independent source-transcription check confirms that its legacy numeric
tables match the production tables after documented operation/field renaming.
Lean proves those tables agree with the new syntax for every natural tag, and
proves generic compiler correctness for every raw input.

Exact integer experiments check binomial splits and representative arithmetic
instances. They are supplementary checks, not substitutes for the unbounded
Lean or mathematical proofs.

WHAT REMAINS PROPOSED

This is not an integrated ProveIt patch. The actual Mathlib Pell adapter,
instantiation with the repository's Pell growth lemmas and source rows, the
adapter using its existing binomial_floor_two certificate, and the ScalarPRCode backend remain
to be integrated. Supplied-program tree equality and the four frozen node
counts must then be checked. No full ProveIt build, measured net line reduction,
or build-time improvement is claimed. No repository changes were pushed.

REPRODUCING THE CHECKS

Install Lean 4.32.0 separately, then run from the archive's root:

  python3 scripts/verify_lean.py
  python3 scripts/exact_checks.py

An explicit compiler path can be supplied:

  python3 scripts/verify_lean.py --lean /path/to/lean

To reproduce the source checks against a checkout at the pinned revision:

  python3 scripts/verify_sources.py /path/to/ProveIt
  python3 scripts/check_schedule_transcription.py /path/to/ProveIt

No check script downloads files or executes repository-provided scripts.
The Lean checker writes logs and its result JSON to evidence/checks/ by default.
Use --out-dir for a separate location. The source checks fail if target bytes
have changed; this is intentional. Exact source sizes are baseline observations,
not claimed savings after integration of earlier proposals.

BUILDING THE PDF

With pdflatex and its usual packages installed:

  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

The report uses amsmath, amssymb, amsthm, geometry, lmodern, microtype,
booktabs, longtable, tabularx, array, enumitem, xcolor, listings, xurl,
hyperref, fancyhdr, and needspace. A lakefile and lean-toolchain are supplied as
convenience metadata; the recorded validation invokes Lean directly.

CONTENTS

  report.tex / report.pdf     Full report
  lean/                      Four checked reusable principles
  scripts/                   Lean checks, exact arithmetic, source checks
  evidence/source_targets.json       Target bytes and source measurements
  evidence/prior_art_audit.md         Detailed exclusion map
  evidence/prior_corpus_manifest.json Full directly audited corpus hashes
  evidence/novelty_matrix.csv         Nearest old idea and incremental change
  evidence/candidate_review.md       Independent mathematical review
  evidence/arithmetic_ideas.md        Detailed arithmetic development notes
  evidence/structural_ideas.md        Schedule integration notes
  evidence/checks/                   Actual validation outputs
  MANIFEST.sha256                    Hashes of all delivered members except itself
