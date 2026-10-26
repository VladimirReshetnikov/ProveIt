FURTHER LEAN PROOF SIMPLIFICATIONS IN DIOPHANTINECONSISTENCY
26 October 2026

Read report/report.pdf for the mathematical arguments, novelty comparison,
exact source measurements, validation scope, and further research questions.
The editable source is report/report.tex, with its small companion inputs.

RESULT

Six additional ideas, implemented in six complete source modules:
1. Remove two internal inductions whose successor cases discard the IH.
2. Reuse the existing Pell base-divisibility oddness theorem.
3. Compose divisibility and signed congruences without opening quotient witnesses.
4. Compare Pell indices using simultaneous monotonicity in the base.
5. Keep nonsquare-norm nonvanishing entirely over the integers.
6. Use inverse invariance of a finite permutation's forward-invariant set.

The complete files shrink from 1,530 to 1,440 physical lines, a net reduction
of 90 lines including new helpers and import changes. Existing public theorem
statements are retained. The standalone Pell experiment additionally proves
a stronger theorem with weaker assumptions.

BASELINE

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: b310142330df89e48413c8fce62e7de223e1c7d5
Lean: 4.32.0
mathlib: 81a5d257c8e410db227a6665ed08f64fea08e997

Closing audit snapshot: d163c476db9ca1142d2d73de8fa64c0b2c03a848.
All six targets, imported repository dependency roots and dependency pins
are unchanged there. The patch also passes its application check against
that later snapshot. See validation/freshness-check.json.

APPLYING THE PATCH

In a clean checkout at the baseline commit, first review and dry-run:

  git apply --check /absolute/path/to/this-packet/patches/new-simplifications.patch

Then apply when ready:

  git apply /absolute/path/to/this-packet/patches/new-simplifications.patch

The same six complete replacement files are provided under replacements/.
They are an alternative way to inspect the result, not an additional patch.

VERIFYING

Use the repository's pinned Lean/Lake environment and matching dependencies.
From any directory, after applying the patch:

  bash /absolute/path/to/this-packet/tools/verify.sh /absolute/path/to/ProveIt

The script does not apply or modify source files. It verifies source hashes,
builds the six affected modules and the existing finite-cycle regression
module, prints axioms, and checks the standalone experiments.

To reproduce the textual counts without changing the checkout:

  python3 /absolute/path/to/this-packet/tools/reproduce_metrics.py /absolute/path/to/ProveIt

The Git object for the baseline commit must be available locally. The
replacement source hashes, baseline hashes, and counts are recorded in
validation/manifest.json.

VALIDATION ALREADY PERFORMED

All six complete replacements compiled together in a combined module tree.
NativeFieldCycles2011Checks compiled against the replacement, preserving its
511 self-loop, zero-loop, and infinite-type offset-20 examples. The seven
edited existing theorems print only propext, Classical.choice and Quot.sound;
the new coordinates_mono_base lemma prints only propext. No sorryAx or new
axiom appears in the selected result audit. The patch passes git apply --check.

The exact-version mathlib cache was reused. The entire ProveIt repository was
not rebuilt, and no compile-time improvement is claimed. The public arguments
hy, hp and hn deliberately remain for compatibility and cause unused-variable
linter warnings in their respective changed theorems.

NOVELTY AUDIT

The initial audit covers the five ZIPs in docs/incoming at the baseline and
the sixth retired DiophantineConsistency simplification packet linked by its
README. It records 81 prior idea families with 103 checked exact report/note
locators. The closing audit additionally covers both newly arrived ZIPs at
d163c476db9ca1142d2d73de8fa64c0b2c03a848; see the final-refresh addendum in audit/.
Novelty is relative to these eight packets. A related canonical-evaluation
idea was screened out, and the unimplemented constructor-algebra direction
is not part of the contribution.

BUILDING THE PDF

With XeLaTeX, latexmk, Latin Modern fonts, DejaVu Sans Mono, and the standard
packages used in report.tex installed:

  bash report/build.sh

FILES

report/       PDF, LaTeX, source excerpts, metrics and build script
patches/      Combined reviewable patch
replacements/ Complete replacement Lean modules at repository-relative paths
experiments/  Standalone alternate proofs and stronger Pell theorem
validation/  Source hashes, exact metrics, compiler logs, axiom audit, versions
audit/        Prior-proposal ledger, comparison and independent conceptual review
tools/        Integration verification and reproducible metrics scripts

The package contains no compiled Lean artifacts or downloaded dependencies.
