# Smaller explicit Diophantine forms for ZFC consistency

Pinned repository: VladimirReshetnikov/ProveIt at
8c6eec9d19ef80538c8e61ff6e0180040583446a.

Start with report/synthesis_report.pdf. Editable TeX, its Markdown source,
and the report builder are included beside it. The report proves the new
reductions, compares the seven wave-4 submissions, and states the exact
inherited compiler and K215 dependencies.

## Reproduce the finite checks

From an extracted, otherwise unchanged archive:

    python3 verify_release.py

Use Python 3.10 or newer with SymPy and NumPy installed. See requirements.txt.
The verifier rejects optimized Python (-O and -OO), verifies the complete
file manifest, then runs newly authored checkers in a temporary copy. It
leaves the delivered tree unchanged. It does not execute source programs
received from the repository; those programs are retained as inert text.

A passing replay certifies the stated finite algebraic, arithmetic, metric,
source, and payload checks. It is not an end-to-end Lean/Rocq certificate,
a proof of consistency, or a bounded search establishing no solutions.

## Mathematical instances and domains

- Twelve positive variables: 110 operations / degree 1081, or 111 / 1041.
- Nine nonnegative variables: 1559 operations / degree 92324*5^32+296.
- Nine positive variables: 1554 operations at the same degree.
- Fourteen unrestricted integers: 1586 operations / degree 813056*5^32+2152.
- Fifteen unrestricted integers: 1594 operations / degree 406528*5^32+2528.
- Fifty unrestricted integers: 29 quadratic residuals, or their quartic sum of squares.

Every output has fixed integer coefficients. The four compiler coefficients
are one coherent tuple selected by COEFFICIENT_BINDING.json, and all four
actual integers are provided under coefficients/payloads/. MF is the shifted
source mask. Do not substitute the native mask or mix ports between packages.

Nine-variable and signed compressed forms have additional fixed coefficient
recipes, described by nine/INDEX_CONSTANTS.json and the signed binding.
Some are far too large to expand. A fixed finite recipe is not another
quantified unknown. The report identifies which integers are materialized.

Circuit registers and named intermediate expressions are abbreviations,
not extra variables. Operations charge binary +, -, and multiplication,
including multiplication by numerals, but not construction of fixed
coefficient leaves. Equality comparisons in systems are free. The three
quantifier domains must not be interchanged.

## Contents

- positive/: inexpensive twelve-positive-variable norm variants and proofs.
- nine/: optimized nine-variable circuits, exact index recipes and checks.
- integers/: unrestricted-integer compressed forms and proof.
- low_degree/: the fifty-integer quartic and its complete residual system.
- coefficients/: new complete native compiler tuple, payloads and adapter.
- audit/: independent mathematical and finite-check reports.
- review/: pinned source comparison, exact source files and live gate counts.
- report/: PDF, TeX, editable report source and optional builder.
- licenses/: inherited licence and attribution notices.

Historical source annotations may name their original package paths. They
are provenance, not active bindings. The root binding and dedicated index
manifests identify every selected instance. PORTABILITY_TRANSFORMS.json
records any release-only path or metadata adaptations.

## Optional PDF rebuild

With Pandoc, XeLaTeX, the DejaVu fonts and fvextra installed:

    python3 report/build_report.py

This edits the extracted report files and therefore changes the immutable
release manifest. Rebuild only in a separate working copy. The precompiled
PDF is already included; a PDF rebuild is not required for finite replay.

## Attribution and scope

This is OpenAI-assisted research for Vladimir Reshetnikov and ProveIt.
New material follows the included MIT No Attribution licence. Inherited
material retains its original terms; read NOTICE.md and licenses/.
No global minimum, new machine-state reduction, proof of Con(ZFC), or new
kernel-certified endpoint is claimed. General ten-integer representation
theorems are discussed explicitly; this archive's variable counts are
claims about its concrete instantiated constructions, not universal records.
