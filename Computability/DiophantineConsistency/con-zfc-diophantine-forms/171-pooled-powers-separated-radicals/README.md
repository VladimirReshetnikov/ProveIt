# Pooled powers and separated radicals for Diophantine consistency

Research prepared for Vladimir Reshetnikov, 25 October 2026.

This release supplies explicit polynomial equations, ordinary soundness and
completeness proofs, full fixed coefficients, constructive witness maps, and
standard-library reproducible finite checks. For each stated domain, the
ordinary proof establishes in ZFC that absence of solutions is equivalent to
syntactic Con(ZFC), relative to the explicitly retained logical calibration.
No consistency decision, global minimum, or new end-to-end kernel certificate
is claimed.

## Principal results

- Integer quartics: 217 variables/154 rows, with 25949 terms and height 4576,
  or 14615 terms and height 16866. Two 218-variable companions trade support.
- Natural quartics: 202 variables/154 rows, with 9818 terms and height 239204765,
  or 12706 terms and height 31145294. Two 203/204-variable companions trade support.
- Ten positive variables:degree 232 at 85 integer-leaf operations, versus 87;
  also degree 348 at 77 operations, between the incoming352/76 and290/79 points.
- Twelve unrestricted integers:degree 512 at 132 operations. This is an explicit
  four-root witness-elimination method and within-twelve tradeoff, not a global
  frontier:existing eleven-variable equations dominate its three basic metrics.
- Separately calibrated whole one-anchor7309 tuple specialization, credited to
  its incoming source: 172011 raw bytes, with explicit big-endian storage.

Each variable count is the complete number of independent quantified coordinates.
All degree-four equations include every quadratic residual and every collected
coefficient. Compact polynomials supply every live binary gate and every full
fixed integer. Addition, subtraction, multiplication, squares and fixed scalar
multiplications each cost one; reuse is free. No rational-leaf count is substituted.

## Read first

1. report/main.pdf and report/main.tex: integrated article and editable sources.
2. integer/PROOF.md and natural/PROOF.md: complete ordinary arithmetic/domain proofs.
3. positive/PROOF.md, positive/q4_interpolation/PROOF.md and
   positive/one_anchor7309/PROOF.md: the compact equations and full tuple boundaries.
4. roots/PROOF.md: signed squareclass separation, adjacent-Pell rational descent,
   all-zero integer maps and exact degree.
5. reviews/: independent AI-assisted mathematical reviews and finite receipts.

The source snapshot is ProveIt commit
892d73e1ab4bc5fd34ecca1967b06dc47ca95494.
See reviews/BASELINE.md for matched-source comparisons. A bounded late audit at
fb1bed5eb7196cf35abfaa746c18c6ee7eae6cfb confirmed the same arithmetic
boundary, with source placements byte-identical. Its main display now uses the
zero-weight6007 tuple at 141226 raw bytes. Our 7309 sidecar is frozen and
separately calibrated, not a latest-storage-record claim. Component lemmas already
present in incoming work are credited; the integer improvement is their new
compatible composition. The natural proof explicitly repairs the potentially
lost Pell orientation after deleting an individual power row.

## Reproduce

From this directory, using Python 3.10 or later with only its standard library:

    python3 -B verify.py

This authenticates the complete release, copies it to independent temporary
directories and runs every listed stage in normal and optimized Python. It also
rejects changed bytes, missing files and unlisted files and verifies that all
sealed files remain unchanged. No search for a Diophantine zero or consistency
witness is performed. The retained integer arithmetic parent's finite checker
is replayed too. Imported formal dependencies are not recompiled.

    python3 -B verify.py --mode normal
    python3 -B verify.py --mode optimized

FINAL_REPLAY.json records the performed full release replay. The final ZIP was
also freshly extracted and replayed before delivery. An external delivery
receipt records that ZIP hash; it cannot be included self-referentially in the ZIP.

The selected literal equations are in integer/integer217,
integer/integer217_sparse, integer/integer218, integer/integer218_sparse,
natural/natural202, natural/natural202_lowheight, natural/natural203,
and natural/natural204. Readable residuals accompany their JSON. Intermediate
stages and inverse certificates are retained for reproduction, not advertised
as additional complexity records.

## Build the article

With a normal TeX Live installation and the packages listed in report/main.tex:

    sh build_report.sh

Recompilation may change PDF metadata/bytes. The delivered PDF was rendered and
every page was visually reviewed. Finite checkers authenticate the mathematical
artifacts, not arbitrary future PDF builds.

Original source notices and licenses remain with their components. No upstream
repository was modified. Reviews are separate checks within an AI-assisted
workflow, not outside human endorsements. No literature-wide priority is claimed.
