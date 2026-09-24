# Coarse Classes Without Least Turing Representatives

Research report prepared for Vladimir Reshetnikov, 18 September 2026.

The main document is `coarse_jump_spectra.pdf` (17 pages). Its self-contained
LaTeX source is `coarse_jump_spectra.tex`.

## Mathematical result

The selected target is C1 in the supplied `turing_degrees_unified.tex`:
must every nonuniform coarse-equivalence class have a least Turing degree?

For the dyadic replication R_A(n) = A(v_2(n+1)), the report proves:

    Spec_T([R_A]_nc) = Spec_T([R_A]_uc) = {d : deg_T(A) <= d'}.

For every A, two coarse descriptions X_0, X_1 can be constructed below
A join 0' such that every total function computable from both is computable.
There is also a perfect family with this pairwise property. If A is not
computable from 0', all these descriptions are noncomputable, and the
coarse classes have no least Turing degree.

In particular A = 0'' gives the spectrum of all high degrees
{d : 0'' <= d'}. Section 9 gives an explicit degree-0' representative G
of that same coarse class.

For effective-dense reducibility the answer for the same dyadic target is
different:

    Spec_T([R_A]_ned) = Spec_T([R_A]_ued) = {d : deg_T(A) <= d}.

That spectrum has a least degree. This does NOT settle C2 in general.

## Status and attribution

The literal negative answer to C1 already follows from the classical
Jockusch--Schupp dyadic characterization and Theorem 4.3 of
Hirschfeldt--Jockusch--Kuyper--Schupp (2016), credited there to Igusa.
Section 11 explains the implication. This report does not claim a
historically new resolution of that question or priority for the stronger
pair/perfect-family formulation.

The full constructions and spectrum calculations are proved in English.
They have not been independently peer reviewed or checked in Lean or
another proof assistant. The non-effective construction explicitly uses
0' to decide c.e. splitting questions. No program in this archive computes
that oracle or purports to generate the actual infinite counterexample.

## Build

Requirements: a TeX distribution with pdfLaTeX and the standard packages
listed in the source. It uses Latin Modern, matching the supplied report's
font family and navy/ink palette. No font files are included.

With Make:

    make pdf

Or run this command three times (until cross-references stabilize):

    pdflatex -interaction=nonstopmode -halt-on-error coarse_jump_spectra.tex

The Makefile places intermediate files in `build/` and copies the final
PDF to the root. `make clean` removes build intermediates and Python caches,
not the report source or the final PDF.

## Finite checks

Requirements: Python 3.10 or newer. Only the Python standard library is used.

    make test

Or:

    cd code
    python -m unittest -v test_finite.py

All 12 tests passed in the recorded run. The checks include exact dyadic
counts, finite density bounds, sparse encoding, preservation of lock
conditions, all 6,561 pairs of partial Boolean truth tables on two oracle
bits and one input (611 no-split cases), and 400 additional fixed-seed
locked-table cases.

These are checks of finite arithmetic and finite analogues. They do not
certify the infinite existence theorem, decide unbounded no-splitting, or
replace the conventional proof.

## Contents

- `coarse_jump_spectra.tex` and `.pdf`: the article, with bibliography.
- `code/density_coding.py`: exact finite dyadic-coding operations.
- `code/finite_split.py`: complete splitting checks for explicitly finite tables.
- `code/test_finite.py`: reproducible finite tests.
- `verification/test_run.txt`: captured test output.
- `verification/proof_audit.md`: claim-by-claim proof obligations and boundaries.
- `verification/document_qa.txt`: compilation and visual-render checks.
- `sources.csv`: source locations, theorem references, and roles.
- `Makefile`: PDF build and test commands.

The user-supplied original report and third-party papers are cited but not
redistributed. The archive contains no font files and no external Python
dependencies.
