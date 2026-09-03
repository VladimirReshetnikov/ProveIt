Reciprocal-Integer Convolution Divisors of the Rvachev Law
===========================================================

Files
-----
Fabius_Rvachev_Reciprocal_Integer_Convolution_Divisors.tex   Complete LaTeX source.
Fabius_Rvachev_Reciprocal_Integer_Convolution_Divisors.pdf   Compiled report.
experiments.py                                               Reproducible exact/numerical experiments.
figures/                                                     Figures included in the report.
data/                                                        CSV and text outputs from the experiments.

Reproduce numerical outputs
---------------------------
From this directory, run:

    python experiments.py --output-dir .

Requirements: Python 3.10+, NumPy, Matplotlib, and mpmath.
The script performs exact integer checks before terminating successfully.
All CSV writers use an explicit LF line terminator.

Repository provenance and replay boundary
-----------------------------------------
The package was filed from the rootless archive
fabius_rvachev_frontier_report_2026-08-30-B.zip (outer SHA-256
cfae82f303c3740bd76673fed772b1f69b9fedb0a911505360c930db7cc5a13f).
This package-local normalization is anchored to merge parents
563b90f25e0563cc521a53e9b478b667eaf3b694 and
685e1963897b1ff2cff8f541e46218cf8d37405a.  Those hashes identify the
repository boundary; they are not a numerical run record.

No experiment was executed as part of this source-only normalization.  The
group README at ../README.md records an earlier temp-isolated Python 3.12
replay: four CSVs were byte-identical, the text summary was EOL-equivalent,
and endpoint_profiles.csv differed in 66 last-place fields, with maximum
absolute difference 1.1102230246251565e-16.  All four PNGs exhibited layout
drift between the unpinned packaged Matplotlib 3.10.8 and replayed 3.11.1
(1475 versus 1476 pixels wide).  The package has no dependency lock, so the
plots are reproducible scientific diagnostics but are not promised to be
byte-identical across Matplotlib versions.

Compile the report
------------------
From this directory, run exactly three direct passes:

    pdflatex -interaction=nonstopmode -halt-on-error Fabius_Rvachev_Reciprocal_Integer_Convolution_Divisors.tex
    pdflatex -interaction=nonstopmode -halt-on-error Fabius_Rvachev_Reciprocal_Integer_Convolution_Divisors.tex
    pdflatex -interaction=nonstopmode -halt-on-error Fabius_Rvachev_Reciprocal_Integer_Convolution_Divisors.tex

The source uses the repository's canonical A4/27 mm/Libertinus wrapper and
embeds the PNG figures from figures/.  After rebuilding, verify the page size,
font embedding, absence of Type 3 fonts and unresolved references, then inspect
rendered pages before removing LaTeX sidecar files.

The normalized artifact was rebuilt with those exact three passes on
2026-08-31 from the then-current 2,307-line, 89,887-byte source (SHA-256
ce215d9b809b7ea6f45e7529ef8afbb442c01e74c83236d0995c6b6c27892088).
The retained PDF is 991,587 bytes (SHA-256
06efd995e03514ac4a3c733a35b3e0fd56c72c9226925e9946f1f5ac7552d9ae) and
has 35 A4 pages.  All 25 font entries are embedded and subset, six are
Libertinus, and none is Type 3.  The final log has no overfull box, underfull
box, TeX error, unresolved reference/citation, or rerun request.  All pages
rendered and contained extractable text, and all LaTeX sidecars were removed.

The current live TeX remains 2,307 lines but is now 90,871 bytes with SHA-256
e6e3d6df88efc3e50f7180b3853fdc6e4c9072f4e56192655bb76e195b282c4e.
It names the law family explicitly as
`\ReciprocalIntegerLaw{M}` (printing `\mathsf R_M^{\mathrm{law}}`) so its
subscript cannot be mistaken for a two-adic valuation.  No PDF was rebuilt
after this notation-only edit: the ledger records the current source and the
retained validated PDF as distinct byte payloads, not a synchronized pair.

Research status
---------------
Results labeled theorem/proposition/lemma/corollary are proved in the report.
Conjectures are explicitly labeled.  "New" means not found in the audited repository
snapshot or limited literature search; it is not a claim of mathematical priority.

Exact Lean adjacency and boundary
---------------------------------
GeneralizedZeroDivisor.lean proves the arithmetic zero set and exact nonzero-
integer orders for generalized Rvachev products, including declarations
Fabius.generalizedRvachevProduct_eq_zero_iff_int and
Fabius.analyticOrderAt_generalizedRvachevProduct_int.
ReciprocalIntegerGammaZeros.lean proves the reciprocal-integer-base zero set
for the geometric reciprocal Gamma function through
Fabius.geometricReciprocalGamma_inv_natCast_eq_zero_iff.

These are adjacent exact zero-divisor infrastructures.  They do not formalize
the report's quotient family, its characteristic-function extension, divisor
classification, quotient multiplicities, or spectral zeta formula.  Those
claims remain manuscript-level results pending a dedicated Lean development.
