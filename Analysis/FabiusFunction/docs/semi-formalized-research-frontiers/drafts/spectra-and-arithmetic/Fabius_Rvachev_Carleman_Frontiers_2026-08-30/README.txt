Critical Ultradifferentiable Geometry of the Fabius--Rvachev System
===================================================================

This archive accompanies the research report prepared on 30 August 2026 from the
public ProveIt Fabius-function documentation corpus.

Main files
----------

  fabius_carleman_frontiers.tex
      Complete LaTeX source of the report.

  fabius_carleman_frontiers.pdf
      Compiled 24-page PDF.

  frontier_experiments.py
      Deterministic, extensively commented Python program for the numerical
      experiments.  It requires no network access and does not import code or
      numerical tables from the repository.

  data/*.csv
      Long-precision tables for the discrete Carleman gauge, the Fourier peak ray,
      the Lambert-W saddle, and exact Bell-polynomial coefficients.

  figures/*.pdf and figures/*.png
      Retained vector sources and the raster figures used in the report.

  numerical_summary.txt
      Key constants and the scope of the exact Bell computation.

  CORPUS_AUDIT.txt
      Scope, method, and limitations of the repository novelty screen.

  SHA256SUMS.txt (retired)
      This package-local ledger was retired repository-wide on 2026-09-01;
      its final archive-payload snapshot remains recoverable from Git history.

Principal mathematical results
------------------------------

The report separates proved statements, proved syntheses with existing repository
theorems, computations, and conjectures.  Its principal additions are:

  * a quantitative interval-uniform law for the normalized high derivatives of
    the Fabius and Rvachev up-functions, in total variation;
  * exact local extrema, oscillation, L^p laws, and signed-moment laws;
  * the exact local Roumieu/Beurling Denjoy--Carleman classification for every
    comparison weight;
  * the exact Faà di Bruno transform M_n^circ = 2^n M_n for
    M_n = 2^{n(n+1)/2}/n!;
  * a critical-class synthesis for every positive forward and inverse iterate;
  * an exact discrete Legendre transform with its log-periodic lattice factor;
  * the exact algebraic Fourier gain log_2(2/sqrt(3)) beyond the derivative
    envelope;
  * a Lambert-W_{-1} saddle expansion for the standard associated function;
  * a base-b/q-deformed weight calculus and a numerically tested Bell-edge
    asymptotic conjecture.

Reproduce the numerical files
-----------------------------

Use Python 3.10 or later.  From this directory:

    python3 -m pip install -r requirements.txt
    python3 frontier_experiments.py --out-dir .

The default run computes all Bell-polynomial coefficients exactly through n=120.
To choose another cutoff:

    python3 frontier_experiments.py --out-dir . --bell-nmax 80

To regenerate CSV and text output without plots:

    python3 frontier_experiments.py --out-dir . --no-figures

The Bell recurrence uses arbitrary-precision Python integers and Fraction objects.
Floating-point conversion occurs only when tables are serialized or figures are
made.  The sinc product and Lambert-W calculations use 100 decimal digits.

Build the PDF
-------------

A TeX Live installation with Libertinus is required. From this directory, run
exactly three serial passes:

    pdflatex -interaction=nonstopmode -halt-on-error -file-line-error fabius_carleman_frontiers.tex
    pdflatex -interaction=nonstopmode -halt-on-error -file-line-error fabius_carleman_frontiers.tex
    pdflatex -interaction=nonstopmode -halt-on-error -file-line-error fabius_carleman_frontiers.tex

Verification notes
------------------

The synchronized 2026-08-31 rebuild has 24 A4 pages at rotation zero. Every
page rendered and contained extractable text. All 22 font rows are embedded
and subset, four are Libertinus, and none is Type 3. The report uses the
retained PNG companions for its plots. The final log has no TeX error,
unresolved reference/citation, rerun request, overfull box, or underfull box.

The novelty assessment is relative to the screened ProveIt corpus, not a claim of
absolute publication priority.  See CORPUS_AUDIT.txt and Section 1 of the report.
