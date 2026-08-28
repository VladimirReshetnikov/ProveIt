FABIUS--RVACHEV FRONTIER REPORT
===============================

Title
-----
Midpoint Transmutation, Dyadic Cardinal Reproduction, and Holonomic
Obstructions: New deductions around the Fabius function, its inverse,
Rvachev's up-function, Thue--Morse cancellation, Lambert-W asymptotics,
and q-scale algebra.

Repository scope
----------------
The report audits the recursive LaTeX corpus under

  Analysis/FabiusFunction/docs

in Vladimir Reshetnikov's ProveIt repository, using the main-branch snapshot
of 27 August 2026.  The exact 57-file inventory and the non-duplication search
protocol are recorded in corpus_manifest.txt and reproduced in the report.

Novelty convention
------------------
"New" means not found in that audited repository snapshot.  It is not a claim
of global historical priority.  Established repository results are separated
from corpus-relative deductions and from conjectural/open directions.

Archive contents
----------------
  fabius_frontier_report.tex          Complete LaTeX source.
  fabius_frontier_report.pdf          Compiled, visually inspected 26-page PDF.
  frontier_experiments.py             Fully commented symbolic/numerical code.
  corpus_manifest.txt                 Recursive 57-source audit ledger.
  results/numerical_results.txt       Human-readable verification ledger.
  results/inverse_defect.csv          Inverse-midpoint experiment data.
  results/reproduction_errors.csv     Cardinal-reproduction residuals.
  figures/*.pdf, figures/*.png        Vector and raster report figures.
  requirements.txt                    Python dependencies.
  SHA256SUMS.txt                      Checksums for all payload files.

Reproduce the numerical work
----------------------------
Use Python 3.11 or later.  From this directory:

  python -m pip install -r requirements.txt
  python frontier_experiments.py

The script writes results/ and figures/.  It uses no network access.
The default run uses 70 decimal digits, 420 half-integer Fourier modes, and
240 sinc-product factors per Fourier coefficient.  These parameters are
centralized in the Settings dataclass near the top of the script.

Build the report
----------------
A recent TeX Live installation with latexmk is recommended:

  latexmk -pdf -interaction=nonstopmode -halt-on-error fabius_frontier_report.tex

The source uses Libertinus when available and falls back to Latin Modern.

Main proved deductions
----------------------
1. Exact midpoint--endpoint transmutation and an all-orders flat inverse
   midpoint defect, with coefficientwise transfer of the endpoint lower-
   Lambert expansion.
2. A dyadic Strang--Fix/cardinal reproduction ladder for dilates of the
   up-function, reciprocal-moment Appell correctors, Bernoulli--Bell formulas,
   and exact q-binomial closure at q=1/4.
3. Independent physical-space and Fourier-space obstructions to D-finiteness,
   with consequences for moment and Appell coefficient sequences.

Verification status
-------------------
The LaTeX source compiles without unresolved references or citations.  The PDF
was rendered page by page at 200 dpi and inspected for clipping, overlap,
broken glyphs, and figure placement.  The included Python script was rerun in
this environment before packaging.
