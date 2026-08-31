Cyclotomic q-Fabius--Rvachev Frontier Report
============================================

Contents
--------
- cyclotomic_q_fabius_frontier.tex : LaTeX manuscript
- cyclotomic_q_fabius_frontier.pdf : compiled PDF
- numerical_experiments.py        : deterministic high-precision experiments
- data/                            : CSV output and generated LaTeX table
- figures/                         : PDF and PNG figures
- corpus_audit_note.txt            : source-audit method and novelty boundary
- corpus_inventory_2026-08-27.txt : preserved recursive 57-TeX-path ledger
- requirements.txt                 : Python dependencies

Reproduce numerical results
---------------------------
From this directory, run:

    python numerical_experiments.py --dps 80

The script writes all CSV tables, summary text, and figures in place.  It uses
mpmath's arbitrary-precision arithmetic and Matplotlib.  No random sampling is
used.

Build the report
----------------
With a standard TeX installation:

    latexmk -pdf -interaction=nonstopmode cyclotomic_q_fabius_frontier.tex

or use pdflatex twice.  The source expects figures/ and data/ to remain beside
it.

Main proved results
-------------------
1. An explicit two-term radial root-of-unity expansion for the complex
   q-Fabius/Rvachev sinc product.
2. A spectral-dilogarithm action with an elementary sign classification.
3. A natural-boundary theorem for every fixed real 0<|z|<pi/2.
4. Cyclotomic blow-ups to exp(-A_omega w^(2d)), with all-order Bell corrections.
5. Condensation of zero power sums, cumulants, moments, and Appell polynomials.
6. Explicit inverse frequency and inverse-q branches.

Status
------
"New" in the manuscript means apparently new relative to the audited ProveIt
repository corpus, not a claim of worldwide priority.
