RANDOM BITS, FINITE CATALOGS, AND ARBITRARY CUTS OF ARITHMETIC
Exact noise thresholds, Boolean universality, and the strength of induction

Research report prepared for Vladimir Reshetnikov with ChatGPT
5 October 2026

START HERE
==========
random_bits_arithmetic_cuts.pdf is the complete 37-page article.
random_bits_arithmetic_cuts.tex is its complete, single-file LaTeX source.
The two figure PDFs used by the source are included in figures/.
All bibliography entries are included in the TeX source; no .bib file is needed.

CONTENTS
========
- random_bits_arithmetic_cuts.pdf: final article, with linked contents,
  proofs, two figures, a ProveIt formalization plan, and fourteen questions.
- random_bits_arithmetic_cuts.tex: complete source.
- figures/: vector PDF figures and PNG copies.
- verify_finite_budgets.py: exact finite checks and figure/data generation.
- finite_budget_verification.json: counts, scope, error, runtime versions.
- FINITE_VERIFICATION_README.txt: details of the finite calculations.
- data/: the complete plotted data and a compact convergence table as CSV.
- SOURCE_AUDIT.txt: primary sources, repository snapshot, attribution scope.
- PROOF_MAP.txt: the principal results and their dependencies.
- SHA256SUMS.txt: checksums of every other deliverable in this archive.

BUILD THE ARTICLE
=================
Extract the archive, enter its random_bits_arithmetic_cuts directory, and run:

    latexmk -pdf -interaction=nonstopmode -halt-on-error random_bits_arithmetic_cuts.tex

Alternatively, run pdflatex on that file three times to settle the table
of contents and cross-references. Standard TeX Live packages suffice.
The source uses Latin Modern, AMS math/theorems, geometry, microtype,
booktabs, longtable, enumitem, fancyhdr, hyperref, bookmark, and xurl.
Keep the figures/ directory beside the TeX file.

The delivered build used pdfTeX 1.40.25 (TeX Live 2023/Debian).
All pages were rendered and visually inspected. The final log had no
undefined references, overfull boxes, or duplicate page destinations.

REPRODUCE THE FINITE CHECKS AND FIGURES
=====================================
With Python 3, NumPy, SciPy, and Matplotlib available, run:

    python verify_finite_budgets.py

The script writes the JSON report, four CSV tables, and both figures in
PDF and PNG form beside itself. It overwrites those reproducible outputs.
It does not require network access. The delivered run used Python 3.12.14,
NumPy 2.3.5, SciPy 1.17.0, and Matplotlib 3.10.8.

All 6,138 exact iid budget checks and 494 unequal-bias projection/extension
checks passed. There were 114 floating spot checks, with maximum absolute
error 3.3306690738754696e-16. The script also verified 10 exact extremizing
pairwise-independent distributions, 55 fair marginals, 660 pairwise joint
identities, 65 quadratic majorant inequalities, and 10 dual expectations.

MATHEMATICAL AND HISTORICAL STATUS
=================================
The infinite-model results are supported by the proofs in the article.
The finite calculations do not simulate a nonstandard model or verify
an infinite theorem. No Lean or Rocq formalization is included.
Independent reasoning passes and a separate skeptical consistency review
were used; these are an internal research audit, not external peer review.

The fair-coin standard-cut conclusion is credited to Elliot Glazer's
2023 MOPA announcement. Optimal finite source ranking, the normal
source-coding transition, and the sharp pairwise atom bound are classical.
The arbitrary-bias classification, arbitrary-cut and countable Boolean
realizations, and associated refinements are proposed contributions.
No established priority or solution of a named open problem is asserted.
See SOURCE_AUDIT.txt and the article for precise attribution and limitations.
