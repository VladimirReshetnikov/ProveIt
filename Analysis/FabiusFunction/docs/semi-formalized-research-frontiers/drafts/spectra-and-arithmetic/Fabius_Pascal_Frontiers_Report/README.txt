FABIUS--PASCAL FRONTIER REPORT
==============================

Title
-----
Automatic Spectra, Exact Dyadic Cubature, and Probabilistic Duals in the
Pascal--Rvachev Hierarchy

Prepared: 30 August 2026

Contents
--------
Fabius_Pascal_Frontiers.tex
    Complete LaTeX source of the 27-page report.

Fabius_Pascal_Frontiers.pdf
    Compiled A4 PDF with embedded fonts, hyperlinks, bibliography, theorem
    numbering, and a 62-item PDF outline.

frontier_experiments.py
    Deterministic, extensively commented Python program supporting the exact
    symbolic and high-precision numerical checks reported in the article.

numerical_output/numerical_results.txt
    Human-readable record of the experiment run.

numerical_output/*.csv
    Machine-readable tables for the gamma limit law, radial Lambert-series
    growth, moment ultra-log-concavity, and the critical Poisson limit.

Scope and novelty convention
----------------------------
The report audits the principal current consolidated LaTeX volumes under
Analysis/FabiusFunction/docs in Vladimir Reshetnikov's ProveIt repository and
uses the repository manifest to track historical drafts stated there to have
been absorbed into those volumes. Direct repository cloning was unavailable
in the execution sandbox, so public GitHub tree and raw-file endpoints were
used for enumeration and reading.

Every label "new" in the report means "not located in this audited repository
state." It is deliberately not an unconditional claim of worldwide first
publication. Results already present in the repository--including the
canonical product, integer zero multiplicities, zero jets, rank-one
nonholonomicity, rank-one Laguerre--Polya/PF structure, spectral zeta formulas,
and existing inverse-Fabius/Lambert-W asymptotics--are treated as inputs or
baselines rather than as new results.

Principal developed results
---------------------------
1. Hypertranscendence and unit-circle natural boundaries for every higher-rank
   spectral-sign Mahler function, resolving a natural-boundary subproblem
   explicitly listed in the repository.
2. A new order-(r+1) Mahler equation, hypertranscendence, natural boundary,
   and non-D-finiteness for the hierarchy of valuation-multiplicity Lambert
   series, together with a bivariate master series.
3. A sharp all-rank dyadic-comb cubature theorem, Appell reconstruction, and
   finite Legendre/Bernoulli reproduction formulas.
4. All-rank Laguerre--Polya and PF-infinity consequences for Wick-rotated
   spectral determinants, including ultra-log-concavity and rank convolution.
5. An infinite Poisson-binomial interpretation of normalized determinants,
   exact moment probabilities, a branching law, and a multi-scale Poisson,
   mod-Poisson, and Gaussian phase diagram.
6. A generalized-gamma-convolution dual with an explicit Thorin measure,
   branching identity, concentration estimates, and a rank central limit
   theorem with exact standardized-cumulant decay.
7. A separated conjecture register and concrete analytical, computational,
   arithmetic, asymptotic, and formalization research programs.

Rebuilding the PDF
------------------
A recent TeX Live distribution is sufficient. From this directory, run:

    pdflatex Fabius_Pascal_Frontiers.tex
    pdflatex Fabius_Pascal_Frontiers.tex

The source uses standard packages including geometry, libertinus (with a
Latin Modern fallback), microtype, amsmath, amsthm, mathtools, booktabs,
longtable, tabularx, hyperref, cleveref, and listings.

Reproducing the numerical checks
--------------------------------
Requirements:

    Python 3.10 or later
    mpmath
    sympy

Run:

    python frontier_experiments.py --output-dir numerical_output --dps 80

The program exits with an exception if an exact identity or internal
consistency test fails. Its outputs are deterministic; the archived files were
regenerated in a clean temporary directory and matched byte-for-byte.

Validation performed
--------------------
- The LaTeX source was rebuilt from a clean auxiliary state.
- The final log contains no undefined citations/references, overfull boxes,
  missing glyphs, or fatal errors.
- The final PDF has 27 A4 pages, embedded fonts, no encryption, and a complete
  hyperlink/outline structure.
- All 27 pages were rendered to PNG and visually inspected for clipping,
  overlap, broken glyphs, and malformed tables.
- The Python file passes bytecode compilation and a clean rerun reproduces all
  archived numerical tables exactly.
