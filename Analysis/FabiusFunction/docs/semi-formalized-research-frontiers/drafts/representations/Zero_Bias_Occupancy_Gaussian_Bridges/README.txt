GAUSSIAN BRIDGES AND DISCRETE FRONTIERS IN ZERO-BIAS OCCUPANCY
Research package, 5 October 2026

Start with occupancy_article.pdf. The article proves the named geometric
occupancy-shape conjecture in the inspected ProveIt Fabius zero-bias report,
and develops sharp sequence-space, frontier, centering, and entropy results.

MAIN RESULTS

1. Full l1 Gaussian bridge convergence for geometric weights, with covariance
   (diag(c) - c c^T)/2 and an exact leading mean l1-error constant.
2. Universal l2 convergence with saddle centering; sum sqrt(c_j) < infinity
   is the necessary and sufficient condition for l1 tightness.
3. A sharp centering transition at exponent 2 for power-law weights.
4. Total-variation limits for the geometric frontier, maximum occupied index,
   and occupied count, with exact phase averages and bulk/frontier independence.
5. A full l1 large deviation principle with rate twice relative entropy,
   exponential concentration, and a strong law under any common coupling.

CONTENTS

occupancy_article.tex       Self-contained LaTeX source, bibliography included.
occupancy_article.pdf       Compiled article.
verify_occupancy.py         Deterministic exact and numerical companion.
requirements.txt           Minimum compatible numerical dependencies.
build.sh                   Three-pass LaTeX build.
numeric_notes.txt           Numerical results and their limitations.
data/                      Eight CSV/JSON records.
figures/                   Two figures in vector PDF and PNG preview formats.

REPRODUCE

Python:
  python -m pip install -r requirements.txt
  python verify_occupancy.py

The recorded environment is Python 3.12.14, NumPy 2.3.5, SciPy 1.17.0,
Matplotlib 3.10.8. Actual versions and checks are recorded in
data/verification_summary.json. Exact checks use fractions.Fraction.
No Monte Carlo or network data is used.

LaTeX:
  bash build.sh

Alternatively run pdflatex three times on occupancy_article.tex, keeping the
figures directory beside it. No BibTeX or repository-specific notation file
is required. Common TeX Live packages and Latin Modern fonts are used.

PROVENANCE AND STATUS

Repository: https://github.com/VladimirReshetnikov/ProveIt
Inspected commit: a21208b3ff14a07a4c8318dbf916d543acbef043
Source blob: 3e406ee42205a5ea223863c2bfbd4c0a8cece08a
Source conjecture label: conj:occupancy-shape
Source report: Zero_Bias_Towers_and_Spectral_Peeling.tex, in
Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/
representations/Fabius_Zero_Bias_Frontier_Report/

The article includes ordinary mathematical proofs and supplementary exact
and numerical checks. It is not a Lean formalization or a refereed paper.
Repository-relative contributions are identified; worldwide priority is
not asserted. No third-party source article is redistributed.

The full reference list, ten further research questions, formalization
sequence, and numerical error qualifications are in the article.
