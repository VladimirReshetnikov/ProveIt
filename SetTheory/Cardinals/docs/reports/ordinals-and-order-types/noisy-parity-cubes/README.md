NOISY PARITY ON FINITE AND INFINITE CUBES
========================================
Exact coloring, inspection budgets, asymptotic laws, and measurable choice
Prepared for Vladimir Reshetnikov, 5 October 2026

READ FIRST
----------
noisy_parity.pdf is the complete research article.
noisy_parity.tex contains the complete LaTeX text, proofs, and bibliography.
The source uses three included vector figure PDFs and needs no bibliography
database, external section files, network access, or shell escape.

THE PROBLEM
-----------
Let X be finitely or countably many independent fair bits. Draw a coordinate J
with ordered positive probabilities p_i, independently add Bernoulli(eta) noise
to every bit, and obtain Y by flipping coordinate J and applying the noise.
Choose one measurable Boolean rule f to maximize P[f(X) != f(Y)].
The same rule and the same random seed, if used, apply to both inputs.

MAIN RESULTS
------------
* For 0 < eta < 1/2 the optimum is
      max_k [1 + (1-2*eta)^k * (2*P_k-1)]/2,
  where P_k=p_1+...+p_k. A finite prefix parity attains it, including on the
  countably infinite cube. The maximizing degree is unique or has one adjacent
  tie, and a first sign change gives an exact stopping criterion.
* The exact expected-inspection frontier joins the prefix-parity scores up to
  the first optimum and stays constant thereafter. A shared mixture of two
  adjacent parities attains every intervening budget.
* A general spectral simulation replaces every measurable Boolean rule by
  randomized finite parities, simultaneously preserving its response to every
  independent XOR perturbation. Its mean query cost is the rule's total
  influence, at most that of any exact adaptive decision tree.
* At zero noise the infinite measurable value is 1 but is unattained. Every
  near-perfect sequence converges weakly to zero and has no Boolean limit in
  measure. Choice-based infinite parity attains pointwise perfection.
* Summable heterogeneous noise gives a compact optimization over all subsets
  of N. Measurable attainment occurs exactly when a finite maximizing subset
  exists. In ZFC an arbitrary label with a measurable success event attains
  the same optimal value. Full infinite parity is optimal exactly when
  eta_i <= p_i for every i.
* General random finitely supported perturbations obey an analogous compact
  optimization theorem.
* Uniform finite weights have a saturation transition at eta*n=1. Geometric
  weights have a logarithmically periodic second term. Regularly varying and
  exact Zipf weights have power-law, second-order, and integer-lattice laws.
* The article proposes twelve further research directions and a staged
  formalization plan connected to the inspected ProveIt snapshot.

STATUS AND ATTRIBUTION
---------------------
The article is an AI-assisted mathematical development with full written
proofs and independent internal audits. Its Fourier, spectral-sample, parity,
and measurable-coloring foundations are classical and cited. Historical
priority for the designed problem and its extensions has NOT been established.
This is not a refereed publication, a certified solution of a named open
problem, or a Lean/Rocq formalization. Numerical checks supplement proofs.
The article does not claim endorsement by Elliot Glazer.

Repository context is pinned to ProveIt commit
b71545625fedc631edc2ead542abbfba72eb6063. No repository changes were made.

CONTENTS
--------
noisy_parity.pdf                  Full typeset article
noisy_parity.tex                  Complete LaTeX source
figures/inspection_frontier.pdf   Exact budget illustration
figures/uniform_transition.pdf    Finite-size saturation transition
figures/geometric_correction.pdf  Integer steps and periodic correction
code/verify_parity.py             Exhaustive exact finite verification
code/check_asymptotics.py         Fixed 18-case, 65-digit Decimal diagnostics
code/create_figures.py            Figure generation and exact example checks
data/verification.json           Recorded exact exhaustive results
data/asymptotics_check.txt        Recorded high-precision diagnostics
data/examples.json               Exact examples and rational product bounds
README.txt                       This file
build.sh                         Rebuild the article with latexmk

BUILD THE PDF
-------------
From the package directory:
    bash build.sh
or:
    latexmk -pdf -interaction=nonstopmode -halt-on-error noisy_parity.tex

Requirements: a current standard LaTeX installation including mathpazo,
amsmath, amssymb, amsthm, mathtools, geometry, microtype, booktabs, longtable,
array, enumitem, graphicx, xcolor, fancyhdr, xurl, needspace, placeins, and
hyperref, plus latexmk.
The included figures mean Python is not needed to build the article.

REPRODUCE THE CHECKS
--------------------
    python3 code/verify_parity.py --output data/verification_rerun.json
    python3 code/check_asymptotics.py
    python3 code/create_figures.py

The first two programs use only the Python standard library.
The figure/example program also requires numpy and matplotlib.

The exhaustive run checks all 65,812 Boolean truth tables in dimensions
1, 2, 3, and 4 under eight rational parameter choices per dimension:
526,496 rule/parameter pairs. It independently computes transition scores,
Walsh scores, the optimum over all rules, influences, minimum exact adaptive
decision-tree costs, and the expected-budget bound. Mathematical quantities
are integers or fractions.Fraction. Runtime metadata can vary between runs.

The asymptotic diagnostics use 65-digit Decimal arithmetic and
Euler--Maclaurin tail evaluation. They are high-precision comparisons, not
interval certificates. The fixed grid is alpha in {1.3,1.5,2,2.5,3,5}
and eta in {10^-5,10^-8,10^-11}.

The example script verifies the five-bit nonlinear optimizer exactly and
encloses the summable-noise infinite product using exact rational partial
products and a geometric tail bound. Decimal interval endpoints are rounded
outward.

The plots are deterministic illustrations of proved formulas; they are not
independent numerical evidence for those formulas.
