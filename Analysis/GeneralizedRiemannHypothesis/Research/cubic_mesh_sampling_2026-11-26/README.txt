CUBIC MESH BUDGETS FOR ONE-SIDED MELLIN CRITERIA
26 November 2026
Prepared for Vladimir Reshetnikov

START HERE
==========
report.pdf is the complete research note. report.tex is its complete editable
LaTeX source. All figures needed for compilation are included.

MAIN RESULT
===========
For E(x)=C(x)-a*x*log(x)-c*x, where C is convex and a>0, sampled one-sided
bounds E(x_j)<=C_epsilon*x_j^(theta+epsilon) imply convergence of the
positive-part Mellin transform for Re(s)>theta if the cumulative gap budget

  H_theta(X)=sum_{x_j<=X} (x_{j+1}-x_j)^3 / x_j^(theta+2)

is O_epsilon(X^epsilon) for every epsilon>0, with 0<=theta<1.

The report proves the exact integrated interpolation cost, a global
extremizing nonnegative weight construction, an explicit fourth-power mesh
with growing missing blocks and infinitely many gaps ~4*X^(5/6), and
applications to zeta and the inspected repository's Dirichlet GRH criterion.
At theta=1/2, that deleted mesh has H_theta(X)=O(log X).

NOVELTY AND PROOF STATUS
=======================
The new result is the sharp integrated sampling/refinement theorem and its
explicit missing-sample application. Fourth-power sampling, convexity,
Landau's analytic principle, and the classical local h^3/12 quadrature
error are credited as existing ingredients. No identical combined theorem
was found in the targeted literature check, but priority is not established.
No additional named open conjecture is claimed solved.

The mathematical proofs are human-readable analytic proofs in the report.
Code checks are supplementary finite verification, not proofs of RH/GRH or
of the infinite sampling theorem. The upstream Lean project was inspected
but not rebuilt. The new theorem has not been formalized in Lean.
formalization/outline.txt is a design outline, not a completed proof.

CONTENTS
========
report.pdf                         Complete research note
report.tex                         Full LaTeX source
build.sh                           Standard TeX Live rebuild commands
code/verify.py                     Deterministic supplementary checks
code/requirements.txt              Python dependencies
code/verification_results.json     Check outcomes and precisions
code/gap_table.csv                 Exact block sizes and numerical limits
figures/*.pdf, figures/*.png        Reproducible mathematical figures
formalization/outline.txt          Explicitly uncompiled Lean architecture
provenance/repository_review.txt   Scope and source-inspection record
provenance/upstream_source_manifest.json
                                   Pinned source URLs and blob identifiers
provenance/literature_search.txt   Search scope and novelty boundaries
SHA256SUMS.txt                     Integrity hashes for the package files

REPRODUCE
=========
From the extracted directory:

  python3 -m pip install -r code/requirements.txt
  python3 code/verify.py
  bash build.sh

The Python script regenerates the JSON, CSV and figures. A normal TeX Live
installation with standard mathematics and font packages builds the PDF.
No internet access is needed after dependencies are installed.

The calculations include symbolic identities, four 100-digit quadrature
comparisons, a global nonnegative ramp extremizer, exact integer block
identities, and finite mesh calculations. The report provides the rigorous
infinite estimates separately.

SOURCE BASELINE
===============
https://github.com/lsernau/grh-lean
Revision: 72fead102f663d5c7a407964a13dc0cf9d977207
https://en.wikipedia.org/wiki/Riemann_hypothesis
Sources accessed 26 November 2026. Detailed bibliography is in report.pdf.

No large upstream source files are redistributed. The manifest records
where the inspected declarations can be obtained from their original source.
