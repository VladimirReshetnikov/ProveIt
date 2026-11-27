ARITHMETIC HIDDEN IN SMALL JUMPS
Research package prepared for Vladimir Reshetnikov, 27 November 2026

START HERE

papers/pathwise_rigidity.pdf is the main research paper. It proves an explicit
almost-sure decoder for primitive Dirichlet characters, up to conjugation,
from any positive interval of the zero-angle Levy process already constructed
in the supplied article. It gives exact leading variances, a multivariate
Gaussian limit with independent prime coordinates, a path-law dichotomy,
finite-band Hellinger bounds, and the contrast with equivalent finite-grid laws.

papers/sharp_extremal_results.pdf is a companion paper. It solves the article's
unrestricted optimal-network problem for coupled polynomial zeros, for both
worst and mean displacement, and the total-rank part of its fixed-parameter
orbit-span problem. Both companion results are unconditional.

All LaTeX sources and the figure needed to rebuild the papers are in papers/.
The mathematical arguments are complete ordinary proofs. No new theorem in
this package is claimed to have been formalized or compiled in Lean.

SOURCE PIN AND NOVELTY

ProveIt: 3d8689ceae76501a5c50f67da37e85369aac4fb6.
Vendored grh-lean upstream: 72fead102f663d5c7a407964a13dc0cf9d977207.

The main proof uses the Dirichlet GRH supplied by that source. It does not
assume simplicity, linear independence, pair correlation, or unshared zeros.
The source's construction of the Levy process and universal density expansion
are credited as existing results. The new contribution is its arithmetic
pathwise observability and quantitative statistical theory.

The companion identifies the exact questions it resolves, including the
unrestricted-support and complex-Hilbert-space qualifications. Standard matrix
optimization, effective-rank inequalities and Fourier frames are credited as
classical ingredients. The exact statements are absent from the inspected
article. Focused literature searches found related tools and constructions,
but cannot establish worldwide priority. See provenance/novelty_review.txt.

REBUILD

With a normal LaTeX installation containing the standard packages used in the
sources, run from the package root:

  python3 code/build_papers.py

Or, from papers/, run pdflatex twice on pathwise_rigidity.tex and twice on
sharp_extremal_results.tex. Bibliographies are included in the TeX files.
The companion inputs network_optima.tex and exact_rank_section.tex.

REPRODUCE THE CHECKS

Python dependencies: numpy, scipy, sympy, mpmath, matplotlib.

  python3 code/verify_decoder.py
  python3 code/verify_network_optima.py --output checks/network_checks.json
  python3 code/verify_rank.py

code/prime_decoder.py implements the finite jump-band estimator, its exact
finite-model moments, and Poisson simulations. The included example uses the
first 150 positive zeta zeros, computed with mpmath at 30 decimal digits.
code/generate_zeta_fixture.py regenerates that data. These zeros are numerical
approximations, not interval-certified enclosures. The illustrative plot and
simulation check the finite implementation; they are not evidence substituting
for the infinite theorems. The proofs do not depend on numerical zero data.

The network checks include an exact symbolic three-vertex example and numerical
matrix/edge-integral checks. The rank thresholds use exact rational arithmetic;
explicit Fourier constructions are checked numerically. Full results are in
checks/. SHA256SUMS.txt records the archive's included files (except itself).

OBSERVATION MODEL

The path decoder observes exact jump amplitudes down to arbitrarily small
scales. The finite-band result observes finitely many jumps at exact amplitudes.
It does not claim finite-time-grid identification or arbitrary-noise tolerance.
Continuous perturbations and finitely many changed jumps are covered by a
proved corollary. The article's all-order equal-conductor density comparison
concerns rescaled small-time transition densities, not equality of those laws.

PROVENANCE AND AUDIT

provenance/source_audit.txt records the endpoint statements and reusable proof
mechanisms in the vendored development. All 21 fetched article sections and
15 reviewed Lean/metadata files were matched against their Git blob hashes.
Their hashes and the source tree are recorded in provenance/. These manifests
identify the upstream files; the full upstream development is not bundled here.
The source audit was not a local full build. Sutherland's independently
published machine-check results for the same upstream commit are linked in
the audit and the main paper, separately from this package's own checks.

Nothing was pushed to the repository as part of preparing this archive.
