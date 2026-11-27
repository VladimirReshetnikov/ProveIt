CONDITIONAL SPECTRAL EXTREMES AND A FUNCTIONAL BRIDGE
Research deliverable - 27 November 2026

Start with spectral_extremes.pdf. The complete editable manuscript is
spectral_extremes.tex; its only external build inputs are figures/*.pdf
and standard LaTeX packages.

MAIN RESULTS

For any positive spectrum with a regularly varying count N(T) of index
alpha>0, independent Gamma(theta,1) weights and p>alpha, condition
X=sum G_j/gamma_j^p to be at most x, with x tending to zero.

1. The largest contributions, together with their spectral locations,
   have a marked Poisson limit. The relevant location scale is
   u/(log N(u))^(1/p), smaller than the bulk scale u. The p-th power of
   a normalized location has Gamma(alpha/p,1) law, independently of
   the gamma shape theta.

2. The entire exactly centered bulk profile converges to a Brownian
   bridge in D[0,1]. It is independent in the limit of both the extreme
   process and the unit-exponential distance from the constraint.

3. For completed Dirichlet L-functions, the winning location has a
   half-normal law at height u/sqrt(log u). All of the top fixed number
   of terms lie in a band carrying a vanishing fraction of total mass.

4. For exponential weights, a heat-trace equation gives an accurate
   center incorporating conductor dependence, with an analytic finite
   enclosure whenever a bound for the counting remainder is known.

The manuscript provides full proofs. The probability results themselves
are unconditional. Dirichlet GRH supplies the interpretation of the
Laplace transform as a reciprocal even completed L-function.

WHAT IS AND IS NOT CLAIMED

This is a new extension of the inspected ProveIt snapshot and the
identified literature, with a targeted rather than exhaustive priority
search. The Gumbel law alone is classical. No new Lean formalization is
claimed. Repeated ordinates are allowed, with one independent gamma
weight per occurrence. Aggregating all weights at a multiple zero before
taking the maximum defines a different statistic.

SOURCE SNAPSHOT

ProveIt commit 00cadb961bbe77c74e5d082c4948f8884d58a970.
Primary predecessor: Analysis/GeneralizedRiemannHypothesis/Article/sections/ana.tex.
Relevant labels: ana:thm:condlaw, ana:thm:block, ana:thm:macro,
ana:cor:fourfifths, ana:thm:medianheight.
The repository's upstream GRH revision is
72fead102f663d5c7a407964a13dc0cf9d977207.
Source blob identifiers are recorded in results/source_manifest.json.

CONTENTS

spectral_extremes.pdf, spectral_extremes.tex  - Complete manuscript.
code/verify_finite.py                       - Independent finite calculations.
code/experiments.py                         - Deterministic diagnostics and sampler.
code/make_figures.py                        - Rebuild all plots from saved data.
code/refined_center.py                      - Validate the heat-trace center.
results/finite_validation.json              - Six high-precision comparisons.
results/asymptotic_diagnostics.json         - All deterministic curves.
results/asymptotic_table.csv                - Compact numerical table.
results/refined_center_validation.json      - Sharper-center diagnostics.
results/refined_center_validation.csv       - Sharper-center table.
results/conditional_simulation.json         - Raw sampled observables.
results/source_manifest.json               - Pinned source identities.
results/pdf_validation.json                - Final document checks.
results/environment.json                   - Versions used for the computations.
figures/                                   - Vector PDF figures and PNG previews.
notes/literature_comparison.txt             - Scope of novelty assessment.
notes/proof_review.txt                      - Independent mathematical audit.
notes/formalization_plan.txt                - Suggested dependency order.
notes/source_audit.txt                      - What the source analysis established.
requirements.txt                           - Numerical Python dependencies.
Makefile                                   - Reproduction commands.
SHA256SUMS                                 - Integrity checks for archive members.

REPRODUCE

Install the Python packages in requirements.txt, then from this directory:

  python3 code/verify_finite.py --output results/finite_validation.json
  python3 code/experiments.py --samples 6000
  python3 code/refined_center.py
  python3 code/make_figures.py
  pdflatex -interaction=nonstopmode -halt-on-error spectral_extremes.tex
  pdflatex -interaction=nonstopmode -halt-on-error spectral_extremes.tex

Alternatively use a configured Tectonic installation to compile the TeX.
The source includes its bibliography directly; BibTeX is unnecessary.

VALIDATION INTERPRETATION

The finite checks compare inclusion-exclusion with independent numerical
Laplace inversion at 110 decimal working precision. They are numerical
consistency checks, not outward-rounded certificates. The asymptotic
experiments use synthetic ordinates obtained by inverting the leading
zero-counting function; they are explicitly not computed zeta zeros.
The rejection sampler is exact for its stated finite spectrum and
conditioning event, up to ordinary floating-point implementation.
Finite truncation and Monte Carlo uncertainty are not hidden.

The proofs, rather than these experiments, establish the infinite limits.

INTEGRITY

After extracting the archive, run:

  sha256sum -c SHA256SUMS

The checksums cover every deliverable file except SHA256SUMS itself.
