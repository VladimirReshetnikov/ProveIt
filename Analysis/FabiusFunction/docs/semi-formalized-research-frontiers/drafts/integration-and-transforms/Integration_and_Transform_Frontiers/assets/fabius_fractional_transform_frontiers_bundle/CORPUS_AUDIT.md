# Corpus audit and novelty boundary

## Immutable baseline

The audit was pinned to the following repository state:

- repository: `VladimirReshetnikov/ProveIt`;
- commit: `22f3939f162b8fe9481b4affcd6ea12e7f45e8fd`;
- subtree: `Analysis/FabiusFunction/docs`;
- subtree Git object: `abec59391ce853eca49c74bc65d0ab7206ab4101`;
- indexed TeX-source count at the snapshot: 84.

The default branch changed while the work was in progress.  Pinning prevents later additions from silently changing the report's novelty boundary.

## Audit method

Every `*.tex` path under the subtree was included in a recursive inventory and searched for terminology and formulas involving:

- antiderivatives, primitives, repeated integration, and moment recurrences;
- Fabius, inverse Fabius/quantiles, and Rvachev's up-function;
- Mellin, Laplace, Fourier, Stieltjes, Hilbert, beta, and related transforms;
- positive, negative, complex, integer, and fractional orders;
- Riemann-Liouville, Caputo, Weyl, Marchaud, Riesz, and fractional Laplacian conventions;
- autocorrelation, difference distributions, stop-loss transforms, and energy integrals;
- endpoint asymptotics, Lambert-W phases, Bell/Bernoulli polynomials, q-binomial formulas, and sinc products.

The current synthesis documents and novelty-critical frontier reports were read contiguously.  Imported literature, OCR-corrected papers, and superseded drafts were content-deduplicated by path, title, and mathematical substance, then consulted wherever the searches indicated overlap.  This is more reliable for novelty control than counting duplicated versions of the same article as independent sources.

## Most important overlap documents

The two broadest recent integral syntheses at the pinned snapshot were:

1. `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/Fabius_Integral_and_Transform_Frontiers/fabius_integrals_and_transforms_frontier_report.tex`
2. `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/fabius_integral_frontiers_bundle/fabius_integral_frontiers.tex`

The principal human-readable baseline was:

3. `Analysis/FabiusFunction/docs/Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.tex`

Additional overlap came from the monomial-antiderivative reports, dyadic primitive ladders, derivative-norm spectrum, inverse-beta and inverse-moment reports, Mellin/heat-kernel frontiers, Fourier-decay work, and autocorrelation notes.

## Material treated as already present

The report does not claim novelty for the following repository themes:

- ordinary and iterated primitives of \(F\), \(1-F\), and `up`;
- monomial, polynomial, complex-power, and selected negative-power weights;
- dyadic primitive reduction and exact moment recurrences;
- causal fractional integrals of `up` and Mellin/moment-tail formulas;
- integer layer-cake and beta-transform formulas for \(F^{-1}\);
- ordinary Cauchy/Stieltjes transforms and their basic dyadic equation;
- Fourier norms of derivatives, autocorrelation identities, and selected energy integrals;
- sharp endpoint asymptotics involving lower Lambert-W and a nonconstant log-periodic phase;
- Bell-polynomial and related inverse-function expansions already developed in the corpus.

Those results are summarized only when needed to fix notation or prove a genuinely different operator identity.

## Systems not found in the pinned corpus and developed here

Exact-term and formula-structure searches did not find the following systems in the pinned tree:

- an arbitrary-complex-order quantile-Volterra transmutation for Riemann-Liouville integrals of \(\phi\circ F^{-1}\), including entire continuation in a power parameter;
- a Caputo transmutation for \(F^{-1}\) at every noninteger order through the intrinsic operator \((F')^{-1}D_x\), together with the endpoint \(L^r\) frontier;
- a two-parameter complex-order generalized Stieltjes family with coupled dyadic/order recurrences, fractional spectral shifts, and a fractional boundary-jump inversion law;
- an exact Weyl order-lowering refinement identity for `up` and convergent exterior algebraic-tail series for Weyl and Riesz derivatives;
- an entire Gamma-normalized positive-part hierarchy for differences of Fabius variables, including negative-order density derivatives, triangular refinement, inverse-quantile double integrals, and fractional Fourier energy.

The report therefore concentrates on these systems and avoids spending pages rederiving the older polynomial primitive ladder.

## Scope of the novelty statement

The audit is strong evidence of non-duplication within the specified repository snapshot.  It is not a proof of global mathematical priority.  A limited external literature sanity check was performed for fractional quantile substitutions, generalized Stieltjes functions, and fractional derivatives of compactly supported refinable functions, but the mathematical literature is too large for an absolute priority claim.  The report deliberately labels its contributions as new relative to the audited repository and separates theorems from conditional statements and conjectures.
