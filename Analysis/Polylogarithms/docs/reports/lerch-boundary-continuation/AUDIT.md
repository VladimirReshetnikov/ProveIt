# Audit and claim-status notes

## Inspection scope

The mathematical audit was focused on `chapters/09-zero-geometry.tex` and the matching research questions in `chapters/10-discovery.tex`, at commit `6ec0b2c11ba3932107aa1e8bdf20627e3ced86fc`. This is not an audit of every theorem in the complete consolidated manuscript.

The manuscript already integrates the exact S4 proof, Gaussian reductions, and other continuations. This report does not relabel those as new results and does not resolve S6.

## Corrections and sharpenings

**No false proved theorem was established in the inspected zero chapter.** The correction is to the possible overextension of a research suggestion. A decreasing first large-k offset does not imply decreasing motion at every finite k. The index-two first-order lower branch is a rigorous counterexample: it decreases, attains one nondegenerate minimum, then increases. The alternating endpoint-direction theorem gives the general mechanism.

**A uniform remainder cannot be differentiated without derivative estimates.** The article proves mixed parameter/scale estimates for the gamma-concentration remainder. These justify the eventual negative-derivative theorem. It does not infer derivatives from the original uniform O(k^-1) location error alone.

**Continuity at rho=1 is not analyticity.** The universal eta^k times a polynomial in log(eta) term proves the sharp C^(k-1), not C^k, boundary regularity. This caveat also applies to simple endpoint zero branches. Finite deformation-jet identities are asserted at the endpoint only below the divergent order.

**Uniform low-index saturation needs its own proof.** Endpoint certificates alone do not prove saturation across rho. The complete n=2 theorem adds a one-crossing power-series argument. For k=1 and n=3 or 4, the weak-deformation theorem proves that saturation fails for sufficiently small positive rho.

## Proof dependency map

1. Existing master identity, spectral representation, Appell–Laplace representation, global multiplicity bound, and persistence are restated and attributed.
2. Exact endpoint signs plus the new power-series crossing argument give the complete n=2 count and unique minimum. The location enclosure adds an exact geometric-tail computation.
3. The classical convergent Lerch expansion, after symbolic cancellation of its paired pole, gives the all-index Abel identity. This yields the endpoint regularity and alternating directions.
4. Mixed-derivative concentration estimates plus simple Appell roots give eventual negative derivatives for any fixed finite order R.
5. An elementary polynomial root structure, a nonzero perturbation coefficient, holomorphic implicit functions, and compact confinement give the all-index small-rho classification.
6. That classification, exact n=3 endpoint signs, a single-crossing parameter curve, and the global zero bound give the unique inner-gap fold.

The all-index nonvanishing proof uses Hermite–Lindemann: log(2) is transcendental, whereas the relevant polynomial is rational and nonzero. The 120 supplied individual sign certificates establish those instances without relying on transcendence in the computation.

## Unresolved and explicitly limited claims

- The n=3 theorem locates a unique fold in a **specified inner gap**, not a unique fold in the whole positive a-axis. Excluding additional temporary outer pairs below that parameter remains conjectural.
- The fold's displayed decimal location is not an interval certificate. Existence, uniqueness within the gap, and nondegeneracy are proved independently of those decimals.
- Only the interval `(0.91560506,0.91560508)` is certified for the index-two minimum parameter; additional displayed digits are diagnostics.
- Large-k derivative thresholds are existential, with n and derivative order fixed. No optimized explicit K(n,R), no all-orders assertion at one finite k, and no uniform growing-n theorem are claimed.
- Exact polynomial checks and rational certificates do not formally verify the analytic lemmas or the Python interpreter.
- No transcendence or numerical independence of new polylogarithmic constants is asserted.
- Literature priority is not established. Classical identities are not presented as new discoveries.

## Numerical safeguards

Numerical root solvers retain a sign bracket, check that the result stays inside it, and verify the expected crossing direction and ordering. This avoids the common failure in which an unconstrained secant solver converges to a different branch. Residuals and diagnostic locations remain explicitly non-interval even after these safeguards.
