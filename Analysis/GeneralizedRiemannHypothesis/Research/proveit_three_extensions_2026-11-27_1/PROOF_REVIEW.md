# Proof review and status

This file records mathematical checks performed during preparation. The proofs were developed and cross-reviewed using separate reasoning passes and assistant agents; this is not external peer review or a Lean formal verification.

## Gram determinant theorem

The full proof is in papers/gram_determinants/gram_determinants.tex.

Checked points:

- The gcd of maximal minors equals the index of the generated column lattice, so normalization preserves both the objective and the zero pattern.
- A minimizing integral matrix can be taken to generate Z² and to have primitive nonzero columns.
- If k columns are zero, the exact identity is
  \(\sum m_v^2=n+2z(A)-2kn+k^2\).
  Since \(z=o(n^2)\), zero columns remove only \(o(n)\) columns.
- The squared truncated primitive-lattice potential has error \(O(R^5\log(2R))\) uniformly over all determinant-one lattices, including extremely thin ones.
- Cauchy–Schwarz and isotropization produce the factor \(4/729\) when the budget is \(Q=n+2z\), and \(1/729\) when written in terms of \(z\).
- At a maximizing aspect ratio, \(4\Phi=6\Psi+T\Psi'\) gives the matching parabolic construction.
- Rounding changes the quadratic budget by \(O(n+R^2)\); the chosen slack dominates that error in the stated range.
- The eight reserved directions preserve the exact column count and add exactly \(4M(M-1)+\sum x_j^2\) zero minors. The correction costs \(o(1)\) of the energy.

The theorem holds for every integer sequence with \(n=o(z)\), \(z=o(n^2)\). It proves eventual feasibility for the exact-z class. The maximizer is rigorously attained, but its numerical location and uniqueness are not certified.

## Positive-filter normal form

The full proof is in papers/positive_filters/positive_filters.tex.

Checked points:

- The strip identity applies to a finite positive exponential sum; finite convex-hull reduction preserves every prescribed derivative constraint and does not enlarge support.
- Equality in the sharp bound forces a lattice support and precisely the stated reflected target divisor.
- Coefficient remainders, rather than individually labeled roots, make the constraint map analytic through collisions.
- The confluent Jacobian is invertible. Conjugation and polynomial divisibility force each homogeneous node and weight variation to vanish.
- The persistent dual certificate is nonnegative on the entire support interval and has only the proposed nodes as zeros. It proves global minimality and uniqueness, not just stationary feasibility.
- Endpoint dominance excludes zeros outside a uniform rectangle; the argument principle rules out unaccounted strip zeros after perturbation.
- The exact deficit integral can be differentiated using exponential endpoint bounds.
- The quadratic form is an integrated variance and a positive graph energy. Hermite interpolation identifies the full normal space, including repeated roots.
- The two-mode quartic law and the boundary-stiffness constant have explicit derivations and numerical or exact checks.

Strict positivity of every base polynomial coefficient is essential. The theorem is local for fixed degree and has no effective uniform neighborhood radius. Its nondegenerate Hessian is in coefficient coordinates; individually labeled root coordinates are singular at collisions. Mixed-entry signs depend on the coordinate convention. The boundary asymptotic uses successive, not simultaneous uniform, limits.

## Finite-field detection

The full proof is in papers/bilinear_detection/bilinear_detection.tex.

Checked points:

- Inclusion-exclusion counts image subspaces with full coordinate support and containing the observed column space.
- Surjection counts and nonzero fiber counts give the exact finite law, including cases with more anchors than ambient dimension.
- The null preserves the exact one-entry marginal. For dimension one it can have zero probabilities; the finite count remains valid.
- Retaining dependent anchors is essential at fixed codimension. Their mass does not vanish and yields the rank-deficiency flag.
- On full row rank, the complete likelihood equals the independent-anchor component times its prior mass; the explicit null rank bound makes this sufficient asymptotically.
- The first transition uses the classical rectangular-nullity law, with its complete support condition.
- The later transition is a defective Poisson experiment. Its plateau, square-case formula, and corner derivative jumps follow from that likelihood.
- The uniform Gaussian proof uses an orthogonal density expansion, avoiding cancellation in an unstable Taylor expansion.
- An optimal exact test **may be chosen** using four statistics. Ancillary tie-breaking means it would be too strong to say every optimal test must do so.

The theorem covers the stated complete bipartite, independently sampled, nonzero-vector model over all finite fields. The executable enumeration checks only small prime fields. Other observation graphs and other sampling laws remain outside the theorem.

## Computational verification

- Exact symbolic filter interpolation and rational integration; twelve independent nonlinear moment solves at 80-digit precision.
- Nine full finite-field enumeration cases covering 440,836 latent assignments and 87,149 possible observed matrices, including impossible observations.
- A separately implemented conditional-count verifier covering 53,114,420 latent assignments by exact aggregation and checking all 818 possible matrices across six cases.
- Eighteen exact single-column chi-square checks.
- An exact rational lower certificate for \(\Psi(32/3)>1/\pi\).
- Exact weighted integer-matrix examples, including 47,765,579 indexed columns stored as directions and multiplicities.
- An exact four-square repair example with 18,048 columns and 1,140,772 zero minors, with two independent determinant calculations.

All proof statements stand independently of these finite or numerical checks. The consolidated verification run is recorded in verification/run_summary.json. The final PDFs were compiled with references resolved and checked visually.

## Scope

No result in this packet depends on the upstream RH or GRH claim. No prominent classical conjecture is asserted solved. The packet advances three concrete directions in the supplied research program with complete written proofs and reproducible artifacts. Historical novelty remains subject to a broader literature review.
