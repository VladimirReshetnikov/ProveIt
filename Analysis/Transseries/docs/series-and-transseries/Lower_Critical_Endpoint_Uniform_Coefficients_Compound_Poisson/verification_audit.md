# Verification and proof-status audit

## Exact finite checks

`verify.py` recorded 385 passing rational assertions. These compare a direct
feedback recursion with the Lagrange coefficient formula, finite-partition
weights with exponential coefficients, Poisson removal identities, and action
cutoff identities. Three finite rational action families are used, including a
signed finite perturbation whose resulting action weights are nonnegative.
These assertions were rerun successfully during the final packaging audit.

## Numerical checks

The independent 80-decimal-digit recurrence at n = 100, epsilon = 0.05 agreed
with the log-space double-precision recurrence to a relative difference of
approximately 2.19e-15. Twelve numerical Hankel-moment integral identities
were checked at 55-digit precision; their absolute differences were all below
1e-38. These are high-precision numerical checks, not exact symbolic proofs.

The full recorded JSON includes leading and corrected coefficients through
n = 2048 for two prefixes, Landau cutoff diagnostics through n = 8192, and
finite compound-Poisson comparisons. The article's coefficient and cutoff
tables were generated directly from that JSON. The Landau diagnostics are
not uniformly close at the sampled parameters; the article displays these
differences and does not claim a finite-parameter error bound for them.

## Mathematical dependency audit

The coefficient proof uses the explicit generating function exp(n*A), not an
unproved global analytic continuation of the inverse. Subtracting its constant
part on the outer coefficient contour retains the epsilon factor in the
exponential error, including when epsilon is arbitrarily tiny.

The total-variation deletion proof depends on the relative coefficient
estimate and an exact Poisson density identity. It does not import a
fixed-distribution conditioning theorem into an unchecked triangular limit.

The continuous cutoff theorem requires n*epsilon -> infinity. The separate
compound-Poisson theorem covers bounded n*epsilon. The simplified matching
expansion has its additional epsilon*log(n)^2 -> 0 hypothesis stated explicitly;
the exact-core Landau result does not require that hypothesis.

The finite prefix is fixed and admissible. Arbitrary slowly varying tails,
growing prefixes, quantitative total-variation bounds, interval-certified
budgets, and noncritical coupling windows remain outside the proved scope.

All fixed-order coefficient expansions are asserted as asymptotic expansions;
only the critical Hahn chart is asserted to converge. The proofs do not
establish an all-order Borel or resurgence statement.

## PDF audit

The final article was rebuilt with latexmk and pdflatex. It has 20 A4 pages,
no undefined references or citations, and no overfull boxes. Every page was
rendered and reviewed in contact sheets; the main deletion theorem and the
coefficient table were additionally inspected at full rendering size. A text
bounding-box check found no words outside the page safety boundary. All
embedded fonts reported by pdffonts are Type 1; there are no Type 3 fonts.

## What is not certified

No new Lean, Coq, or other proof-assistant verification was performed. The
numerical computations do not use directed rounding. The mathematical
manuscript has not undergone independent peer review, and the source search
was not an exhaustive proof of global publication priority.
