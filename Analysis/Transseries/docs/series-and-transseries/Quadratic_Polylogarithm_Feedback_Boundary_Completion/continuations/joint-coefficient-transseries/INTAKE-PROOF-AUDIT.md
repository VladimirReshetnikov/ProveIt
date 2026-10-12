# Joint coefficients and reciprocal inverse endpoints: proof audit

12 October 2026. This records conventional mathematical review of sections
2--7 and their canonical synthesis. It supplements the earlier OVERVIEW,
whose scope was intake reconciliation and finite replay. The delivered
article, PDF, verification code and original outputs remain unchanged.
The collective manuscript author is ProveIt Contributors.

## Exact representation and moving-order scale

Lagrange inversion gives the normalized coefficient as a compound-Poisson
probability divided by n, for all positive b. The endpoint reference radius
must not be identified with the actual fold radius when b<A. Positivity
and the uniform linear coefficient give the required intensity bounds.

Gamma recurrence pairs the two colliding poles before any limit is taken.
The regular part has K_0(H)=H+3/2, and the square-root Taylor expansion adds
A^2/b^2 to the quadratic coefficient. The uniform O(t^(5/2)) local remainder
follows from D=At+O(t^(3/2)). The scalar equation has exactly one B>1
eventually: its derivative has at most one sign change and its initial
value is negative. The two-variable implicit chart is convergent; that
claim is separate from the fixed-order asymptotic coefficient expansion.

## Every fixed logarithmic order

The parabolic-cylinder normalization was checked against the differential
equation and initial values in DLMF 12.2.4--12.2.7. The Fourier definition
fixes the principal logarithm and both signs. Spatial differentiation raises
the kernel order, and central values reduce to reciprocal Gamma.

The whole Fourier contour is controlled. Retaining positive intensities
up to n^(1/4) gives a Gaussian bound in the growing central region;
retaining the first intensity gives exp(-c sqrt(n)) outside it. A finite
central expansion on a sqrt(log log(n)) window has an integrable remainder.
The unit-cube formula for the divided exponential supplies the Stirling
coefficients and controls y near zero without assuming epsilon log|y|
uniformly small. Each truncation order is fixed, and all parameter sets
are compact. These facts establish the stated absolute lattice-uniform
theorem and answer parent question Q1 in precisely that scope.

The untruncated approximate exponential can grow at infinity and is not
used as a global characteristic function. No convergence of the infinite
logarithmic expansion is accepted or needed. At epsilon=0 the constants
are exactly the existing Gamma-moment polynomials evaluated at -log(2);
this is a normalization reconciliation, not a separate first derivation.

## Positive tails and nonlinear composition

The positive analytic composition theorem keeps a common endpoint disk,
uniform bound and positive linear coefficient. It depends only on the
first two endpoint derivatives within the logarithmic sector. The
regularized convolution proof of the kernel tail was checked, including
its integrations by parts, Gaussian moments and reciprocal-Gamma zeros.
Order derivatives follow from a uniform complex-order neighborhood.

Choosing a sufficiently high fixed expansion order makes the absolute
error smaller than q/xi^3 throughout each positive window xi<=log(n)^M.
This proves the stated relative Gaussian-plus-power matching. The lower
Lambert branch gives the larger crossing root, and the finite transition
profile follows after squaring the standardized coordinate. Lattice
rounding is smaller than that transition scale. The b-to-coordinate
derivative is positive on the selected local branch. Parent Q2 is thereby
resolved on these positive windows, with negative growing windows and
macroscopic deviations still open. The primary Lam--Blanchet--Burch--Bazant
and Berger--Birkner--Yuan papers retain credit for the broader heavy-tail
correction and Gaussian/one-large-jump context.

## Reciprocal orders

The ramification classification agrees with the earlier
summation-singularities continuation and is credited to both proof routes.
For alpha=p/q<1 the leading inverse power forces ramification p; for
alpha>1 the first nonanalytic term forces q. Irrational powers and integer
logarithms exclude finite ramification. The explicit inverse coefficients
at alpha=1/m follow from ordinary analytic Lagrange inversion.

The moving-order chart factors off b_m^(-m) exp(m^2 tau) and has nonzero
implicit derivative 1/m. Its variables 1/log(1/y), y^(m-1) and y^m are
independent for the convergence assertion. Fixed-deficit order jets and
fixed-value order jets differ because the endpoint itself moves.
The upper-bank modulus obstruction for 1<s<3/2 has the claimed negative
coefficient. It limits a proposed real-order extension, does not refute
the printed integer theorem, and does not determine the global inverse
Taylor radius after a local endpoint becomes removable.

## New matched-derivative theorem

The canonical synthesis adds a theorem addressing part of research
question R3. If two positive analytic outer functions agree in endpoint
derivatives 1 through r-1, their normalized coefficient-law difference has
first scale n/B^r and exactly the r-th spatial derivatives of the same
finite logarithmic correction functions. Different endpoint values are
normalized separately; equality of those values is not required.

The proof uses the exact exponential difference integrated along convex
combinations of the two positive models. This preserves the common scale
and supplies a weighted Gaussian majorant after division by n/B^r. It is
essential: simply subtracting the two old absolute remainders would lose
the smaller sector. Endpoint Taylor expansion identifies the amplitude
(-1)^r A^r delta_r/r!, and the finite Fourier calculus supplies every fixed
logarithmic order within that first difference.

At the critical center, the cubic Gaussian term vanishes. The exact order
derivative H_5^[1](0)=-4 gives the first nonzero normalized coefficient
difference -A^3 delta_3 q/(3 B^4), of order n^(-2) log(n)^(-3).
The positive cubic family in the manuscript matches the lower derivatives
exactly and tests the sign independently with finite coefficient sums.
This is a comparison theorem, not a complete single-model multi-sector
transseries, and its truncation and matching orders remain fixed.

## Evidence boundaries and publication location

The prior isolated replay in intake-verification remains the full replay
of the three unmodified supplied programs. Its exact residuals and finite
case counts are now included in the canonical receipt checks. The new
independent check_matched_endpoint_identities.py uses finite symbolic
expansion, four corruption controls and separate Fourier quadrature.
check_matched_endpoint_coefficients.py uses positive recurrences at 65
digits, with selected cases independently repeated at 85 digits. The
coefficient errors are observations; they are not monotonically improving
in every case and are not certified remainder bounds.

Canonical theory and complete proofs are in Volume I, Sections 1.11--1.12,
chapters/01-joint-coefficients.tex. The four PDFs and combined edition share
that source. Current build, visual-review and evidence receipts belong to
the collective manuscript's verification directory; no Lean or remote-CI
claim is made by this audit.
