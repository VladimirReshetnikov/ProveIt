# Log-gamma result provenance

## Source checkpoint

The audited manuscript is pinned to ProveIt commit
afed07429d3d37eceb6c8e9e54cf4da2d3f39d53.
Chapter 7 still treats a named depth-two coordinate for the cubic
log-gamma moment as an open target.

## Published starting results

**David H. Bailey, David Borwein, and Jonathan M. Borwein.**
On Eulerian log-gamma integrals and Tornheim–Witten zeta functions.
The Ramanujan Journal 36 (2015), 43–68.
DOI: https://doi.org/10.1007/s11139-012-9427-1

Author preprint:
https://www.davidhbailey.com/dhbpapers/log-gamma.pdf

Theorem 6 evaluates the cubic moment in Tornheim derivatives.
Theorems 7–8 treat the fourth moment. The author preprint is dated
28 July 2012. The compact differential-operator form in this article
was derived independently and then checked against that known evaluation.
It is explicitly attributed as an equivalent representation.

**Tewodros Amdeberhan, Mark W. Coffey, Olivier Espinosa,
Christoph Koutschan, Dante V. Manna, and Victor H. Moll.**
Integrals of powers of loggamma.
Proceedings of the American Mathematical Society 139 (2011), 535–545.
DOI: https://doi.org/10.1090/S0002-9939-2010-10589-0

Author preprint:
https://www.math.tulane.edu/~vhm/papers_html/lg-subm.pdf

Section 8, Theorem 8.1 states the full fixed-order asymptotic moment
expansion and its first coefficients. The coefficients here agree with
that expansion. Its existence is a known result, not a new discovery
of this continuation.

## Quantitative continuation

The article develops a meromorphic generating-function and residue
description, a late-coefficient asymptotic determined by a reciprocal-gamma
critical point, the resulting divergence at every fixed moment, and
an explicit remainder bound for a growing number of retained terms.
The proofs use classical Lagrange inversion, positivity, and a local
Fourier argument.

The literature search verified the published starting results but did
not establish exhaustive priority over all inverse-gamma asymptotic
literature. Accordingly, the claim is a proved extension of the audited
manuscript, with the precise theorems supplied for review.

## Certificate and diagnostics

The cubic certificate uses integer fixed-point outward intervals.
SymPy supplies exact Bernoulli rational numbers; floating-point
special-function values are not trusted. The default order 360 and
130 fixed-point digits give width below 2.387e-113 and 112 common
decimal places. The JSON endpoints are exact decimal rationals.

An independent replay reproduced every certificate field exactly.
Separate mpmath quadratures at 150 and 180 decimal working digits
lie inside the rational enclosure. These quadratures are diagnostics;
the analytic remainder and outward arithmetic establish the enclosure.

The coefficient and growing-truncation formulas were independently
audited, including the first asymptotic correction, the interval split,
all constants in the remainder, and the sufficient integer cutoff n>=7.
The cross-review file records the issues found and their corrections.
