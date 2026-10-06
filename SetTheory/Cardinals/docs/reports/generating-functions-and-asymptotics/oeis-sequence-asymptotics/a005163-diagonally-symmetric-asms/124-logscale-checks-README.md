# Exact finite companion for report124

Python 3.10 or later, standard library only. From any working directory:

    python /path/to/checks/verify.py
    python -O /path/to/checks/verify.py
    python /path/to/checks/negative_tests.py

Each command writes deterministic JSON to stdout. Exit 0 means PASS; exit 1 is
an intentional FAIL with the specific diagnostic; exit 2 means an unexpected
ERROR. Checks use explicit guards, never removable assert statements. There is
no network, numerical tolerance, floating-point root decision, external package,
pre-existing cache, or runtime dependency on an earlier report. Both programs
suppress bytecode writes. Keep output outside this closed directory.

## Scope and independent routes

1. The original DSASM skew generating function is multiplied as a truncated
   bivariate formal series on a 12-by-12 grid. A separate binomial-sum entry and
   a recursive perfect-matching Pfaffian produce the fugacity polynomials.
   These are compared with exact Gaussian-elimination shifted determinants for
   n=1..10 and t=0,1,3/2,3,5 (50 adjacent identities). The Pfaffian route uses no
   determinant, interpolation, or division. Seven small Z polynomials and ten
   calibration derivatives are recomputed against inherited report121 values.
2. At t=3 the shifted determinant is compared with the Pascal determinant and
   the ordinary ASM factorial product. Column multilinearity, adjacent
   polynomial differentiation, and the inverse/trace derivative formula give
   three independent finite routes. Adjacent mean calibration and the finite
   individual mean bracket are checked. The four Bernoulli-B2 coefficients
   13/36, 1/12, -1/24, -13/24 sum to -5/36; halving gives -5/72. This is exact
   coefficient algebra, not a certificate for the analytic Stirling remainder.
3. Continuous-Hahn monic recurrence polynomials through degree 12 are compared
   against a directly constructed terminating hypergeometric polynomial and the
   residue-free step-3i difference operator. The Fourier differential operator
   L=(1-t^2)d/dt/2-(t+1/6) acts on monomials independently. Its images agree
   with (-i)^k(k+1)! times the standard Jacobi polynomial for (4/3,2/3), with
   the complex phases factored out exactly. Leading coefficients, all 91
   Jacobi beta-integral orthogonality/norm pairs, and Hahn/Jacobi norm ratios
   are rational identities. The Fourier-gauge change of measure and original
   mass 2 are checked algebraically using the stated beta/gamma identities.
4. The continuous-Hahn finite cubic is checked at n=1..10, in the rationally
   rescaled monic basis. Actual degree-lowering action is converted into finite
   matrices. The related trigonometric defect is retained: only its last
   column can be nonzero, and its last diagonal is 3n(n-2), including -3 at
   n=1. Nothing is silently replaced by an infinite section.
5. The Jacobi contiguous relation is verified as a polynomial equality at
   n=1..16 for four fixed parameter pairs: (4/3,2/3), (2/3,4/3), (7/3,2/3),
   (5/3,4/3), giving 64 cases. Independently canceled gamma products reconstruct
   both squared normalized coefficients. Sparse polynomial algebra in alpha,
   beta verifies that the first gamma-ratio coefficient equals
   alpha(alpha+beta+1), exactly canceling the shifted-frequency coefficient.
   The integrable variance diagonal exponent is -2/3. Its coefficient identity
   does not by itself establish a uniform Jacobi kernel bound.
6. Rational Householder frames of ambient/rank sizes (5,2), (6,3), (8,4) produce
   three genuinely noncommuting compressed pairs A,B. Exact checks retain the
   coordinate projection in tr(AB)=||X P Y*||_HS^2 (the finite column-restricted
   X,Y already contain P). The overlap is strictly positive even though the
   uncompressed supports are orthogonal. Nine mixed log-determinant Hessians
   are evaluated by column multilinearity and independently by resolvents.
   Ordered noncommuting determinant and resolvent factorizations are checked.
   Separate rational tilted projections check orthogonality and the exact
   variance factorization; positive diagonal factors stand for commuting
   exponential factors, without numerical exponentials. Relative determinant
   algebra and symmetric-resolvent/skew-error trace cancellation are checked
   at delta=-2,0,3/2. These are finite model identities, not discretizations or
   empirical tests of the DSASM Hardy operators.
7. Sparse Laurent-polynomial arithmetic proves the exact inverse-center
   quadratic cancellation, then performs the substitution r=sqrt(y/alpha),
   log r=(log y-log alpha)/2. It recovers the logarithmic inverse coefficient
   5/(288 sqrt(alpha)). Twenty-seven rational substitutions provide additional
   algebra controls. Logs in this part are formal independent symbols: no
   asymptotic remainder, ceiling bound, or effective threshold is computed.

## Sources and historical provenance

The DSASM input is Behrend, Fischer and Koutschan, *Diagonally symmetric
alternating sign matrices*, arXiv:2309.08446v3, especially equation (4.11):
https://arxiv.org/html/2309.08446v3
The calibration determinant uses Krattenthaler, *Advanced Determinant Calculus*,
Theorem 34, equation (3.24), and the ASM product:
https://www.mat.univie.ac.at/~kratt/akkomb/detsurv.pdf
The classical polynomial context is Rosengren, arXiv:1204.3424, section 3:
https://arxiv.org/pdf/1204.3424
Standard normalizations and analytic input are DLMF 18.3, 18.9.6, 18.22.14,
5.12.1 and 5.11(iii). The specialized Fourier/Hardy reductions are derived in
the present report and are not attributed verbatim to those classical sources.

fixtures.json records an exact extraction from the delivered report121
checks/fixtures.json: small_z at n=0..6 and ell_at_3 at n=1..10. Its original
byte count (3470), SHA-256, original report label and date are pinned. The
inherited reference values are independently recomputed by fresh code here.
No earlier implementation is copied or required at runtime. In particular,
report121's limited asymptotic scope is not retroactively expanded by reuse.

## Closed inventory and adversarial checks

inventory.json lists SHA-256 and byte count for the other five files. verify.py
pins the exact six-file directory inventory and rejects unknown files,
directories, symlinks, malformed/duplicate JSON keys, weak ranges, noncanonical
rationals, Boolean-as-integer metadata and provenance changes. The enclosing
package must hash inventory.json too. This is accidental-corruption detection,
not protection against coordinated replacement of a verifier and its manifest.

negative_tests.py makes temporary clean copies outside this directory. It runs
the complete unaltered verifier normally and under -O, requiring identical
positive JSON. It then runs every selected mutation in both modes. Mathematical
and schema mutations are deliberately resealed so they reach the intended guard.
Every negative control must exit 1, report FAIL, and produce its exact expected
diagnostic. A crash, ERROR, incidental integrity failure, or different failure
is not accepted. Every run is compared byte-for-byte before and after, and the
original closed directory must remain byte-identical through the campaign.
The output reports the exact case and failure counts. Coverage is selected,
not exhaustive over every source line or fixture leaf.

## Analytic limits

No finite computation certifies any analytic all-size O(1) bound. Endpoint
Jacobi/Bessel estimates, weighted Hardy Hilbert-Schmidt bounds, trace-class
comparisons, strong convergence, nonzero Fredholm limits and the analytic
Stirling remainder belong to the report's proofs. This companion does not
prove an amplitude, residual convergence, parity matching, an effective inverse
threshold, or a real-valued o(1) approximation to an integer-valued inverse.
