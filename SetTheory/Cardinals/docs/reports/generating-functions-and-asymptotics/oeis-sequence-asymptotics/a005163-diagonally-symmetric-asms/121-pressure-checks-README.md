# Exact finite verification companion for report121

Run from anywhere with Python 3.10 or later, standard library only:

    python /path/to/checks/verify.py
    python -O /path/to/checks/verify.py
    python /path/to/checks/mutation_tests.py

The verifier writes deterministic JSON to stdout. Exit 0 is PASS, 1 is an
intentional FAIL with a diagnostic, and 2 is an unexpected ERROR. Validation
uses explicit `need`/`require` guards, never removable `assert` statements.
Run outputs belong outside this closed directory. No network, external package,
report120 file, pre-existing cache, or floating-point root finder is used.
Do not run py_compile in this directory: unlisted files/directories are rejected.

## Mathematical scope and independent routes

1. The original bivariate skew kernel is expanded directly on a 14 by 14 grid.
   Its coefficients are compared with a separately implemented binomial sum for
   the original Pfaffian. The parameter-dependent Pfaffian is expanded by
   recursive perfect-matchings over exact polynomial coefficients for n=0..13.
   There is no determinant, division or interpolation in that Pfaffian route.
2. For D_n at t=3, n=1..12, Bareiss determinants of the original shifted kernel
   are differentiated by multilinearity (one replaced column at a time).
   Values and derivatives are compared with adjacent independently expanded
   Pfaffians, and with the rational calibration-matrix trace formula. The
   bounded A and singular G trace decomposition is also checked exactly.
3. Radical-free simultaneous similarity is used for C, J, L. With
   D_i=sqrt(Gamma(i+a+1)/i!), use V=D C D^-1, Lhat=D L D^-1,
   Jhat=D J D^-1. Then

       V_ij=(a+j+1)_i/i!
       Lhat_ij=(a+j+1)_(i-j)/(i-j)!  (i>=j)
       Uhat_ij=binom(j,i)             (j>=i)
       Jhat_(k,k-1)=(k+a)f(k), Jhat_(k-1,k)=k f(k).

   Factorization, triangular inversion, commutation, conjugation, involution,
   reciprocal pairing and tr((I+V)^-1)=n/2 are checked for n=1..8 at
   a=-1/2,0,1/2,1,2,3,4; a=2 is extended through n=12. Separately, sparse
   polynomial arithmetic in four independent variables certifies the
   denominator-cleared commutator and conjugation identities identically.
   The exceptional zero denominator at i=j=a=0 is not numerically divided by.
4. Direct enumeration of original symmetric {-1,0,1} ASM matrices for n=0..6
   retains every diagonal mask. It checks that a occupied first corner is +1,
   the rest of its row and column vanish, and the full coefficient polynomial
   after corner deletion equals the size-(n-1) joint polynomial. Enumerated
   univariate polynomials are compared with the independent Pfaffian route.
5. The real polynomials q_n, n=0..13, are built from those Pfaffians. Exact
   rational Sturm chains prove finite real-rootedness; gcd cancellation and
   disjoint root isolation certify alternating reduced root labels. Restoring
   the common real-rooted gcd preserves weak interlacing, with multiplicities.
   Positive controls include x^3-x versus x^2 and x^3 versus x^2. Negative
   controls reject nonreal roots, wrong ordering and unmatched multiplicity.
6. For every positive t=s^2 at each checked size n=1..13, the rational
   numerators of 1+(M_n-M_(n-1)) and 1-(M_n-M_(n-1)) have nonnegative exact
   coefficients and positive denominator. Thus the finite mean bound is
   checked for all positive fugacities, not just sampled points. The adjacent
   identity and individual calibration bracket are checked for n=1..12.
7. Rosengren's b=3 even-minus and plus products are compared with direct
   determinants through n=16, including zero odd minus determinants. The exact
   successive even ratio is checked. Bernoulli-polynomial arithmetic yields
   the log-ratio coefficients -3/4, 3/4, -961/1152. Leading cancellations and
   gamma normalization are verified exactly, squaring positive gamma constants
   to avoid radicals. This does not itself certify an analytic remainder.
8. Integral substitution uses y=sin(phi)^2, u^2=(1+3y)/4. Exact squared
   Jacobian, symbol and region identities give 3y(1+y)/((1+3y)(1+2y)); all
   square roots are positive on the open integration interval. Partial
   fractions give 1/2-2/(1+3y)+(3/2)/(1+2y). The substitution z=tan(phi)
   reduces each elementary integral to integral_0^infinity
   dz/(1+(1+c)z^2)=pi/(2sqrt(1+c)), by the arctangent endpoints. The final
   value is (sqrt(3)-1)/4, with a rational square-certified enclosure.
9. pressure.py checks the pole-cleared determinant and the ordered M=N B
   factorization at n=1..8 and t=13/4,10/3,7/2,15/4, directly against the
   original kernel determinant ratio. Sparse closed walks are compared with
   matrix-word multiplication for 12 words at n=4,8,12; their formal limiting
   symbol integrals are computed by Laurent expansion and exact polynomial
   integration. These are not numerical tests of convergence. The local
   Jacobi profiles are certified algebraically for every offset -6..6.
10. Pressure integral differentiation, resolvent partial fractions, pressure
   special values/derivatives, mean/variance and cumulants through order four
   are checked by formal rational algebra. The root-density substitution
   lambda=y^2, normalization (finite mass 1/2), Stieltjes-transform partial
   fractions and compactified resolvent identity are verified independently.
   Exceptional t=1,4 values of partial fractions are removable and use
   continuity. Analytic-limit, continuation, root-measure and CLT conclusions
   require the separately audited proof; computations do not establish them.
11. Compact supplementary algebra checks the LDP saddle discriminant and
   stationary equation, rational cancellations in the endpoint rates, and the
   exact quadratic threshold root with 27 positive-branch rational examples.
   The elementary logarithmic endpoint limits and two-ceiling integer inverse
   theorem belong to the proof; no real-valued o(1) inverse is asserted.

Finite checks do not prove trace limits, stability or all-size interlacing.
The exact polynomial identities are all-parameter algebraic certificates; their
analytic uses remain part of the proof. The pressure, linear free-energy and statistical limits require the analytic
proof; no full asymptotic equivalent, logarithmic power or amplitude is proved
by these computations.

## Closed fixtures, integrity and negative controls

fixtures.json has an exact schema: version, report, fixed ranges, provenance,
small Z polynomials, minus determinants, calibration derivatives, Stirling
coefficients, integral and explicit limitations.
All fixture values are independently recomputed by the verifier. JSON duplicate
keys, noncanonical rationals, Boolean-as-integer versions, unknown fields and
weakened ranges are rejected. The fixtures are reference outputs, not a proof.

inventory.json records byte counts and SHA-256 hashes of every other file here;
verify.py pins the exact set of filenames. The outer package must hash this
manifest too. This detects accidental corruption, not malicious coordinated
rewriting of the verifier and its manifest or supply-chain authenticity.

mutation_tests.py makes temporary copies outside this directory and tests the
unaltered complete verifier in normal and -O modes. It then corrupts inventory,
fixture schemas, mathematical coefficients, corner deletion and root inputs;
semantic mutations are deliberately resealed to ensure they reach mathematical
or schema guards. Every expected failure must have exit 1, status FAIL and the
specific intended diagnostic; a crash or generic ERROR does not count as a
successful negative test. Shared-root and multiplicity examples are explicit.

### Precisely tested mutation coverage

The campaign has 41 mutation/control definitions, each run normally and under
-O (82 expected failures), plus the two complete positive baseline runs. It
covers selected inventory/hash/schema errors; a changed derivative fixture;
the original kernel, determinant differentiation, rational factorization and
commutator/reciprocal trace, arbitrary-parameter conjugation, Toeplitz/singular
trace coefficients, corner deletion, both determinant products and their ratio,
Stirling coefficients, integral decomposition, real-root/interlacing/domain
failures, pressure resolvent/mean/density/transform algebra, finite ordered
factorization and pole clearing, mixed path sums and symbol/profile
coefficients, the LDP saddle, and threshold quadratic algebra. This is selected
path coverage, not exhaustive mutation of every fixture leaf or source line.
