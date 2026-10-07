# Exact ratio-partition expansion code

This directory contains newly written, reproducible code for the expansion of

    F(q) = sum(k >= 1) q^(3k) / product(j = k..2k) (1 - q^j).

The coefficient a(n) counts partitions whose largest part is twice their
smallest part. Both extreme parts are mandatory, accounting for q^(3k).
There are no network reads, OEIS b-files, copied third-party programs, or
redistributed paper copies. The exact computation uses the Python standard
library only. Python 3.9 or newer is recommended.

## Commands (from the report directory)

    python -B code/exact.py --order 4
    python -B code/exact.py --order 8 --counts 400
    python -B code/selftest.py
    python -B -O code/selftest.py
    python -B code/build.py --out build-new --order 4 --max-n 10000

The build destination must be new or empty and outside `code/`. Existing files
are never overwritten: creation uses exclusive mode. Source files are not
modified. `-B` avoids incidental Python bytecode caches. Every output is
specified by its content; no timestamp, machine name, or absolute path enters
the generated tables. Repeating the build in two fresh directories produces
byte-identical exact outputs. `build.py` itself runs both selftests and refuses
to continue if normal and optimized results differ.

`exact.py --order J` accepts any nonnegative integer fixed order. It has no
hard-coded maximum order or fitted constants. Resource requirements grow with
J; this is finite formal algebra, not a convergence claim. `build.py` also
constructs general inverse polynomials, whose symbolic size can grow quickly.

## Exact algorithm and truncation

`Q5(a,b)` represents a+b sqrt(5) by two reduced `Fraction` coordinates. Only
integer and Fraction inputs are accepted. No decimal or floating-point
conversion occurs in the exact algorithms. Argument guards use explicit
exceptions and continue to operate under `python -O`.

Set phi=(1+sqrt(5))/2, rho=phi-1, a=3phi-4, and s=sqrt(t). Taylor series for
f'(x)=-z/(1-z), z=rho exp(-u), give derivatives at x0=log(phi); rho^2 gives
those at 2x0. In the exponent E(s,Y), include

    h^(m)(x0) Y^m s^(m-2)/m!,                     m >= 3,
    (log g)^(m)(x0) Y^m s^m/m!,                  m >= 1,
    e_(2r-1)^(m)(x0) Y^m s^(4r-2+m)/m!,          r >= 1, m >= 0.

Only terms whose **entire s-degree is at most 2J** are retained. Polynomial
powers of Y are not truncated. The exponential recurrence is

    B_0=1,  n B_n = sum(k=1..n) k E_k B_(n-k).

Finally c_j=E[B_(2j)(Y)] with E[Y^(2m)]=(2m-1)!! a^(-m) and odd moments zero.
The derivative and Bernoulli bounds cover every term needed at the requested
whole degree, including new Euler--Maclaurin corrections at higher orders.

## Independent checks

`oracle.py` calculates the same c1--c4 using two different components:
Eulerian-polynomial rational functions for all f derivatives, and the product
of factorial-series exponentials instead of the exponential recurrence.
Bernoulli numbers use a separate binomial-sum identity. It shares the exact
field and elementary polynomial arithmetic, so it is an algorithmic
cross-check rather than a separate arithmetic implementation.

The optimized count routine updates finite products by

    P_(k+1)=P_k(1-q^k)/((1-q^(2k+1))(1-q^(2k+2))).

It uses O(N^2) integer operations and O(N) storage. Selftests compare it with
independently rebuilt coin-change products through n=400 and directly
enumerate integer partitions through n=35. The n=0,1,2 convention is a(n)=0.
No global last exception for monotonicity or log-concavity is claimed.

`inverse.py` constructs P_j in the independent formal variables
w, alpha_1,...,alpha_J, with Fraction coefficients, and verifies the defining
logarithmic equation through the requested order. The inverse is continuous;
it does not eliminate the ceiling brackets required for integer thresholds.
The constants alpha_r=B^r [z^r]log(1+sum d_j z^j), B=2 sqrt(A), are defined by
the article and can be substituted into these universal polynomials.

## Generated files

- `exact_tables.json`: exact c_j, coefficient-transfer polynomials in sqrt(A),
  inverse polynomials, and selected exact integer counts (integers encoded as
  decimal strings to avoid JSON consumer precision loss)
- `radial_coefficients.tex`: TeX align environment for c_0,...,c_J
- `inverse_polynomials.tex`: TeX align environment for universal P_1,...,P_J;
  long higher-order equations may need editorial line breaking
- `exact_counts.tex`: exact count table
- `selftest.txt`: normal and optimized test results
- `SHA256SUMS.json`: hashes of the preceding deterministic exact artifacts

`A` is pi^2/30. A coefficient-transfer JSON term with key k represents the
Q(sqrt(5)) coefficient multiplying (sqrt(A))^k. Each inverse monomial records
powers in the order `[w, alpha_1, ..., alpha_J]`. Rational coefficients are
canonical Fraction strings. The manifest excludes itself and any optional
numerical diagnostics subsequently added.

## Optional high-precision diagnostics

Install mpmath separately if desired; it is not needed by the exact build.

    python -B code/numerical.py --max-n 10000 --dps 80 --radial --out diagnostics-new.json

The optional script recomputes exact integer counts and converts exact field
coefficients to mpmath only at the numerical boundary. It reports coefficient
residuals, finite radial-sum residuals, and implicit continuous inverse errors.
It refuses to overwrite an existing output file. The direct radial sum has
a reported finite cutoff. None of these numerical results certifies an error
bound, an asymptotic theorem, or a globally valid integer rounding rule.
