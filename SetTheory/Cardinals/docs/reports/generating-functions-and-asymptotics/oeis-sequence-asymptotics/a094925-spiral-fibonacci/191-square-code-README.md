# Mathematical code and exact verification

All mandatory modules use the Python standard library. Every mathematical
check uses explicit exceptions rather than removable `assert` statements.

- `spiral.py` implements t(n) and the prescribed recurrence. Indices are exact
  Python integers in 0..1000000, excluding booleans; a(0)=0 and a(1)=1 are
  prescribed. The two-term recurrence begins at n=2. `t(0)=t(1)=0` are only
  bookkeeping. `values(last)` returns indices 0 through `last` inclusively
- `check_geometry.py` independently generates the path with directions
  east, north, west, south and run lengths 1,1,2,2,... . Neighbor selection
  uses occupied coordinates and exact squared Euclidean distances, without
  using the proposed predecessor formula. Finding an eligible point at
  squared distance 1 or 2 is required, and ties are rejected. No lattice
  distance lies strictly between those shells. Full brute force examines
  every earlier point except the predecessor through index 4096. The default
  full check reaches index 250000, including 999 corners and 127 complete
  early pre-corner occupancy rectangles
- `inverse_series.py` computes the analytic inverse-germ coefficients by a
  triangular logarithmic recurrence using `Fraction`. `derive(order)` accepts
  exact integer orders 1..40. Let Q=(1+u delta)^2-u(1+u delta)+u^2. The module
  verifies delta+log(Q)=0, exp(delta)Q=1, and R Q^2=(1+u delta)^2 at the requested
  finite order
- `independent_series.py` imports no main-series code. It derives delta from
  exp(delta)Q=1 using sparse polynomial products and finite factorial sums,
  then obtains R by rational polynomial long division. Agreement through
  order 12 and at every lower truncation is mandatory. This independence
  concerns the computational derivation; both implement the same identities
- `check_exact.py` checks those identities, all 64 OEIS terms, full geometry,
  996 corner identities, 25 exact rational transport-cancellation samples,
  and malformed-domain/fixture rejection. Normal and optimized runs emit
  canonical byte-identical JSON. Finite rational samples are not a substitute
  for the article's symbolic cancellation or analytic estimates
- `diagnose_mpmath.py` is separate optional code. It imports mpmath only inside
  its `run` function. It uses high-precision noninterval arithmetic for
  normalization and residual samples and certifies no numerical digits

Low-level polynomial primitives are implementation details; the supported
entry points are the validated `derive(order)` functions. Geometry's
`run_checks(listed, limit, brute_limit)` accepts a 64-term nonnegative integer
fixture, 63<=limit<=1000000 and 8<=brute_limit<=limit. The mandatory checker
has no reduced-coverage switch and always runs the stated full scope.

From the package root:

    python3 -I -S -B code/check_exact.py
    python3 -I -S -B -O code/check_exact.py

For optional diagnostics in an environment where mpmath is already available:

    python3 -B code/diagnose_mpmath.py --max-n 10000 --precision 80

Do not use `-S` for that optional command, because it intentionally needs a
third-party package. Allowed diagnostic bounds are 100..1000000 for `max-n`
and 30..200 for working decimal precision. Printed digits express working
precision, not certified accuracy. Mandatory code neither imports this module
nor runs its commands; floating results never enter release decisions.

There is no exact amplitude certificate in this package. The existence and
positivity of C, uniform remainder, analytic germ, and inverse conclusions
are proved in Report191, rather than inferred from these finite checks.
