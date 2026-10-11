QUARTIC DIGAMMA--HARMONIC BRIDGE

Requirements: Python 3, SymPy 1.14.0, mpmath 1.3.0.
Run from any working directory by supplying the path to each script.

  python3 check_quartic_exact.py
  python3 check_quartic.py
  python3 check_quartic_mellin.py

Run the arithmetic/quadrature program before the Mellin program. The
Mellin program reads quartic_numeric_results.json beside itself to compare
its independent eta/beta evaluation against the direct digamma quadrature.
Result files are written beside the scripts and replace their included
records. Work in a copy to preserve the original package hashes.

The 15 exact checks cover the quartic principal parts, residue difference,
finite summation identity, asymptotic constant, integrated higher poles,
Laurent coefficient conversion, elimination of eta, and the normalized
primitive. They do not replace the analytic contour and convergence proofs.

The 80-digit numerical programs compare three routes:
  1. Direct quadrature after a convergent local digamma subtraction;
  2. An absolutely convergent arithmetic series with Bernoulli/Hurwitz tail;
  3. Mellin evaluations of eta and beta_1 inserted into the quartic identity.

At the final arithmetic truncation (N=80, asymptotic order 40), the first
two routes differ by less than 3.4e-62. The independent Mellin route
differs from quadrature by less than 2.1e-74. Finite Bernoulli asymptotics
and ordinary mpmath arithmetic are used; these are not interval enclosures.
