# Reviewer notes

This is an unrefereed manuscript with exact arithmetic supplements. The
statements of new results should be reviewed independently before a research
publication or an OEIS submission.

The critical arithmetic steps are the finite Gamma cancellation (3.1), the
residue-dependent valuation lemma, the identity expressing each shifted floor
function as a slice of the ordinary Landau function, and the denominator-prime
reduction. The latter is what permits composite denominators; the ordinary
floor criterion is never applied directly to fractional Gamma arguments.

For the two infinite denominator-clearing families, check that at sufficiently
large prime-power levels at most one factor is counted, and that its residue
lies on the correct side of an endpoint of the ordinary step function. The
explicit lcm constants cover all remaining levels. The separate primes dividing
k in the positive-shift family are treated explicitly.

The analytic dependency is Levelt's companion description of regular-singular
hypergeometric monodromy. The printed positive-definite Gram matrices prove
finiteness of the relevant integral matrix groups. The fractional Frobenius
series require the indicial root condition Q(r/d)=0; checking only the shifted
recurrence would omit its boundary term. Rational coefficients then permit
descent of algebraicity from C(x) to Q(x).

The exact checker confirms finite certificate identities but is not a formal
proof checker. The numerical demonstrations are not interval-certified.
All-order formulas are Poincare expansions with fixed-order remainder bounds;
no exponentially small sectors or resurgent completeness are claimed.

Remaining targets include supercongruences, minimal algebraic equations,
optimal clearing constants, and natural combinatorial interpretations.
