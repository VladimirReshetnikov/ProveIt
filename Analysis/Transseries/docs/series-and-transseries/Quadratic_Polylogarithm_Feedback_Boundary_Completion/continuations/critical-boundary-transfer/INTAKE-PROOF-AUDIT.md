# Quadratic boundaries: reconciliation and proof review, 12 October 2026

This delivery is an addition to the existing boundary-completion report,
not the first resolution of the predecessor's boundary question. Its source
predates the integration already present in collective Sections 1.7 and 1.8.
All delivered files remain unchanged; the following are intake findings.

## Exact overlap and accepted refinements

The notation dictionary to the host's sections/02-phase.tex and
sections/03-charts.tex is new X = old d = -Log(r/R), new tau = old x,
and new B = old A = zeta(s-1). This is the same logarithmic coordinate,
not merely a leading equivalent of 1-r/R.

- The quadratic lift, positive coefficients, exact dominant radius, strict
  boundary amplitude and three critical laws agree with the host and the
  collective phase theorem. The circle-continuation argument uses strict
  positivity, absolute boundary convergence and an implicit derivative
  smaller than 1 away from the positive point. Real monotonicity alone
  would not prove the complex radius.
- Both noninteger convergent two-generator charts and finite Lagrange
  extraction already occur in the host's sections/03-charts.tex, including
  its labels thm:chart-low and thm:chart-high. The new display expands the
  same analytic tail. The minimum ramification statements follow from
  the nonzero leading exponent below order 3, and from both the half-power
  and the first non-half-integer exponent above order 3.
- The marginal shift 5/2 and finite Gamma-derivative hierarchy overlap
  collective Section 1.8. The apparent different normalizations are
  reconciled by Y = 2 Lambda for the same Lambert core. Do not duplicate
  these as separate discoveries or import the linear-core shift 3/2.
- The logarithmic transfer dictionary uses Li_(lambda+1) to subtract
  each singular power of X. It therefore has no artificial integer 1/n
  descendants for an individual X^lambda term. Parameter differentiation
  gives the logarithmic terms. This supplies the host's explicit open
  task in sections/07-verification-research.tex, lines 232-239, on finite
  coefficient corrections away from the marginal order.
- At s=5/2, the X term is analytic and its n^-2 coefficient is exactly
  zero; the next displayed coefficient is negative. At s=4 the nonzero
  X*log(X) term yields +zeta(3)/(6*(1+zeta(2))^2) times n^-2. The general
  integer obstruction above order 3 agrees with the host's logarithmic
  chart and excludes finite Puiseux ramification of the full inverse.
- Finite-prefix transport retains f_j >= 0 and f_1 > 0, not positivity of
  the prefix polynomial alone. The singular amplitude kappa, endpoint
  moments and quadratic contribution give the displayed marginal shift
  3/2 + (1 + D^2 P(1))/kappa. This is an additional normalization extension.

The proofs of these fixed-parameter statements are accepted for synthesis:
the convergent implicit charts justify finite local truncation, and sectorial
continuation plus finite Hankel transfer justify the coefficient expansions.
An infinite convergent coefficient-asymptotic sum is not asserted.

## Fresh replay and remaining work

The full unchanged suite completed on an isolated copy at its delivered
maximum n=4096: 293 exact assertions, 21 original-equation checks, six
Lambert-core checks and 49 coefficient evaluations across seven models.
The pinned dependencies were SymPy 1.14.0, mpmath 1.3.0 and NumPy 2.3.5
on Python 3.13.5. Windows longdouble has 15 decimal digits here, so the
delivered arbitrary-exponent mpmath fallback was used where needed; this
is not a byte-identical reproduction of the delivered Linux floating data.
The local coordinate checks use 85 digits. Fresh records retain the engine
used for every coefficient. None are interval certificates or Lean proofs.

Synthesize the nonmarginal charts and finite coefficient transfer in Volume I
after the existing phase and marginal sections, crediting both reports.
This intake has not yet changed the canonical TeX or rebuilt its PDFs.
The delivered future questions about moving critical parameters must be
read alongside the host's existing order-crossover and coefficient-crossover
sections, whose separate proof audits remain pending; they are not evidence
that those topics are absent from the current repository.
