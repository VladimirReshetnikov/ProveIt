# Corrections, extensions, and scope

No new mathematical error was established in the accepted repository statements
actually inspected. The following are safeguards attached to the present proofs,
not claims that the source authors made these mistakes.

## 1. Zero order requires an actual continuation argument

The positive-integer first-jet Gamma-kernel theorem in the existing resonant
article assumes m >= 1. This report extends the first jet to m = 0 by a direct
contour proof and a digamma identity. The original lattice boundary integrals
have local powers justified for Re(s)>0. At zero, the product
`zeta(1-s,a)/Gamma(s)` must be continued as a whole; the removable value of each
lateral core is 1, not 0. The explicit ordinary zero-order minor is

    1/xi - pi/sin(pi*xi).

## 2. Jump-free does not mean physically complete

Theorem `ojf:thm:neutral` constructs an exactly zero-jump order curve while its
arithmetic completion remains `(-1)^m*exp(-x)+O(exp(-2*x))`. The joint ideal
classifies cancellation of both data. First-order robustness of an actionwise
jump cancellation under order detuning is equivalent to joint cancellation and
therefore requires degree 2N for the first N actions.

These are forward analytic statements. They do not assert removal of every
singular germ on every Borel sheet, nor do they define an Ecalle median.

## 3. Inversion must retain the correct exact core

Use the holomorphic conjugate-pair digamma formula for A(z) in complex inverse
arguments. Do not apply complex inversion to a formula containing `Re` as an
operation on complex z. The inverse core is exactly w=A^{-1}(y); replacing it
by a finite algebraic asymptotic approximation generally overwhelms the
exponential correction.

The inverse average and the physical inverse differ in second sector by

    [pi^2/a_w^2 + pi^2*b_w/(2*a_w^3) - log(2)/a_w] * exp(-2*w),

where a_w=A'(w), b_w=A''(w). The remainder is O(w^3 exp(-3w)). This is a
specialization of the already-known nonlinear averaging obstruction, with an
explicit uniform analytic chart and physical comparison, not a new discovery
that arithmetic averaging fails to be an algebra homomorphism.

## 4. Degree optimality has a coefficient-field qualification

The sharp filter construction allows arbitrary real coefficients, including
logarithms of spectral nodes. For nonconstant filters of the restricted form
c*p(u/pi), with p having real algebraic coefficients, neither real nor imaginary
action data can vanish at any n>=2 at integer or half-integer centers. This
follows from Gelfond–Schneider; increasing degree alone does not remove this
arithmetic restriction.

## 5. Certificates and evidence are not stronger than stated

The endpoint radius sqrt(3)/40 and large-core parameter radius c/w are sufficient
analytic disks, not optimal radii. Real monotonicity proves the real inverse
exists globally, not that its complex continuation is univalent everywhere.
The 165 exact checks are finite regressions, and the 46 numerical checks are
floating-point diagnostics, not a formal or interval proof.

## 6. The source audit is bounded

Three incoming ZIPs could not be inspected. No theorem in them is alleged to be
wrong or absent. Before promotion into canonical volumes, compare this package
against those actual archive contents. See SOURCE_AUDIT.md for pinned identities
and the exact limitation.
