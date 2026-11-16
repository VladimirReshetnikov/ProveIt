# Source audit and corrections

## Wikipedia characterization typo

The displayed characterization currently has `Gamma(x)^n`.  This fails already
at `x=1`: the recurrence gives `f(n+1)=Gamma(n)f(n)`, whereas the displayed
right-hand side would be `f(n)`.  The cited higher-order Bohr--Mollerup source
has the correct factor `Gamma(n)^x`.  The report proves the corrected version.

## Wikipedia pure-imaginary modulus typo

The displayed right-hand side for `|G(iy)|` starts with `y`.  A modulus cannot
be negative.  Conjugating the canonical product gives the squared identity with
factor `y^2`, hence the unsquared prefactor is `|y|`.

## MathWorld equation (18)

The left-hand side image is omitted in the text extraction.  Algebraically,
using `Gamma(1/4) Gamma(3/4)=pi sqrt(2)`, the right-hand side is exactly the
alternative form of the preceding formula for `G(3/4)`.

## Taylor-domain qualification

The power series is valid on the complex disk `|z|<1`, not merely on the real
interval `0<z<1`.  The report proves compact-disk tail estimates.

## Integral-domain qualification

The literal improper integral displayed on Wikipedia converges directly for
`Re z>-1`.  Elsewhere it is an analytic continuation and therefore needs an
explicit path/branch certificate.

## Logarithms and quotients

Equations involving `log G`, `log Gamma`, square roots or division are stated
only on certified zero-free domains and with a fixed branch obtained by
continuation from the positive real axis.  Globally valid versions are given
as exponentiated or cross-multiplied identities whenever practical.

## Formalization status

No web source or ProveIt proof packet is treated as a kernel proof.  Existing
`gamma_ipra` material is reused as a list of finite contracts and proof plans;
its own README explicitly says that the full analytic development and object-
theory compilation remain work.
