# Independent audit of unequal-rate Stieltjes collisions

Audited `work_tails/unequal_rate_collisions.tex` through its complete joint
spectral germ, the constant correction, and every displayed example. No
mathematical error was found. The argument applies to fixed positive rates;
the stated exclusion of ratios varying without compact bounds is necessary.

## Joint holomorphic remainder

For fixed positive lambda and mu, both `x+lambda*epsilon` and
`x+mu*epsilon` are comparable to `x+epsilon`, with constants independent of
`x in (0,1)` and small positive epsilon. In a mixed term, the Taylor remainder
of degree r has size `O((x+mu*epsilon)^(r+1))`. Multiplying it by the singular
factor of order r leaves a bound `C(x+epsilon)^(-Re u)`, and hence
`C x^(-eta)` on a compact spectral disk with `|Re u|<=eta<1/4`.
The analogous other mixed remainder has the same majorant, while the product
of regular factors is bounded. Finite Taylor remainders can be used throughout
the compact positive argument interval; an infinite Taylor series beyond its
radius is neither required nor used.

For full uniformity, split the integral at a small fixed delta. On
`(0,delta)`, the common integrable majorant makes the integral uniformly
small. On `[delta,1]`, the shifted analytic functions and their finite Taylor
remainders converge uniformly in the compact spectral disk. This proves the
locally uniform `o(1)` asserted in `urc:full-expansion`. Cauchy's integral
formula on slightly larger parameter disks then proves the same result for
each fixed mixed spectral derivative. Thus the derivative extraction does
not rely merely on pointwise convergence along spectral rays.

The singular--singular completion has omitted tail
`P_r(u)P_t(v) int_1^infinity (x+lambda*epsilon)^(-r-1-u)
(x+mu*epsilon)^(-t-1-v) dx`. It converges locally uniformly to
`P_r(u)P_t(v)/(r+t+1+u+v)`, with the minus sign shown in the finite-part germ.
There is no additional constant from this term depending on the rates.

## Finite contact extraction

The mixed primitive in `urc:exact-mixed-primitive` follows by the finite
binomial expansion in `x+lambda*epsilon`. Its noncritical lower endpoint is
exactly `epsilon^(k-r-u) M_(r,k)`, including every power of lambda.
At the critical degree k=r, the lower endpoint and the limiting upper
endpoint combine into the removable germ N_r. Setting the formal constant
in `log(epsilon)` to its coefficient of degree zero gives precisely `r! C_r`.

The Taylor coefficient multiplying it is
`gamma_n^(r+t)(1)/r!`; the factorial cancels. This independently proves the
two finite contact terms in `urc:constant-formula`. The noncritical powers
remain strictly negative after any finite spectral differentiation, and
therefore cannot contribute a constant. This also confirms the sparse list
of possible negative powers.

The ratio identity used at spectral index zero is valid: differentiation
of either side of
`sum binom(r,j)(R-1)^j/j = sum (R^j-1)/j`
gives `1+R+...+R^(r-1)`, and both sides vanish at R=1. The contact examples,
the finite harmonic coefficient formula, and the truncation at lambda=1
have the correct signs and degree.

## Independent finite-part checks

The inherited source is
`ProveIt_Lattice_Contacts_and_Mixed_Zeta_Identities_2026-10-11/sections/06_independent_shifts.tex`.
Its exact trigamma-square formula is `gs:trigamma-square`, lines 558--565,
and its finite-part evaluations are `gs:boundary-checks`, lines 609--618.
The common-shift expression and `L_3(1,a)=O(a)` already give
`F_(0,0)^(1,1)=2 zeta(3)+4 zeta'(3)` after expanding psi(1+a).

A separate germ calculation verifies this normalization. Let
`w=u+v`, `Q=Gamma(1+w)/(Gamma(1+u)Gamma(1+v))`, and
`E(s)=pi*s/sin(pi*s)`. The meromorphic Hurwitz product formula gives the raw
product of `Z_1(u,x)` and `Z_1(v,x)` as

`(1+w)(2+w) Q zeta(3+w) [E(u)/u+E(v)/v]`.

Its critical local terms have meromorphic integrals

`(1+u)(1+v)(2+v) zeta(3+v)/u`

and its exchanged companion. Subtract these two terms to obtain the
coefficientwise finite-part germ in the specified cutoff coordinate.
Each resulting quotient is removable; its value at zero is
`zeta(3)+2 zeta'(3)`. Their sum independently proves the stated trigamma
baseline.

For `F_(1,0)^(0,0)`, expand the displayed removable coincident germ using

`Q=1+zeta(2)uv-zeta(3)uv(u+v)+O(total degree 4)`,
`E(u)=1+zeta(2)u^2+O(u^4)`, and
`Z(u,1)=gamma-gamma_1*u+gamma_2*u^2/2+O(u^3)`.

The universal quotient contributes `-2zeta(2)+zeta(3)(u+v)`, while the
two Z divided differences contribute
`2gamma_1-(3gamma_2/2+2gamma*zeta(2))(u+v)`.
The coefficient of u is therefore
`zeta(3)-3gamma_2/2-2gamma*zeta(2)`; applying the Stieltjes sign convention
gives exactly `F_(1,0)^(0,0)=3gamma_2/2+2gamma*zeta(2)-zeta(3)`.

## Displayed collision laws

The three polygamma examples were re-derived from their local singular parts
and critical Taylor coefficients. Their ordered logarithmic terms cancel as
shown, leaving `zeta(2)[mu/lambda+log(mu/lambda)]`. The trigamma square has
the leading mixed beta derivative, the two reciprocal-rate zeta(2) terms,
and the indicated `4zeta(3)log(epsilon)` coefficient.

The dilogarithm numerator for E(lambda,mu) follows directly after
`y=(lambda-mu)/(x+lambda)`: an integration of `log(y)/(1-y)` produces the
stated real Li_2 expression. The diagonal limit is
`(1+log(lambda))/lambda`. The first Stieltjes collision then follows from
the singular--singular logarithm and the two critical primitives
`-gamma*(log(epsilon)+log(lambda))^2/2` and
`-gamma_1*(log(epsilon)+log(mu))`.

Exact symbolic checks of the finite-part coefficients, ratio identity,
beta derivatives, and displayed constants are provided separately in
`verify_collision_audit.py` and its output `collision_audit_verification.json`.
The numerical diagnostics in the author's verifier are corroboration only;
they are not claimed to be rigorous remainder enclosures.
