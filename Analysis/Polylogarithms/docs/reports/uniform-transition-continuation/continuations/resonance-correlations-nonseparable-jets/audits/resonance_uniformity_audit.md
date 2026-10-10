# Independent audit of the resonance section

All displayed formulas in `deliverable/sections/02_resonance.tex` were checked.
No sign, factorial, or domain obstruction was found. The exact gamma factor is

    (-1)^k k! Gamma(-k-epsilon) t^epsilon
    = -exp(-T epsilon) E_k(epsilon)/epsilon.

The polygamma formula is correct because
`psi^(r-1)(k+1)=(-1)^r(r-1)![zeta(r)-H_k^(r)]`.
The finite-part polynomials and normalized Hurwitz primitive also check.

## Small wording/logical changes recommended to the root

1. `H_k-log(k+1)` is increasing to Euler's constant, not decreasing.
2. In the exact-cancellation proof, name the logarithm explicitly as that of
   `Gamma(1-epsilon)/prod(1+epsilon/j)`: the displayed larger factor includes
   `1/epsilon`, which is not an analytic logarithm at zero.
3. After the shift-difference formula, justify passage to the unweighted sum
   by dominated convergence. On a fixed compact positive v interval,

       d/dv [ exp(-(m+v)t) log^n(m+v)/(m+v) ]
       = O((1+log^n m)/m^2)

   uniformly for t>0 and m large. The new term caused by the exponential uses
   `t exp(-(m+v)t) <= 1/[e(m+v)]`. The mean-value theorem now supplies a
   summable majorant for the weighted difference itself.
4. The centered coefficients `b_{k,j}` must remain in the uniform expansion.
   Their k->infinity limits cannot replace them to all orders on arbitrary
   joint paths. Quantitatively `E_k(w)-pi*w/sin(pi*w)=O(|w|^2/(k+1))` locally
   in |w|<1, leading to an additional error O(1/[(k+1)T]) after resonance
   normalization. The current limiting-coefficient proposition is correct.

## A full normal-convergence proof for the tail hinge

For every compact `K` contained in `Re a>0`, every `0<rho<1`, and every
`0<R<2*pi`, one has

    sup_{a in K, |epsilon|<=rho}
    sum_{ell>=1} R^ell/ell! * |zeta(1+epsilon-ell,a)| < infinity.

Use Hermite's integral, equivalently

    zeta(s,a)=a^(-s)/2 + a^(1-s)/(s-1)
       + i integral_0^infinity
         [(a+i y)^(-s)-(a-i y)^(-s)]/(exp(2*pi*y)-1) dy.

This is the equivalent-power form of DLMF 25.11.29, verified at
https://dlmf.nist.gov/25.11.E29 (web reference `turn12view0`; the root should
open the source before citing it). Powers use the principal logarithm;
`Re(a+-iy)>0` makes this branch uniform on the allowed parameters.

Set `s=1+epsilon-ell`, and let `delta>0` bound `Re a` below and `A` bound
`|a|` above on K. The two elementary terms are bounded by `C D^ell` for a
fixed D, using `|ell-epsilon|>=ell-rho`. Their factorially weighted sums
therefore converge uniformly.

For y>=1, the absolute values in the integral are bounded by
`C(A+y+1)^(ell-1+rho)`. Sum them with `R^ell/ell!` before integrating.
The result is bounded by a polynomial in y times
`exp[-(2*pi-R)y]`, which is integrable.

For 0<=y<=1, retain the difference in the numerator. Integrating its
derivative along the segment from -y to y gives a bound
`C y(ell+1)D^ell`; the factor y cancels the first-order zero in the
denominator. The factorially weighted sum is again uniformly finite.
This proves the asserted bound without restricting a to be real.
Enlarging K slightly and using Cauchy's formula also gives all fixed
a-derivative bounds used in the resonance theorem.

Now

    k!/(k+ell)! <= 1/[(k+1)ell!], ell>=1,

and the preceding lemma, with t_0<R<2*pi, gives

    |B_k| <= C t/(k+1).

Finally

    t/(k+1) = exp(-T) exp(H_k-gamma)/(k+1) <= exp(-T),

using the corrected harmonic inequality. This makes the all-k exponential
tail estimate completely explicit.

