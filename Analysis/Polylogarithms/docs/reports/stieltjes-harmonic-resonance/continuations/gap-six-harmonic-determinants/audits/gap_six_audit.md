# Independent audit of the gap-six completion

Audited source: `work_rank/gap_six_proof.tex`, labels `gs:density` through
`gs:large-positive`, the inherited Gamma basis, and `gs:leading-coefficient`.
No quantitative or sign error remained after this audit. The proof's
finite-field certificate is a proof of nonvanishing, not of positivity on its
finite interval; the article makes that distinction correctly.

## Gamma input and density constants

The Gamma contour identity was checked against the complete inherited proof in
`ProveIt_Ordered_Boundary_Identities_2026-10-11/sections/08_gamma_basis.tex`.
The shifted Gamma factors have their nearest poles outside the contour strip;
the tanh multiplier's two simple poles produce the subtracted sixth derivative.
For the initial determinant, the three multiplier columns divided by tanh are
`[2v^2,v,1]`, with `v=cosh(pi x)`. Their alternant is minus twice the ordinary
Vandermonde. The polynomial alternant in `x^2` has positive leading factors.
Thus the claimed strict negative sign of the initial determinant is correct.

The cited complex logarithmic Stirling remainder is precisely supported by
DLMF 5.11(ii), https://dlmf.nist.gov/5.11: the first omitted magnitude after
`1/(12z)` is `1/(360|z|^3)`, multiplied by at most
`sec^4(arg(z)/2) <= 4` in the present right half-plane. Hence the bound
`1/(90|z|^3)` has the correct exponent, domain, and constant.

Writing `z=(x/2)(t+i)`, `t=1/(2x)`, and taking twelve real parts independently
gives exactly

`L=-(3/2)log(1+t^2)+3(arctan(t)/t-1)+4t^2/(1+t^2)+12 Re(rho)`.

The elementary terms have absolute sum at most `13/(8x^2)`; the remainder
contributes at most `16/(15x^3)`. For `x>=2`, their combined constant is
`259/120 < 9/4`. The normalized multiplier factors all lie in `[0,1]`, so
combining their error with the Gamma-density error introduces no product-error
penalty. The resulting constant is actually at most `9/2+1/9 < 6`.

## Shifted Laplace estimate

The horizontal contour deformation is entirely in `Re y>=2`; the pole at
`y=i/2` lies outside it. The left vertical segment has length `1/2` and
denominator magnitude at least `2^3`, giving the stated `3^N/16` bound.
The binomial remainder quotient at its largest argument `u=1/4` equals
`268/27 < 10`, validating the coefficient `5/(2y^2)`.

The density-error integral splits at `sqrt(N)` as claimed. The upper part is
at most `12 S2`; the lower part is bounded by
`sqrt(N)(N+1)^(N/2)`. In the two compact-to-factorial ratios, the prefactor
suppressed in the displayed bounds is
`(10/30^5)(N-5)^5`, which is indeed smaller than the polynomial factors used
there. Thus no exponential or factorial factor was lost.

For `N=4096`, the squared first threshold inequality has exact margin
`(N-5)^2-3600(N+1)=1987081 > 0`; this quadratic is increasing thereafter.
The inequality `N^6 <= 2^(N-2)` persists by the indicated induction. All
compact contributions are therefore absorbed well within the available
`16-(12+5/2)=3/2` units of `S2`.

## Normalized determinant

The odd columns' leading phases are `i` and `-i`; their next retained terms
are real. The middle column's phase is `-1`, and its first nonzero imaginary
term is `-(3/2)S1`. Both Gamma-ratio error bounds follow exactly.
The row and column scalings give the stated correction
`rho_i=(2b-1)/(2b+2i-3)`.

At `b=2048` the outer error is at most `400/4190209`, and the middle error
bound is `226588/8382465`; both are less than `1/25`. They decrease with b.
The limiting determinant and permanent are exactly `-5/1944` and
`289/23328`. The perturbation margin is
`373661/364500000 > 0`, so the large-index sign is rigorously forced.

## Inverse-row sign

A clearer proof than restoring differential-operator scales is available.
Deleting the last row and first column of `M_b` gives exactly `M_(b-1)` under
`(j,k,p,q) -> (j-1,k-1,p-2,q-2)`: all binomial pairs and the Bernoulli index
are unchanged. The cofactor formula is therefore

`lambda_last=(-1)^(b-1) det(M_(b-1))/det(M_b)`.

Substituting the bridge cancels the sign and proves the positive factor
`4b f_(b-1)/(d_(b+3) f_b)`. At b=4, the small formal minor can be evaluated
directly; no theorem for a zero-order tail is needed. The author incorporated
this cofactor argument into the fragment.

Exact original Bernoulli matrices for b=4,...,10 independently verified the
cofactor relation and inverse entry, and the auxiliary determinant is exactly
`f3=-1/638788869734400000`. These checks and the exact analytic constants are
recorded in `gap_six_audit_verification.json`.

This audit supports the proof as written. It does not replace the analytic
argument or the separately runnable full finite-field certificate.
