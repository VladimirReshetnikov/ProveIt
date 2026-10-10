# Independent review of the sharp global Euler constant

Status: the proposed argument is valid. The endpoint atom in the
fourth-power mixture and the range `x/sqrt(s) >= 1` are essential details.
Both are treated below and are explicit in the final article. The polynomial certificates
have also passed a separate symbolic and exact-rational replay.

## 1. Probability normalization and remainder identity

The probability density
`mu_a(dx)=(-log x)^(a-1) dx/Gamma(a)` on `(0,1)` is exactly the law of
`X=exp(-T_a)` for `T_a ~ Gamma(a,1)`, since the Jacobian is `dx=-exp(-t)dt`.
It has moments `E[X^m]=(m+1)^(-a)`.

For independent `X~mu_a`, `Y~mu_b`,

`f(n) = E[(X^(2n)-(XY)^(2n))/(1-Y)]`.

Indeed `(1-Y^(2n))/(1-Y)` has `2n` terms, whose expectation is precisely
`H_(2n)^(b)`. Consequently

`d_k=E[((1-X^2)^k-(1-X^2Y^2)^k)/(1-Y)]`.

The integrand is strictly negative for `k>=1`, with magnitude at most
`2k` by the mean-value theorem in `Y`. Thus the Euler transform converges
absolutely for all positive `a,b`, independently of whether the original
alternating boundary series converges.

The analytic identity

`F_(a,b)(z) = z^2 E[X/((1-zX)(1-zXY))]`

has coefficient `H_(n-1)^(b)/n^a`: the numerator supplies one extra factor
`X`, so no factor is missing. It extends to the slit plane by local uniform
domination. At `z=i`, its imaginary part is

`g = -E[X^2(1+Y)/((1+X^2)(1+X^2Y^2))]`.

Summing the absolutely convergent Euler transform gives this same value.
Geometric summation of its tail gives

`R_N=2^N(E_N-g)=E[(W_N(XY)-W_N(X))/(1-Y)]`,

with `W_N(x)=(1-x^2)^N/(1+x^2)`. Its sign is strictly positive.

## 2. Fourth-power mixture

Write `w_N(t)=W_N(sqrt(t))=(1-t)^N/(1+t)` for `0<=t<=1`.
For `N>=4`, the derivatives of orders 0 through 3 vanish at 1, and
`(-1)^5 w_N^(5)(t)>=0`. The latter follows directly from Leibniz's
rule, since every derivative term has the same alternating sign.

Taylor's integral formula at 1 gives

`w_N(t)=alpha_N (1-t)^4 + integral_(t)^1 [-w_N^(5)(s)](s-t)^4 ds/24`,

where `alpha_N=w_N^(4)(1)/24`. Thus `alpha_4=1/2` and `alpha_N=0` for
`N>4`. This is a positive mixture of `(1-t/s)_+^4`, with mixing density
`s^4[-w_N^(5)(s)]/24` on `(0,1)` and the displayed atom at `s=1`.
Evaluating at `t=0` gives total mass `w_N(0)=1`.

## 3. The component maximum includes the truncated region

For a component and fixed `0<y<1`, put `z=x^2/s`, so the kernel is

`[(1-zy^2)_+^4-(1-z)_+^4]/(1-y)`.

On `0<=z<=1`, its numerator derivative is
`4[(1-z)^3-y^2(1-zy^2)^3]`. It changes sign exactly once, at

`z_*=(1-y^(2/3))/(1-y^(8/3))`, which lies strictly between 0 and 1.

On `1<=z<=1/y^2`, the numerator is `(1-zy^2)^4`, strictly decreasing.
For `z>=1/y^2`, it is zero. Hence the global maximum over *all* `z>=0`
occurs at `z_*`; restricting the proof to `z<=1` would otherwise leave
the possible range `x>sqrt(s)` untreated.

Substitution gives the exact maximum

`M_4(y)=(1-y)^3(1+y)^4/(1-y^(8/3))^3`.

The endpoints are harmless: `M_4(0)=1` and its limit at 1 is `27/32`.
Putting `y=t^3` reduces `M_4(y)<9/8` on `0<y<1` to positivity of

`Q_4(t)=[9(1-t^8)^3-8(1-t^3)^3(1+t^3)^4]/(1-t)^3`.

## 4. Independent exact replay

`review_euler_certificate.py` reconstructs both bivariate rational-kernel
numerators and the univariate fourth-power polynomial in SymPy. It does
not import any polynomial or Bernstein code from the producer.
It proves the stored coefficient lists equal those exact expressions,
verifies every box lies in the unit box, verifies pairwise disjoint
interiors, verifies total volume 1, and recomputes every Bernstein
coefficient after an independent affine substitution.

All checks passed:

| Polynomial | Boxes | Positive coefficients | Minimum coefficient |
|---|---:|---:|---:|
| `P_2` | 13 | 208 | `3/64` |
| `P_3` | 7 | 210 | `11337/40960` |
| `Q_4` | 2 | 44 | `1` |

The machine-readable independent report is
`euler_independent_review.json`.

## 5. Sharpness and scope

The resulting bound `R_N<9/8` holds for every integer `N>=2` and every
positive `a,b`. For `N=1`, `R_1=-2g`, whose global supremum is the
previously proved unique Gaussian axis maximum
`C_*=max_(b>0)[beta(b)+2^(-b)eta(b)]`. The final article supplies the short exact witness
`C_* >= C(1) > -2 E_8(0,1) = 1627631/1441440 > 9/8`; hence the maximum over truncation indices is controlled
by the first Euler truncation in the *global* optimization problem.

It follows that `C_*` is the least universal constant in the strict
enclosure `0<E_N-g<C_*2^(-N)` over all `a,b>0` and `N>=1`. Sharpness
uses `N=1`, `b=b_*`, `a down to 0`; no claim that scaled remainders are
monotone in `N` at every fixed supercritical pair is needed or implied.
This last distinction should remain explicit.
