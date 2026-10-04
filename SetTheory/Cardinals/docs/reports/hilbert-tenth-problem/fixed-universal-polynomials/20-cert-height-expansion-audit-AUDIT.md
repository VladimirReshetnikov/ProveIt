# Independent audit of the separate analytic height follow-on

## Verdict and precise scope

**PASS: no mathematical defect found.** The proof in
`../square-product82-height-expansion-20261004/LOG_HEIGHT.md` establishes:

1. The exact real logarithmic identity E1
2. Its absolutely convergent five-scale expansion E2 and explicit truncation
   error E3
3. The uniform leading correction E5, with a positive difference from N
4. Strict increase of the specified real analytic interpolation, branch by branch
5. The first exponentially small inverse correction E7 with its stated constant 64
6. A convergent algebraic inverse expansion near infinity, with all three
   displayed coefficient lists correct

This is **not a complete all-orders inverse transseries**. The forward statement
is an exact convergent multiscale identity in five dependent small arguments.
The inverse statement combines a convergent algebraic cubic-root branch with
one explicitly controlled exponential correction. It does not enumerate all
inverse exponential sectors. The real interpolation is not a family of
noninteger chart witnesses, and none of these statements smooths away the
power-of-five radix jumps in the ordinary input.

No mathematical change to the draft was required. Its author was asked only
to update the obsolete initial verification-status prose. The precise reviewed
source hash and dependency pins are in `SOURCE_BINDINGS.json`. This audit and
its evidence are separate from the frozen exact-height/minimum-completion core.

## 1. Exact identity and forward series

Let alpha=ln(lambda_A). The real-positive Pell formula gives exactly

    S=sinh(p*alpha)^2,
    ln(2S)=2p*ln(lambda_A)+2ln(1-u)-ln2.

The auxiliary formula gives, without a floor or asymptotic approximation,

    ln H=(R-1)ln(2S)+R*g(b)-(1/2)ln(1-b)+ln(1-v).

Substituting
`ln(lambda_A)=L ln2+ln(1+d)+g(a)` proves E1, including every sign and
factor of two. In particular the coefficient of `g(b)` is R, not R-1,
and the denominator contributes `-(1/2)ln(1-b)`.

Differentiation yields

    g'(z)=-(1/(2z))*[(1-z)^(-1/2)-1].

The binomial series and `g(0)=0` therefore give
`g(z)=-sum c_j z^j`, with exactly
`c_j=binom(2j,j)/(2j*4^j)`. Every argument is in `(0,1)`, so each component
series is absolutely convergent. Summing the five absolutely convergent
series termwise proves E2; the fact that their arguments depend on one
another creates no convergence obstruction for this finite sum.

The alternating logarithm remainder supplies the first term of E3.
For the other four tails, `0<c_j<=1/(2j)` and `j>=k+1` give the displayed
geometric bounds. Applying the triangle inequality to the b coefficient
produces `(R+1)/(2j)`, as used in E3; its sign need not be guessed. The
stated remainder is in natural-log units and must be divided by ln2 for
base-two log height, exactly as the draft says.

The notation “all-orders” is warranted in this precise convergent identity
sense. Grouping all five powers with the same j is not a claim that these
terms have one globally decreasing asymptotic ordering in the ordinary input.
The draft expressly disclaims that stronger interpretation.

## 2. Uniform leading correction

The four smaller arguments satisfy E4 under the stated hypotheses, also for
real p and y in the interpolation. The necessary lower bound on S follows
from

    lambda_A>2^L+1,
    lambda_A^(2p)>2^(2pL)+2p*2^((2p-1)L)>2^(2pL)+2,
    S=(lambda_A^(2p)-2+lambda_A^(-2p))/4>2^(2pL-2).

The convexity/Bernoulli step is valid for real `2p>=32`; it does not require
p to be an integer. Since `d>=2^(-p)`, the elementary exponent comparisons
then give `a,u,b,v<=d^2/16`. For a itself the stronger estimate
`a<2^(-2p-2y)<=2^(-2p-6)` already suffices.

Applying the stated logarithm inequalities to E1 gives five contributions
bounded, after normalization by `B*d^2`, by

    1/2, 1/16, 1/(8p), 1/(16p), 1/8.

The fourth follows from `(R+1)/(R-1)<=2` for `R>=3`; the last deliberately
drops the favorable factor B. Their sum is at most `179/256<1` for
`p>=16`. Thus E5 has its claimed strict constant-one error bound. In
particular the difference is positive, since its main term is `B*d/ln2`
and `0<d<1`. E6 is a valid rearrangement; the constant-one assertion is
correctly restricted to E5 before that rearrangement.

## 3. Real interpolation and derivative estimates

On each branch `p(R)` and `y(R)` are strictly increasing positive affine
functions for `R>=100`. Hence A, lambda_A, lambda_A^p, S, and arcosh(S)
increase strictly. The quotient `sinh(R theta)/sinh(theta)` increases
strictly in R for fixed positive theta. It increases in theta because

    R*coth(R theta)-coth(theta)>0,

which follows from strict increase of `z*coth(z)`. The derivative numerator
`sinh(z)cosh(z)-z` is positive for positive z. This proves interpolation
monotonicity without relying on integer Pell recurrences or bit lengths.

For the displayed cubics, direct differentiation gives

    A+: N'=4R^2+(8/3)R-7/3, N''=8R+8/3,
    A-: N'=4R^2-8R+3,       N''=8R-8,
    B:  N'=(75R^2+50R-39)/14, N''=(150R+50)/14.

For every `R>=100`, these satisfy `N'>3R^2` and `0<N''<12R`.
The error coefficient B is `(4/3)(R^2-1)`, `(4/3)(R-1)^2`, or
`(10/7)(R^2-1)`, respectively. Therefore `B<2R^2` and
`0<B'/B<=3/R` uniformly. With `ln2>2/3`, these also give

    B/(ln2*N')<1,
    B'/B+N''/N'+p'ln2 < 7/R+1 < 2.

Consequently `0<T(R)<2^(-p(R))` and `|T'(R)|<2*2^(-p(R))`.
All constants in the inverse argument hold on the whole real interval,
not only at the integer fixtures used for numerical checks.

## 4. Inverse correction and the explicit 64 error

Write `ell_h=N(R)+E(R)` and let `r0` solve `N(r0)=ell_h` on `r0>=100`.
The monotonic cubic is unbounded there, so the root exists and is unique.
E5 gives `E(R)>0`, hence `delta=r0-R>0`. The mean-value theorem gives

    delta=E(R)/N'(xi), R<xi<r0,
    delta<d(1+d)<2d<4q, q=2^(-p(R)),
    delta<1.

The logarithmic error estimate gives

    |E(R)-B(R)q/ln2| <= (B(R)/ln2)*(2q/Y+4q^2).

After division by `N'(xi)`, this contributes at most `2q/Y+4q^2`.
Changing the principal denominator from `N'(xi)` to `N'(R)` is harmless.
Indeed a direct bound slightly stronger than the draft's is

    (Bq/ln2)*[N'(xi)-N'(R)]/[N'(xi)N'(R)]
        < q*[12xi*(xi-R)]/[3xi^2]
        < 4q*delta/R.

In particular the draft's bound `5q*delta/R<20q^2/R<=q^2/5` is valid.
The derivative estimate above gives
`|T(r0)-T(R)|<2q*delta<8q^2`. Thus the total error is below
`2q/Y+13q^2`, as claimed.

Finally `p',y'<1` and `delta<1` imply
`q<2*2^(-p0)` and `1/Y<2*2^(-y0)`. Therefore the error is below

    8*2^(-p0-y0)+52*2^(-2p0)
      <=64*[2^(-p0-y0)+2^(-2p0)].

This verifies the exact constant, signs, and evaluation point in E7.
Using the full rational coefficient in T is essential to this stated
remainder. Replacing it with its limit generally contributes the much
larger additional term `O(2^(-p0)/r0)`; the draft explicitly warns of this.
The two limits `1/(3ln2)` and `4/(15ln2)` are correct.

## 5. Algebraic inverse coefficients and convergence

After normalizing by gamma and translating to a depressed cubic, the
coefficients of the linear and constant terms are

    A+: -25/12, 11/27,
    A-: -3/4,  0,
    B:  -142/75, 104/675.

For `t^3+P*t+Q=s^3`, substitution gives
`t=s-(P/3)s^(-1)-(Q/3)s^(-2)+O(s^(-3))`. Translating back produces
exactly all three displayed lists in LOG_HEIGHT.md. In particular the
A- coefficient at `s^(-2)` is zero.

The rescaling `r=s*h`, `w=1/s` yields an analytic polynomial equation
with derivative 3 in h at `(w,h)=(0,1)`. The analytic implicit-function
theorem provides a unique genuinely convergent power series h(w) near
zero, not just a formal asymptotic solution. For positive sufficiently
large s this branch is the unique large real cubic root. No explicit
convergence radius was claimed or needed. This proves all algebraic
orders, while E7 adds only the stated first exponential inverse correction.

## 6. Independent corroborative evidence

`check_expansion.py` is newly authored and executes no upstream code or saved
schedule. Normal and `python -O` runs give byte-identical PASS receipts,
with 8,719 active checks. They include:

* Exact rational polynomial/derivative checks for all three branches at
  403 bounded rational points each
* Exact rational recursion of the algebraic inverse through order 12,
  including zero residual through that order and every displayed coefficient
* 1,000 exact central-binomial coefficient envelope checks
* 18 independent real interpolation cases, including fractional R, over
  `R=100,100.5,101,143,250,512`, using up to 983 decimal digits
* Direct hyperbolic evaluation of log height compared with E1; E3 tails
  through truncation order four; E4/E5; derivative and displacement bounds;
  an independently solved cubic inverse and E7
* 240 generic g-series/tail tests where its terms are numerically visible

The largest sampled E7 error-to-bound ratio is below 0.0151. These are
high-precision numerical corroborations, **not interval-certified numerical
proofs**. The unbounded conclusions and uniform constants are established
by the proof audit above. No integer witness tuple was materialized.
