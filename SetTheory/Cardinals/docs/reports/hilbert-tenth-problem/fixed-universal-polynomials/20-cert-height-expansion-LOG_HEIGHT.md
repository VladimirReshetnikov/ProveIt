# Separate follow-on: convergent log-height expansion and cubic inversion

Author proof and bounded checks are complete; the separate independent
mathematical audit reported PASS for E1–E7 and the Puiseux coefficients.
This is a separately scoped extension of the core HEIGHT.md /
AUX_MINIMUM.md packet. No upstream program or schedule is executed.

## 1. Exact identity and convergent all-orders expansion

Use the core construction's p,y,R, with L=p+y+1 and
N=(R−1)(2pL−1). Let

    X=2^p, Y=2^y, d=X^(−1)+2/(XY), A=XY+Y+2,
    lambda_A=A+sqrt(A^2−1),
    c=(lambda_A^p−lambda_A^(−p))/(2sqrt(A^2−1)),
    S=(A^2−1)c^2=(lambda_A^p−lambda_A^(−p))^2/4,
    lambda_S=S+sqrt(S^2−1), H=psi_S(R),
    B=2p(R−1), a=A^(−2), b=S^(−2),
    u=lambda_A^(−2p), v=lambda_S^(−2R).

Here B is an error coefficient, not the compiler radix. Define

    g(z)=ln((1+sqrt(1−z))/2),  0<=z<1.

Directly from the two Pell formulas,

    (ln 2)(log2 H−N)
      = B[ln(1+d)+g(a)] + 2(R−1)ln(1−u)
        + R g(b) − (1/2)ln(1−b) + ln(1−v).                (E1)

Indeed lambda_A=2^L(1+d)*exp(g(a)),
2S=lambda_A^(2p)(1−u)^2/2, and
H=lambda_S^R(1−v)/(2sqrt(S^2−1)). This proves (E1)
without an approximation or a logarithmic-floor argument.

Set c_j=binom(2j,j)/(2j*4^j). Differentiating g and integrating its
convergent binomial series gives

    g(z)=−sum_(j>=1)c_j*z^j.

Thus (E1) is the absolutely convergent multiscale expansion

    (ln 2)(log2 H−N)
      = sum_(j>=1) [
          B*(-1)^(j+1)*d^j/j − B*c_j*a^j
          −2(R−1)*u^j/j
          +(1/(2j)−R*c_j)*b^j − v^j/j ].                 (E2)

All five arguments d,a,b,u,v lie strictly between zero and one. This is
an all-orders convergent formula, with explicit main-radical,
main-conjugate, auxiliary-radical, and auxiliary-conjugate scales. It is
not merely a formal first-order asymptotic. Those names describe terms in
a formula, not separate circuit operations.

If E2 is truncated after j=k, k>=1, the absolute error in natural-log
units is at most

    B*d^(k+1)/(k+1)
    + B*a^(k+1)/[2(k+1)(1−a)]
    + 2(R−1)*u^(k+1)/[(k+1)(1−u)]
    + (R+1)*b^(k+1)/[2(k+1)(1−b)]
    + v^(k+1)/[(k+1)(1−v)].                              (E3)

For the d term use the alternating-series bound; for the others use
c_j<=1/(2j) and geometric tails. Division by ln2 gives the error in
log2 H. The coefficient of b has been bounded by
R/(2j)+1/(2j), so (E3) is valid without sign assumptions.

One may substitute a=2^(−2p−2y)(1+d)^(−2) and expand its factors by
the convergent binomial series. The exact conjugate variables u,v retain
the still smaller scales. We do not claim a globally ordered single-power
series in x, nor a single fixed coefficient asymptotic across radix jumps.

## 2. Explicit first-order bound

For the actual construction, and also for the real interpolation below,
p>=16, y>=3, R>=8, R<2p. Then

    0<d<2^(1−p),
    a,u,b,v <= d^2/16.                                    (E4)

Here a<2^(−2p−2y). Also lambda_A>2XY+1>2^L, so
u<2^(−2pL). Convexity gives
lambda_A^(2p)>2^(2pL)+2p*2^[(2p−1)L]>2^(2pL)+2;
hence S>2^(2pL−2), and b<2^(−4pL+4).
Finally lambda_S>S gives v<2^[−2R(2pL−2)]. Each of these last
three bounds is at most 2^(−2p−4)<=d^2/16 under the displayed
hypotheses. In particular all four arguments are below 1/2.

Using |ln(1+d)−d|<=d^2/2,
|g(z)|<=z/[2(1−z)], and |ln(1−z)|<=z/(1−z), equation E1 gives

    |log2 H−N − B*d/ln2| < B*d^2/ln2.                     (E5)

For a fully explicit budget, after division by B*d^2 the five error
contributions are at most

    1/2, 1/16, 1/(8p), 1/(16p), 1/8,

respectively: the last bound is deliberately loose, using B>=1.
Their sum is below one for p>=16. This proves (E5), not merely its
order notation. In particular

    log2 H−N = [2p(R−1)/ln2]*2^(−p)
              *[1+2^(1−y)+O(d)],                         (E6)

and (E5) specifies an absolute constant of one for the remainder before
this final rearrangement. The difference is strictly positive because
d<1. The exact integer bit length from the core proof remains N+1.

## 3. Real interpolation and monotonicity

For each branch separately, extend p and y to affine functions of real
R>=100:

    A+: p=2(R+1)/3, y=(R+1)/3−1
    A−: p=2(R−1)/3, y=(R−1)/3−1
    B:  p=5(R+1)/7, y=15(R+1)/28−1.

Use the real positive formulas in Section 1 to define S(R) and
mathcal_H(R)=sinh(R*arcosh(S(R)))/sinh(arcosh(S(R))).
For integer parameters this is exactly the auxiliary Pell witness.
It is a distinct real analytic interpolation, not an assertion that
noninteger indices or inputs are chart witnesses.

A, lambda_A, and lambda_A^p strictly increase with R. Therefore
S=(lambda_A^p−lambda_A^(−p))^2/4 strictly increases. For theta>0 and
R>1, sinh(Rtheta)/sinh(theta) strictly increases in R and theta.
For theta, differentiate its logarithm: R*coth(Rtheta)−coth(theta)>0,
because z*coth(z) strictly increases on z>0:

    d[z*coth(z)]/dz = [sinh(z)cosh(z)−z]/sinh(z)^2 > 0.

Thus mathcal_H and log2(mathcal_H) are strictly increasing. The core
integer bit-length claim is not needed for this monotonicity proof.

Let N(R) denote the branch cubic (bit length minus one):

    A+: N=(4R^3+4R^2−7R−1)/3
    A−: N=(4R^3−12R^2+9R−1)/3
    B:  N=(25R^3+25R^2−39R−11)/14.

For R>=100, N'(R)>3R^2 and 0<N''(R)<12R. Also
B(R)=2p(R)(R−1)<2R^2 and B'(R)/B(R)<=3/R.
Consequently N has a unique increasing real inverse in this range.

## 4. First exponentially small inverse correction, with a bound

Take an actual or interpolated R>=100 and let ell_h=log2(mathcal_H(R)).
Let r0 be the unique real root of N(r0)=ell_h on the large-R branch.
Define p0=p(r0), y0=y(r0), and

    T(r)= [2p(r)(r−1)/(ln2*N'(r))]*2^(−p(r)).

Then

    R = r0−T(r0)+error,
    |error| <=64[2^(−p0−y0)+2^(−2p0)].                    (E7)

Here is an explicit derivation. By E5, ell_h=N(R)+E(R), where
E(R)>0. Therefore r0>R and, writing delta=r0−R,

    delta=E(R)/N'(xi),       R<xi<r0,
    0<delta<2d<1.

For the second inequality use N'(xi)>=N'(R)>3R^2,
B<2R^2, ln2>2/3, and E<=B*d(1+d)/ln2.
Let q=2^(−p(R)). E5 and d=q(1+2/Y) yield

    |E(R)−B(R)q/ln2| <= [B(R)/ln2]*(2q/Y+4q^2).

Since B/(ln2*N')<1, division by N'(xi) gives an error at most
2q/Y+4q^2. Replacing N'(xi) by N'(R) contributes at most
5q*delta/R<20q^2/R<=q^2/5, using N''<12r and delta<4q.
Moreover |T'(r)|<2*2^(−p(r)) for r>=100, because

    |T'/T| <= B'/B + N''/N' + p'ln2 < 2,
    0<T(r)<2^(−p(r)).

Thus replacing T(R) by T(r0) costs at most 2q*delta<8q^2.
The total is less than 2q/Y+13q^2. Since delta<1 and both p',y'<1,
we have q<2*2^(−p0) and 1/Y<2*2^(−y0). Hence the total is at most
8*2^(−p0−y0)+52*2^(−2p0), proving the stated looser constant 64.

The exact rational coefficient in T tends to

    1/(3ln2) in either Branch A,
    4/(15ln2) in Branch B.

Equation E7 uses the full coefficient at r0; replacing it by its limit
introduces an additional O(2^(−p0)/r0) error and would not preserve E7.

## 5. The algebraic cubic inverse has a convergent Puiseux expansion

Set gamma=4/3 in A and gamma=25/14 in B, and let
s=(ell_h/gamma)^(1/3). The large cubic root has

    A+: r0=s−1/3+(25/36)s^(−1)−(11/81)s^(−2)+O(s^(−3))
    A−: r0=s+1+(1/4)s^(−1)+0*s^(−2)+O(s^(−3))
    B:  r0=s−1/3+(142/225)s^(−1)−(104/2025)s^(−2)+O(s^(−3)).

These coefficients follow by direct substitution into the displayed
cubics. To see that the all-orders algebraic series converges near
infinity, write N(r)=gamma*r^3+b2*r^2+b1*r+b0, r=s*h, w=1/s.
Then h solves

    h^3+(b2/gamma)w*h^2+(b1/gamma)w^2*h+(b0/gamma)w^3=1.

At w=0,h=1 the derivative with respect to h is 3, so the analytic
implicit-function theorem supplies a unique convergent power series
h(w) near zero. Its recursively determined coefficients give all orders
of the algebraic inverse. E7 then adds the first exponentially small
correction beyond that convergent algebraic branch.

This does not claim a fully enumerated all-orders inverse transseries.
The forward all-orders expansion E2 and the first inverse correction E7
are the completed results. All claims about x remain subject to the
core packet's power-of-five radix jumps.

## 6. Verification status

The author checker expansion_check.py passed with 355 active checks in
normal and optimized execution; the receipts are byte-identical. It uses
450-digit Decimal arithmetic on nine independent real parameter cases
(three branches, R=100,200,300), tests truncations at orders1,2,4, checks
the explicit inverse bound, and verifies the displayed Puiseux coefficients
with exact rational arithmetic. Decimal tests are corroborative, not
interval-arithmetic certification; the proof supplies the rigorous bounds.

The independent reviewer reported a separate PASS after checking E1–E7,
all derivative/error constants, and the Puiseux coefficients, with a fresh
checker covering18 real cases through R=512 including fractional R and
12 exact inverse-series coefficients. Its own audit packet supplies those
independent receipts. No claim about a fully enumerated or convergent
all-orders exponential inverse expansion is included here.
