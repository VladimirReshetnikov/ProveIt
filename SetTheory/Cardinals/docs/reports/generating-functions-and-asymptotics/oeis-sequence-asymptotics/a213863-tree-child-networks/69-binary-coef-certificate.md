# A213863 Airy coefficient certificate

This is a formal coefficient certificate, with a standard cutoff-quasimode
interpretation for the frozen operator.  It does **not**, by itself, establish
the nonautonomous amplitude limit or turn the formal forward expansion into
an asymptotic theorem.

## Conventions and exact equations

Put c=2/3, e=N^(-1/3), x=(j+1)e, ell=z*c^(2/3), where z is the largest
negative zero of Ai.  Fix the derivative gauge

F(x)=Ai(c^(1/3)x+z)/(c^(1/3)Ai'(z)),
F''=(cx+ell)F, F(0)=0, F'(0)=1.

A pair (P,Q) denotes PF+QF'.  Every correction G_k obeys G_k(0)=G_k'(0)=0.
Thus the derivative gauge fixes multiplication of the full profile by a
formal scalar series.  The scalar coefficients below depend on this gauge.

For the frozen Jacobi problem the exact equation is

b_-(e,x)f(e,x-e)+b_+(e,x)f(e,x+e)=lambda(e)f(e,x),

with

b_-^2=1-c*x*e^2/(1+x*e^2-e^3),
b_+^2=1-c*(x+e)*e^2/(1+x*e^2).

For the original nonsymmetric recurrence, write d_N(j)=H_N f(e,x),
H_N/H_(N-1)=2(1+sum_{m>=2}s_m e^m).  Its exact formal equation is

2(1+sum s_m e^m)f(e,x)
 = b_-^2 f(e*(1-e^3)^(-1/3),(x-e)*(1-e^3)^(-1/3))
   + f(e*(1-e^3)^(-1/3),(x+e)*(1-e^3)^(-1/3)).

In particular both the spatial arguments and the explicit powers of the
profile expansion use time N-1 on the right.  Omitting the latter is an
incorrect recursion from order e^4 onward.

## Frozen coefficients and finite profile

lambda(e)=2+ell*e^2-e^3/3+(3*ell^2/4)e^4+(ell/18)e^5
          +((1143*ell^3-940)/2520)e^6+(41*ell^2/120)e^7+O(e^8).

The finite profile f=F+e^2 G_2+e^3 G_3 gives residual O(e^6), where

G_1=0,
G_2=[(-3ell+2x)/9]F+[x(3ell-x)/9]F',
G_3=-F/9+xF'/9.

Together with the e^6 scalar and G_4 below, all residual coefficients
through degree 6 vanish, so the formal residual is O(e^7):

G_4=P_4 F+Q_4 F',
P_4=(945ell^3 x^2-54ell^2-315ell x^4-1422ell x
       +70x^5-1587x^2)/17010,
Q_4=x(3ell^2+65ell x+9x^2)/945.

The degree-7 certificate, including G_5, is in coefficients-order7.json.
It has residual O(e^8), enough for a normalized-endpoint comparison through
the relative e^3 term using only the O(e^2) spectral gap and the elementary
coordinate bound by the l2 norm.

### Frozen norm and endpoint

Integration of the Airy equation gives integral F^2 dx=1/c and
integral xF^2 dx / integral F^2 dx = -2ell/(3c)=-ell.
Integration by parts gives

integral F G_2 dx / integral F^2 dx = -5ell/6,
integral F G_3 dx / integral F^2 dx = -1/6.

Therefore the squared continuum norm of the derivative-normalized profile is

(1/c)[1-(5ell/3)e^2-e^3/3+O(e^4)].

Euler--Maclaurin produces no additional relative terms through e^3 here:
the leading endpoint square and its first derivative vanish, and the
correction profiles vanish at zero along with their first derivatives.
The unnormalized endpoint is

f(e,e)/e=1+ell*e^2/6+e^3/6+O(e^4).

Thus the l2-normalized sampled frozen profile satisfies

psi_N(0)=sqrt(c)*N^(-1/2)
          [1+ell*N^(-2/3)+(1/3)N^(-1)+O(N^(-4/3))].

The occupied-parity normalized endpoint is sqrt(2) times this.  The
formula is for the normalized quasimode; transferring it to the actual
eigenvector uses the usual isolated-ground-eigenvalue estimate.  With the
degree-7 certificate its residual is O(e^8), l2 error O(e^6), and endpoint
relative error O(e^(9/2)); hence the displayed terms are preserved.

### Uniform meaning of the frozen residual

For example, multiply the finite sampled profile by a smooth cutoff that is
1 for x<=e^(-1/4), zero for x>=2e^(-1/4).  The Airy tail and all cutoff errors
are smaller than every power of e.  On its support the Taylor remainders are
bounded by e^6 (or e^7/e^8 for the longer certificate) times a fixed polynomial
in x times exp(-a*x^(3/2)), for some a>0.  Squaring and summing over the lattice
costs e^(-1); normalizing the sampled profile contributes e^(1/2).  Hence the
normalized l2 residual has exactly the stated order, without a lost power
from the growing support.  The cutoff lies far below the terminal boundary
x~N^(2/3), so that boundary contributes no error.

## Nonautonomous coefficients

s_2=ell/2,
s_3=-1/3,
s_4=ell^2/24,
s_5=ell/9,
s_6=-(3ell^3+32)/144,
s_7=49ell^2/360.

The first corrections are

G_1=-(x^2/3)F,
G_2=[x(x^3-2)/18]F+(x^2/18)F',
G_3=-[x^2(9ell+x^4-12x)/162]F-(x^4/54)F'.

Full G_4 and G_5 are in the JSON certificate.  Direct substitution checks
both pair components to be zero at every power e^0,...,e^7.

The original-profile endpoint is

f(e,e)/e=1+(ell/6)e^2-e^3/3+(ell^2/120)e^4+O(e^5).

This is not the frozen-profile endpoint; the two gauges describe different
operators and must not be interchanged.

## Formal forward logarithm

Discrete antidifferencing of log(H_N/H_(N-1)) gives

log H_N = constant + N log 2 +(3ell/2)N^(1/3) -(1/3)log N
          +(ell^2/4)N^(-1/3) -(ell/6)N^(-2/3)
          +(1/9)N^(-1) -(ell^2/20)N^(-4/3)+...

After including the endpoint f(e,e),

log d_N(0) = constant + N log 2 +(3ell/2)N^(1/3) -(2/3)log N
              +(ell^2/4)N^(-1/3) +0*N^(-2/3)
              -(2/9)N^(-1) -(ell^2/18)N^(-4/3)+...

At N=2n, a_n=3^n n! d_(2n)(0).  If the amplitude and all-orders stability
theorems are supplied, the resulting forward expansion is

log[a_n/(gamma*n!*12^n*exp(z*(3n)^(1/3))*n^(-2/3))]
 = alpha*n^(-1/3) -(1/9)n^(-1) -(alpha/9)n^(-4/3)+...,
alpha=3^(2/3)z^2/18.

In particular the first three ordinary relative coefficients are
alpha, alpha^2/2, alpha^3/6-1/9.  The absence of the n^(-2/3) logarithmic
term is an exact cancellation, not a numerical fit.

## All-orders recursion and uniqueness

Let L=D^2-(cx+ell).  Suppose the known residual at degree m is RF+SF'.
The new equation, with mu=lambda_m or mu=2s_m, is

L(PF+QF')-mu F+RF+SF'=0.

Eliminating P gives the polynomial operator

TQ=-Q'''/2+2(cx+ell)Q'+cQ.

On x^d its leading coefficient is c(2d+1), which never vanishes.  Thus T
is an invertible triangular map on polynomials of degree <=d.  Solve

TQ=-R+S'/2,
P'=(-S-Q'')/2,
P(0)=-Q'(0).

Then set mu=-cQ(0) and replace Q by Q+mu/c.  This enforces Q(0)=0 without
altering the derivative gauge and produces the unique scalar and profile
correction.  All finite-order forcing terms are polynomials because the
exact coefficient and time-shift series have polynomial coefficients in x.
This supplies an elementary all-orders formal construction, independent of
any unproved integral formula.

## Reproduction and numerical cross-check

Run:

python derive_coefficients.py --order 6
python derive_coefficients.py --order 7
python check_frozen_numerical.py

The exact symbolic script asserts: the polynomial inverse identity; the
two boundary gauges for every correction; the recursive pair equation; and
vanishing of both residual components at every computed degree.

The separate numerical script diagonalizes only the exact tridiagonal
matrix.  At N=20000 it gives lambda=1.997566036632287 and
endpoint/[sqrt(2/3)N^(-1/2)]=0.9975989968783974.  Across N=200,...,20000,
the degree-6 eigenvalue error divided by e^7 stays bounded (1.5903 down to
1.2108), approaching the predicted degree-7 coefficient 41ell^2/120.
The endpoint error after the relative e^3 terms divided by e^4 remains
bounded (1.9444 up to 2.1777).  These are checks, not proof substitutes.
