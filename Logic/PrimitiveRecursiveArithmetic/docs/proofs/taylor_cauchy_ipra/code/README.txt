EXACT-ARITHMETIC VALIDATION ARTIFACTS
===================================

Run with Python 3.10 or later; only the standard library is required:

  python3 validate_exact.py --output validation.json

Every asserted equality and comparison uses fractions.Fraction, including
the complex arithmetic. Decimal strings in the JSON are display-only.
Numerator/denominator strings are the authoritative exact numbers.
The output is deterministic. No random data, floating point quadrature,
network requests, or external packages are used.

These are finite examples and arithmetic validation artifacts. They are not
formal proofs of the universal theorems, not a proof checker for iPRA, and
not substitutes for the paper's mathematical argument.

WHAT IS CHECKED
--------------

1. Finite telescoping, summation by parts, finite geometric expansion,
   the Taylor product decomposition, first- and second-difference bounds
   for w_j(t)=(1-t)^j/j!, and the exact quotient remainder identity.
2. Exact affine complex line integration by the trapezoid rule, cancellation
   around rational triangles, and four-way midpoint subdivision.
3. Taylor's exact integral remainder for 54 polynomial/order/endpoint
   choices, including reversed and equal endpoints. Polynomial integration
   is exact coefficient arithmetic. The factorial remainder bound is also
   checked using a conservative coefficient bound.
4. The literal finite Taylor certificate with a common sample precision:

   |E_0(1,p)-sum_{j<=n} E_j(0,p)/j!
      -(1/N)sum_{i<N} w_n(i/N)E_{n+1}(i/N,p)|
   <= (n+1)2^(-r)+(n+1)(2N+1)2^(-p)+C/N,

   C=sum_{j<=n}(beta_j+beta_{j+1}+2).

   The example uses f(t)=1+t+t^2+t^3, n=2, N=64, p=16, r=4.
   All sample-error, derivative-remainder, local-cell and final-error
   hypotheses are checked as exact rational inequalities. The necessary
   evaluation error proportional to N is included.
5. A certified quadrature illustration of the circle Cauchy formula for
   f(z)=1+z+z^2 at a=1/4+i/8, with N=64 and 128 per quarter circle.

RATIONAL CIRCLE PARAMETRIZATION AND CERTIFICATE
---------------------------------------------

The positively oriented unit circle is traversed in four rational pieces

  gamma_q(t)=i^q beta(t),  beta(t)=(1+it)/(1-it),
  0<=t<=1, q=0,1,2,3.

The endpoint matching is exact. Algebra gives |beta|=1 and

  beta'=2i/(1-it)^2, beta''=-4/(1-it)^3,
  beta'''=-12i/(1-it)^4.

Thus the Euclidean bounds |gamma'|<=2, |gamma''|<=4, |gamma'''|<=12
hold. On the circle |z-a|>=1-|a|>=5/8=:d. For g(z)=f(z)/(z-a),

  |g|  <= 3/d = 24/5,
  |g'| <= 3/d+3/d^2 = 312/25,
  |g''|<= 2/d+6/d^2+6/d^3 = 5392/125.

For H_q(t)=g(gamma_q(t))gamma'_q(t), the product/chain rule yields

  H_q'' = g''(gamma_q)(gamma'_q)^3
           +3g'(gamma_q)gamma'_q gamma''_q +g(gamma_q)gamma'''_q,
  |H_q''| <= 8(5392/125)+24(312/25)+12(24/5)
           =87776/125=:M_2.

The composite trapezoid rule on [0,1] with N equal cells has error at
most M_2/(12N^2). This is the integral of the elementary second-derivative
error kernel, and holds componentwise / in the Euclidean norm. Summing
four quarters gives contour quadrature error M_2/(3N^2).

Define pi constructively by pi=4*integral_0^1 1/(1+t^2) dt. For
v(t)=1/(1+t^2),

  v''=(6t^2-2)/(1+t^2)^3,
  |6t^2-2|<=2+6t^2<=2(1+t^2)^3,

so |v''|<=2. If P_N is four times its rational trapezoid sum, then

  P_N-2/(3N^2) <= pi <= P_N+2/(3N^2).

The target value uses P_N: T_N=2 P_N i f(a). Here
f(a)=83/64+3i/16 and |f(a)|<=|Re f(a)|+|Im f(a)|=95/64. Thus

  |Q_N - T_N| <= [M_2/3 + 95/48]/N^2,

where Q_N is the four-quarter rational trapezoid sum. The JSON contains
Q_N, T_N, their exact rational difference, its squared Euclidean norm,
the exact rational error bound B_N, and the checked comparison

  (Re(Q_N-T_N))^2+(Im(Q_N-T_N))^2 <= B_N^2.

WHY THE POLYNOMIAL CIRCLE IDENTITY IS INDEPENDENTLY ELEMENTARY
------------------------------------------------------------

Polynomial division gives

  f(z)/(z-a) = z+(1+a)+f(a)/(z-a).

The polynomial terms integrate to zero by endpoint cancellation of their
explicit primitives. For the shifted kernel, the finite geometric identity
gives, for every m>=1,

  1/(z-a)=sum_{k=0}^{m-1} a^k/z^(k+1)
            +a^m/[z^m(z-a)].

The k>=1 terms have explicit single-valued primitives and integrate to
zero. The remaining tail has contour-integral norm at most
8(3/8)^m/(5/8), since the four parametrizations have total length at most
8. This explicit geometric error tends to zero with a PR rate. Finally

  beta'/beta=2i/(1+t^2)

on each quarter, so the k=0 integral is exactly 2 pi i. This establishes
the particular polynomial identity underlying the quadrature certificate
without using the general Cauchy theorem as a black box.

The derivative and quadrature-error arguments above are human mathematical
proofs of the certificate bounds. The executable checks the stated finite
instances and exact rational comparisons; it does not formalize those
general derivative or integration arguments.
