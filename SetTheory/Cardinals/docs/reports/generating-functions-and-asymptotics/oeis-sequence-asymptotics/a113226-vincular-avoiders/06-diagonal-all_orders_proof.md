# A113226: complete dominant saddle expansion and inversion

This note continues exact_egf_proof.md. Put rho=log4, b=pi/sqrt(rho), a=(b/2)^(2/3), and T0=rho/2-3. Then

A(z)=exp(T(z)), T(z)=z/2+[pi-3 arctan(w)]/w,
w=sqrt(4 exp(-z)-1),                                             (1)

where the branches agree with positive real w for 0<z<rho. Consequently, with delta=rho-z,

T(z)=pi delta^(-1/2)+T0-(pi/4)delta^(1/2)+delta/2+O(delta^(3/2)).   (2)

The full convergent local expansion is obtained from

T(rho-delta)=(rho-delta)/2+pi/sqrt(exp(delta)-1)
             -3 sum_(j>=0) (-1)^j(exp(delta)-1)^j/(2j+1).         (3)

## Analytic continuation and minor arcs

The exact integral also has the form

T(z)=z int_0^1 exp(zv)/[1-(exp(zv)-1)(exp(z(1-v))-1)]dv.           (4)

For |z|=r<rho and v in [0,1],

|(exp(zv)-1)(exp(z(1-v))-1)|
 <=(exp(rv)-1)(exp(r(1-v))-1)
 <=(exp(r/2)-1)^2<1.

The second inequality follows by writing the product as exp(r)+1-exp(rv)-exp(r(1-v)). On |z|=rho, equality in the last bound requires v=1/2. At v=1/2, equality in the first bound requires z to be positive real: equality in |exp(z/2)-1|<=exp(|z|/2)-1 requires the degree-one and degree-two terms to have the same argument, hence arg z=0. Thus (4) continues analytically through every point of |z|=rho other than rho, uniformly on compact subsets.

Formula (1), or equivalently (3), gives a slit neighborhood of rho, with the square root chosen by delta^(1/2)>0 on the positive real axis. By compactness and uniqueness of analytic continuation, there is an epsilon>0 such that A is analytic in |z|<rho+epsilon slit along the real interval [rho,rho+epsilon). Here epsilon is fixed and small; no global assertion about farther branches is needed.

Use the Cauchy contour formed by the left part of |z|=rho+epsilon and its vertical chord Re z=r=rho(1-a n^(-2/3)). The chord crosses the positive real axis at r and excludes the slit. Its endpoints stay a fixed positive distance from rho. The outer arc is exponentially smaller than rho^(-n)exp(3a n^(1/3)).

On the vertical chord write z=r+iy. For |y| small, (2) gives

Re T(r+iy)<=pi (rho-r)^(-1/2)
 -c (rho-r)^(-1/2) min{ y^2/(rho-r)^2,1 }+C,                    (5)

with positive constants c,C independent of n. Indeed
Re(1-it)^(-1/2)<1 for t!=0, with deficit comparable to min(t^2,1); the remaining analytic-in-sqrt(delta) terms are bounded. Also |r+iy|>=r. Thus the part |y|>=n^(-5/6+eta), for any fixed small eta>0, is exponentially small relative to the central integral, with loss exp(-c n^(2eta)); farther fixed portions have loss exp(-c n^(1/3)). This supplies the needed minor-arc estimate rather than relying on real-axis singular behavior alone.

## Finite coefficient algorithm and all-orders error

Let h=n^(-1/6), gamma=sqrt(2a/3), and put

u(h,v)=a h^4+i gamma h^5 v.

Changing the orientation of the vertical chord if needed, its central contribution is obtained by setting z=rho(1-u(h,v)). Define the formal series

R(h,v)=T(rho(1-u(h,v)))-(h^(-6)+1)log(1-u(h,v))
       -3a h^(-2)-T0+v^2/2.                                   (6)

The negative powers cancel and R belongs to h C[v][[h]]. Its coefficient of h^j is an even polynomial in v when j is even, and an odd polynomial when j is odd. Define

c_j = (1/sqrt(2pi)) int_R exp(-v^2/2)[h^(2j)]exp(R(h,v))dv.       (7)

This is a finite algorithm: only finitely many terms of (3) and (6) are used, and Gaussian monomials integrate to zero in odd degree and (2k-1)!! in degree 2k. In particular c0=1 and

c1=a^2(1-rho)/2-5/(36a).                                        (8)

For every fixed K,

a_n/n! = C rho^(-n) exp(3a n^(1/3)) n^(-5/6)
          [sum_(j=0)^K c_j n^(-j/3)+O_K(n^(-(K+1)/3))],          (9)

C=exp(T0)sqrt(a/(3pi)).

To justify (7)-(9), use the central window |v|<=h^(-eta) for a sufficiently small fixed eta>0. In that window the Taylor expansion of the convergent expression (3), followed by that of the exponential, has, at every fixed order J, a remainder bounded by h^(J+1) times a fixed polynomial in |v| times exp(C h |v|^3). Since h|v| is small, the local exponent remains <=-v^2/4 after its Gaussian factor is included; this also follows directly from (5). The remainder is therefore integrable with O(h^(J+1)) total size. Expand through J=2K+1. Odd terms integrate to zero on the symmetric window, and extending each polynomial-Gaussian integral to the real line costs less than every power of h. Formula (5) controls the discarded part. The Jacobian is rho gamma h^5, while the factor 1/z has already been included in (6). Its leading constant is gamma/sqrt(2pi)=sqrt(a/(3pi)), as stated.

This proves the leading equivalent, its all-orders expansion, and the following exact constants in the 2025 conjectured form:

beta=-5/6,
mu=exp(3a)=37.92669385021515729525...,
C=0.03570604125804483339....

The previously fitted amplitude near .032 is not asserted to equal this constant; its finite-data convergence is affected by c1=-.39827424329477706556... and later terms.

## Inversion with an integer threshold

Let y tend to infinity and define N(y)=min{n:a_n>=y}. Eventual monotonicity follows from (9) with, for example, K=4: a_(n+1)/a_n~n/rho. For a fixed K, use the positive smooth tail model

f_K(x)=Gamma(x+1) C rho^(-x) exp(3a x^(1/3)) x^(-5/6)
          sum_(j=0)^K c_j x^(-j/3).

It is strictly increasing for all large x, since its logarithmic derivative is log(x/rho)+O(x^(-2/3)). Let x_K(y) be its large inverse. Then there is C_K'>0 such that

ceil(x_K-epsilon_K)<=N(y)<=ceil(x_K+epsilon_K),
epsilon_K=C_K' x_K^(-(K+1)/3)/log x_K.                           (10)

The proof is a mean-value comparison between the logarithmic model error O(x^(-(K+1)/3)) and its derivative. Exact rounding is valid when the inverse model is farther than epsilon_K from the integers; no arbitrary interpolation of a_n is needed.

For a formal explicit inverse, let X solve log Gamma(X+1)-X log rho=log y, and let Psi(X)=psi(X+1)-log rho. Put

q(X)=3a X^(1/3)-(5/6)log X+log C+log(sum_(j>=0)c_j X^(-j/3)).

The compatible finite-order inverse expansion is generated by

x ~ X+sum_(k>=1) (-1)^k/k! [(1/Psi)d/dX]^(k-1)[q(X)^k/Psi(X)].   (11)

Here the first displacement is of order X^(1/3)/log X, which is small compared with X, and each additional reversion term decreases asymptotically. In particular

x=X-[3a X^(1/3)-(5/6)log X+log C+c1 X^(-1/3)]/Psi(X)
    +3a^2 X^(-1/3)/Psi(X)^2
    -(9a^2/2)X^(2/3)Psi'(X)/Psi(X)^3
    +O(X^(-2/3)/log X).                                        (12)

The stated remainder includes the omitted c2 term and the smaller cross terms in q q'/Psi^2-q^2 Psi'/(2Psi^3). Each finite truncation can instead be specified without bookkeeping ambiguity by (10)-(11).
