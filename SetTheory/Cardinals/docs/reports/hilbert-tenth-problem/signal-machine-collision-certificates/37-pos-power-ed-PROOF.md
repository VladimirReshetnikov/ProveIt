# Exact degree of the bounded-halting interpolation polynomial

4 October 2026. This is a separate, unnumbered continuation of the retained
three-witness construction. It does not modify that source or sealed Report 66.
The main result here is an all-horizon algebraic theorem, not numerical evidence.

## 1. Statement and notation

Let K be a positive integer, N=K^2, and c=(N-1)!. Let U,V be the unique rational
polynomials of degree at most N-1 with, for 1<=i<=N,

    U(i)=u_i=ceil(i/K),
    V(i)=v_i=i+K-Ku_i.

Thus U_0=cU and V_0=cV are exactly the integer polynomials in Section 4 of
`dependencies/three_witness_PROOF.md`. We use c for the denominator-clearing
factor, avoiding confusion with polynomial degree. For K>=2 define

    delta_K = K^2-1,  if K is even;
              K^2-2,  if K is odd.

**Exact interpolation theorem.** For every K>=2,

    deg U = deg V = deg U_0 = deg V_0 = delta_K.

Write a_K for the leading coefficient of U_0. Its explicit integer formula is

    a_K = -sum_{h=1}^{K-1} binom(K^2-2,hK-1),            K even;

    a_K = (K^2-1) sum_{h=1}^{K-1}
                        (-1)^(h+1) binom(K^2-3,hK-1),    K odd >=3.

In particular a_K<0 when K is even, and

    sign(a_K)=(-1)^((K+1)/2)                             K odd >=3.

The leading coefficient of V_0 is -K a_K. When K=1, U_0=V_0=1.

**Exact polynomial-degree corollary.** For the precise six-square polynomial
P_(M,T) in the retained construction, put K=T+1 and N=K^2. Its joint total degree
in A,B,j,r,s, for every finite acceptance subset S of {1,...,N}, is

    deg P_(M,0)=2;
    deg P_(M,T)=4(T+1)^2-4,   T positive and odd;
    deg P_(M,T)=4(T+1)^2-8,   T positive and even.

For T>=1 its entire highest homogeneous part is the single monomial

    (1+K^4) a_K^4 j^(4 delta_K).

Consequently the degree is independent of the program, its acceptance table,
and whether acceptance means first halt by T or first halt exactly at T.
There is no artificial degree padding, and no noncancellation assumption.

## 2. Symmetry and the relation between the interpolants

At every node,

    u_(N+1-i)=K+1-u_i.

The two polynomials U(N+1-z) and K+1-U(z) have degree at most N-1 and agree at
all N nodes. Therefore they are identical. Equivalently,

    U((N+1)/2+x)-(K+1)/2

is odd in x. If K is odd, N is odd and N-1 is even, so the coefficient of
z^(N-1) vanishes and deg U<=N-2. This argument is valid over Q even when the
center is a half-integer.

For K>=2, the polynomial z+K-KU(z) has degree at most N-1 and interpolates all
v_i. Uniqueness gives the exact polynomial identity

    V(z)=z+K-KU(z),
    V_0(z)=c(z+K)-K U_0(z).                                 (1)

Once deg U>=2 is proved, (1) implies deg V=deg U and lc(V_0)=-K lc(U_0).
The hypothesis K>=2 matters: the identity need not hold as a degree-zero
polynomial when there is only the node 1.

## 3. Finite differences at block boundaries

For a sequence f_1,f_2,..., let Delta f_i=f_(i+1)-f_i. Repeated expansion gives

    Delta^q f_1 = sum_{k=0}^q (-1)^(q-k) binom(q,k) f_(k+1).

For a polynomial f of degree at most q, its q-th difference is q! times the
coefficient of z^q: taking one difference decreases a degree-q leading term
b z^q to qb z^(q-1), and induction proves the assertion, including lower degree.

The step values satisfy, at every interpolation node,

    u_i=1+sum_{h=1}^{K-1} 1_{i>hK}.

For 1<=b<=q, Pascal's identity telescopes to

    sum_{k=b}^q (-1)^(q-k) binom(q,k)
       =(-1)^(q-b) binom(q-1,b-1).                         (2)

Consequently, whenever q>=1 and all boundaries hK in use satisfy hK<=q,

    Delta^q u_1 = sum_{h=1}^{K-1}
                    (-1)^(q-hK) binom(q-1,hK-1).           (3)

For q=N-1 this condition holds for every K>=2. When K is even, q is odd and
hK is even. Thus (3) is the negative sum of strictly positive binomial
coefficients. Since U has degree at most N-1, this proves

    deg U=N-1,
    lc(U_0)=c Delta^(N-1)u_1/(N-1)!
           =-sum_{h=1}^{K-1} binom(N-2,hK-1).

For odd K>=3, symmetry already gives deg U<=N-2. Set q=N-2. The first N-1
interpolation nodes suffice to compute this difference, and
(K-1)K<=N-2. Both q and K are odd, so (3) becomes

    Delta^(N-2)u_1 = S_K,
    S_K=sum_{h=1}^{K-1} (-1)^(h+1) binom(K^2-3,hK-1).       (4)

If S_K is nonzero, then deg U=N-2 and

    lc(U_0)=c S_K/(N-2)!=(N-1)S_K.

The next section proves its sign for every odd K>=3.

## 4. Strict sign of the odd-K alternating binomial sum

Fix odd K>=3, and write n=K^2-3. Let the K complex roots of r^K=-1 be used
only in the following finite algebraic identity. For any integer m,

    (1/K) sum_{r^K=-1} r^m
       =0                  if K does not divide m;
        (-1)^(m/K)         if K divides m.

Indeed, writing the roots as exp(i*pi/K) times all K-th roots of unity reduces
the assertion to a finite geometric sum. Expanding (1+r)^n therefore gives

    (1/K) sum_{r^K=-1} r(1+r)^n
       =sum_{h=1}^{K-1} (-1)^h binom(n,hK-1)
       =-S_K.                                                (5)

These are exactly all contributing h: 0<=hK-1<=n permits 1<=h<=K-1.
The real root r=-1 contributes zero, because n>0. Pair the other roots as
exp(2i theta_l), exp(-2i theta_l), where

    theta_l=(2l+1)pi/(2K),   0<=l<=(K-3)/2.

All theta_l lie strictly between 0 and pi/2, and

    1+exp(2i theta_l)=2 cos(theta_l) exp(i theta_l).

The real part of r(1+r)^n is therefore

    2^n cos(theta_l)^n cos((n+2)theta_l).

Since n+2=K^2-1,

    cos((n+2)theta_l)
      =cos(K(2l+1)pi/2-theta_l)
      =(-1)^((K-1)/2+l) sin(theta_l).

Substituting these paired terms in (5) yields the exact identity

    S_K = (-1)^((K+1)/2) (2^(n+1)/K)
          sum_{l=0}^{(K-3)/2} (-1)^l
                         sin(theta_l) cos(theta_l)^n.         (6)

It remains to prove that the alternating sum in (6) is strictly positive.
For f(theta)=sin(theta) cos(theta)^n on (0,pi/2),

    f'(theta)=cos(theta)^(n-1)
                  (cos(theta)^2-n sin(theta)^2).

Thus f is strictly decreasing whenever tan(theta)>1/sqrt(n). An elementary
uniform bound places every theta_l in that decreasing interval. Since K>=3,

    n=K^2-3 >= (2/3)K^2,
    1/sqrt(n) <= sqrt(3/2)/K < 3/(2K) < pi/(2K)=theta_0.

The strict middle inequality follows by squaring sqrt(3/2)<3/2, and the last
uses pi>3. Also tan(theta)>theta for 0<theta<pi/2, since the derivative of
tan(theta)-theta is tan(theta)^2>0 and its value at zero is zero. Consequently

    tan(theta_l)>1/sqrt(n)

for every l. Hence f(theta_0)>f(theta_1)>...>0.

Any finite alternating sum of a strictly decreasing positive sequence,
beginning with its positive term, is strictly positive: pair successive terms
as (f_0-f_1)+(f_2-f_3)+..., adding the positive final term if unpaired. This
includes K=3, when there is just one term. Formula (6) now proves

    (-1)^((K+1)/2) S_K > 0.                                  (7)

Equations (4) and (7) complete the exact interpolation theorem. Its minimum
degree for K>=2 is 3, attained at K=2, so the use of (1) is justified.

## 5. Exact degree of the six-square polynomial

For clarity, retain the source's entire formula. For arbitrary
S subset {1,...,N}, set

    R(j)=product_{i=1}^N (j-i),
    H_S(j)=product_{i in S}(j-i),

with the empty product equal to 1, and

    R_A=(cA-U_0(j))(U_0(j)-cK),
    L_A=cA-U_0(j)-c(r-1),
    R_B=(cB-V_0(j))(V_0(j)-cK),
    L_B=cB-V_0(j)-c(s-1),

    P=R^2+R_A^2+L_A^2+R_B^2+L_B^2+H_S^2.                    (8)

Let K>=2 and delta=delta_K. Because delta>=3, the highest homogeneous terms of
the classification residuals are respectively

    -a_K^2 j^(2delta),
    -K^2 a_K^2 j^(2delta).

In particular the A U_0 and B V_0 terms, of joint degree delta+1, cannot
compete with the squared-interpolant terms of degree 2delta. Squaring these
two residuals gives highest terms

    a_K^4 j^(4delta),
    K^4 a_K^4 j^(4delta).

The remaining four squared residuals have degree at most 2N,2delta,2delta,2N.
For even K>=2,

    4delta-2N=2N-4>0;

for odd K>=3,

    4delta-2N=2N-8>0.

Thus none of them contributes in degree 4delta. The entire top homogeneous
part is exactly (1+K^4)a_K^4 j^(4delta), whose coefficient is strictly positive.
This proves both the exact joint degree and its independence of S, including
empty and full tables.

For K=1, c=1 and U_0=V_0=1. The classification residuals vanish identically and

    P=(j-1)^2+(A-r)^2+(B-s)^2+H_S(j)^2,

where H_S is either 1 or j-1. Both possibilities have joint degree two.

## 6. Consequences and scope

1. The earlier upper bound 4(T+1)^2-4 is attained exactly at odd positive T.
   It exceeds the actual degree by exactly four at even positive T.
2. The original native-gap composition has degree max(12,deg P), because its
   two degree-twelve POWER monomials involve independent module variables.
   Thus it has degree 12 at T=0 and the exact degree above at every T>=1.
   This uses the literal retained POWER residuals for degree accounting only;
   the interpolation theorem needs no Pell or physical theorem.
3. The source's support argument can use delta in place of N-1. Since
   2N<4delta for K>=2, its same disjoint monomial types give at most
   16delta+11 monomials. This is 16N-5 for even K and 16N-21 for odd K>=3.
   It is a support ceiling, not an exact support count.
4. All witnesses, equations, correctness statements, and uniqueness properties
   remain those of the retained construction. This theorem sharpens only its
   algebraic degree accounting. The horizon still indexes a changing family.
   No fixed-polynomial unbounded-halting, minimality, novelty, or priority
   claim is made.

## 7. Independently authored finite evidence

The fresh `exact_degree_check.py` is displayed and read in full before running.
It uses integer finite-difference tables and a Newton-basis reconstruction,
independently of the retained Lagrange checker. It checks the degree and both
boundary formulas for K=1,...,40, including both signs, and reconstructs full
cleared interpolation polynomials for K=1,...,9. It verifies every node,
reflection symmetry, and identity (1). It fully expands (8) for declared
acceptance subsets for K=1,...,7, checking the complete highest homogeneous
part, exact degree, and sharpened support ceiling. For K=1,2 it covers every
acceptance subset.

The checker receives explicit arrays u_i,v_i and literal acceptance subsets.
It runs no counter program, machine interpreter, physical simulator,
source-packet script, upstream implementation, or Lean. It does not use
floating-point trigonometry to certify (7); the all-K sign proof is Section 4.
Finite evidence supports, but does not replace, the proof.

The source proof, its dependencies, and its checker were read as inert text.
Unchanged copies of the proof and retained dependency records accompany this
packet. Their origins and hashes are in `SOURCE_PINS.json`; the source-packet
inventory hashes before and after work agree. No earlier source or sealed
report is edited. This continuation awaits independent review.
