# A second Pell root removes the native quotient

Prepared for the ProveIt research iteration of 25 October 2026, with AI assistance.
This is a new arithmetic reduction of the exact incoming first-Pell carrier.
The immutable comparison revision is b42c796d1f5de9912a576bc2fd77b778ae7402bf.
The parent is docs/incoming/ConZFC_Pell_Carrier65_2026-10-25.zip, whose
equation/carrier65.json has been retained as parent65.json. The new equations
retain its complete admissible942 fixed tuple; no coefficient is mixed with
the indexed943 tuple of source 170.

## Complete formula

The thirteen independent inputs are positive integers, in JSON order

    J,F,alpha,f,i,T,s,w,n,eta,zeta,m,gamma.

The fixed integers beta,K0,MC,MF are exactly those of the parent. Define

    h=beta J, q=h+1, C=q-F-alpha,
    X=wq, Y=sq^3, E=XY, k=eta+zeta,
    ell=EkY, c=kY+eta, a=E+Y, H=4a+3,
    Delta=a^2+H=(a+2)^2-1, D=X+ac+gamma H,
    R=[h(q-F)+alpha](q^2-1)+(MC+q MF)J,
    tau=En+k-R, B=(K0+w)C-F,
    b=cT-R, V=f^2 b-c, S=h i Delta c^2.

For the main equation put L=V^2; for the companion put L=bV. Define

    y=1+4[h(m-LB)-B],
    N0=tau^2-ell(ell+k), N1=D^2-Delta c^2,
    Na=S^2(V^2-y^2)+y^2, Ns=Delta f^2-S^2.

The requested single polynomial is

    P=N0 N1 Na Ns-Delta.

All these names are polynomial abbreviations. In particular y is a signed
polynomial value, not an extra positive variable. No variable exponent,
division, floor, factorial, or unspecified predicate occurs in P.

The literal main evaluator has 69 live operations and exact degree 174.
The companion has 70 operations and exact degree 170. Both have thirteen
positive unknowns. The main unrestricted-integer lift has 39 unknowns,
160 operations, and exact degree 348. The companion lift has 39 unknowns,
161 operations, and exact degree 340.

## 1. A strong residue of every odd Pell ordinate

Let S>=2 be an integer, and write

    chi_S(r)+psi_S(r)*sqrt(S^2-1)=(S+sqrt(S^2-1))^r.

For every j>=0,

    psi_S(2j+1) = (-1)^j mod 4S^2.                    (1)

Indeed the odd subsequence satisfies u_(j+2)=(4S^2-2)u_(j+1)-u_j,
with u_0=1 and u_1=4S^2-1. Reduction modulo 4S^2 and induction give (1).
This modulus, including its factor 4, is essential: congruence only modulo
S^2 would not select a sign when S is odd.

Suppose integers V,y satisfy

    S^2 V^2-(S^2-1)y^2=1.                             (2)

Neither V nor y is zero. Positive solutions of x^2-(S^2-1)u^2=1 are
(chi_S(r),psi_S(r)) for r>=1. This classification follows by multiplying
by S-sqrt(S^2-1): when u>1, the new ordinate Su-x is positive and smaller
than u, and the new abscissa Sx-(S^2-1)u is positive. The inequalities
sqrt(S^2-1)<x/u<S give the decrease; positivity of the abscissa follows
from sqrt(S^2-1)>(S^2-1)/S. The terminal positive solution is (S,1).
Applying this to x=S|V| and u=|y| gives an index r. The recurrence for chi
modulo S shows that its even-index values are +1 or -1 modulo S, whereas
its odd-index values are 0. Since S divides x, r is odd. Hence, by (1),

    y = +1 or -1 mod 4S^2.                            (3)

If in addition y=1 mod4, the minus sign in (3) is excluded. Therefore

    4S^2 divides y-1.                                (4)

Finally (2) gives the uniform strict bound |y|<2|V|.
These statements cover both signs of V and y and require no encoded rank.

## 2. Unit signs without the deleted native factor

All inputs are positive. In particular h>=31, c>1, Delta>1 and S>c.
Since Ns=Delta[f^2-Delta(hic^2)^2], cancel Delta from P=0. The product
of the four integer factors N0,N1,Na,Ns/Delta is one, so each is a unit.

The consecutive-product Pell obstruction from the parent excludes N0=-1:
ell(ell+k)=EY(EY+1)k^2, with EY>=2. This does not assume tau positive.
Delta is 0 or3 modulo4, excluding -1 for N1 and Ns/Delta. Since S^2 is
0 or1 modulo4, Na is congruent to y^2 or V^2 modulo4 and cannot be -1.
Thus

    N0=N1=Na=1,       Ns=Delta.                       (5)

No conclusion about C, R, B, or the first index was used. In particular
Na=1 is equation (2), and the polynomial y is 1 modulo4. Formula (4)
applies. Since h divides S,

    h^2 divides h(m-LB)-B,

and therefore h divides B. This conclusion does not require h odd or prime.

## 3. Recovering the sign of the deleted quotient

For L=V^2 we have L>=|V|>=1. For the companion L=bV the same inequality
holds at a zero: if b=0, then V=-c and (2) would imply

    y^2-c^2=(c^2-1)/(S^2-1),

strictly between zero and one, impossible for integers. Moreover (5) gives
f^2=1+Delta h^2 i^2 c^4>c. Thus V=f^2b-c has the sign of nonzero b,
and bV=|b||V|>=|V|.

Write W=1+hL, which is positive. If B<=-1, then positivity of m gives

    y=1+4(hm-WB) >= 1+4(h+W) >4hL >=4|V|,

contradicting |y|<2|V|. Consequently B>=0. Set

    z=B/h+1,

a positive integer. The deleted factor of the parent is restored exactly:

    Nt=(K0+w)C+(q-F)-zh=B+q-zh=1.

Keep the remaining parent inputs, replace its i by hi, and replace its
positive y by |y|. Every parent factor then has its required value, and
its Carrier65 polynomial is zero. This is the soundness map. It invokes
no unproved source conclusion to recover C or R; those are recovered by
the already proved parent only after this map is complete.

## 4. Positive completeness with a fresh strong Pell seed

A finite syntactic ZFC refutation gives the exact parent's canonical outer
data. In particular N0=N1=1, R=3 mod4, c=psi_(a+2)(R), X=2^R,
C>0, F<q, h divides B, and R>q(q^2-1). The source's first-carrier input
n is positive. These data do not depend on the private strong seed f,i
or the auxiliary coordinates T,y.

We first note the strict inequality B>0. Indeed R>q(q^2-1) and q>=32
imply 2^R>q^2, hence w=X/q>q. Since C>=1 and F<q,

    B=(K0+w)C-F > w-q >0.                            (6)

Choose a positive Pell solution f^2-Delta I^2=1 with hc^2 dividing I.
Such solutions exist cofinally: in the finite ring
(Z/(hc^2)Z)[t]/(t^2-Delta), the unit a+2+t has a finite multiplicative
order, because its norm is one. A positive multiple of that order gives
I=0 modulo hc^2, and its positive powers give arbitrarily large choices.
Set i=I/(hc^2)>0 and S=Delta I. Then our Ns equals Delta.

Set V*=chi_S(R)/S and y*=psi_S(R). The numerator chi_S(R) is divisible
by S because R is odd, so these are positive integers. The same elementary
polynomial identities used in the parent's fresh-ordinate completeness give

    V*=-c mod f^2,          V*=-R mod c.

For completeness, if R=2j+1, write chi_S(R)/S=Q_j(S^2). The identities
Q_j(1-A^2)=(-1)^j psi_A(R), Q_j(0)=(-1)^j R, with A=a+2,
give these congruences because S^2=1-A^2 mod f^2, c divides S, and j is odd.
Also gcd(c,f)=1 and f^2=1 mod c. Hence

    T=(V*+c+Rf^2)/(cf^2)>0

is an integer and our V is V*. In this sentence the quotient is part of
the witness construction, not an operation in the polynomial.

By (1), y*=-1 modulo 4S^2. Set the signed target y=-y*, so y=1 modulo
4S^2. For L=V^2, or L=bV in the companion, define

    m=(y-1)/(4h)+(1+hL)B/h.                          (7)

This is an integer: h divides B and 4h divides y-1. It is strictly
positive. Indeed B is a positive multiple of h by (6), and L>=V>=1;
using |y|<2V gives

    m > -(2V+1)/(4h)+1+hL >0.

Equation (7) makes the literal polynomial carrier equal the signed y.
All four factors in (5) have the required values, and P=0. This proves
positive zero existence from the finite refutation.

The construction is existential; it does not identify all parent and child
zeros. It deliberately changes the strong Pell seed and the auxiliary pair.

## 5. Integer domain and exact arithmetic size

For each of the thirteen positive coordinates substitute

    1+u^2+v^2+w(w+1),       u,v,w unrestricted integers.

This parametrizes every positive integer. Indeed the classical three-square
theorem applied to 4N+1 shows that each N>=0 is u^2+v^2+w(w+1): among
three squares summing to 4N+1 exactly one is odd, and subtracting its 1
and dividing by4 gives the stated representation. Conversely the expression
is nonnegative for all integer u,v,w. The standard domain translation has
three independent integers and seven arithmetic operations per coordinate.

Thus the main equation has 39 unrestricted integers and 69+13*7=160
operations. The degree doubles to348; the companion has degree340 and
161 operations. No claim is made that either is a minimum among other
integer-domain constructions.

Relative to Carrier65, delete the three rows producing the final Nt from
the already computed (K0+w)C, add the single B subtraction, delete one
output multiplication, add one multiplication scaling i by h, and add
the six-row y carrier. The net change is -3+1-1+1+6=+4 operations:
65 becomes69. L=bV adds one multiplication.

The exact factor degrees for L=V^2 are N0:22, N1:18, Na:86, Ns:48,
giving174. For L=bV the Na degree is82, giving170. The N1 degree uses
the exact cancellation

    (ac+Z)^2-(a^2+H)c^2=2acZ+Z^2-Hc^2,

where Z=X+gamma H. With q0=beta J and k0=eta+zeta, the full leading
form of the main equation is

    -128 q0^99 gamma i^4 k0^15 w^14 s^27 f^8 T^4
         (q0-F-alpha)^2.

The companion leading form is

    -128 q0^99 gamma i^4 k0^15 w^14 s^27 f^4 T^4
         (q0-F-alpha)^2.

These formulas, the actual DAG, all coefficient bytes and specialization
to the fixed numerical tuple are independently checked by verify.py.
The coefficient of the term choosing eta in k0 and -F in the last factor
is -128 beta^99, so the degree remains exact for every positive beta.

## 6. Scope and comparison

The proof composes with the exact parent's admissible942/native/K215/ZFC
refutation calibration. It establishes in ordinary mathematics formalizable
inside ZFC that P has a zero exactly when a finite syntactic ZFC refutation
exists. Negating yields the requested ZFC-provable equivalence of no integer
zero of the lifted polynomial with Con(ZFC).

Finite checks authenticate polynomials and coefficients; they do not decide
consistency or replace unbounded Pell or logical calibration proofs. No
fresh complete Lean/Rocq or encoded object-language derivation is claimed.

Source170 already uses an auxiliary Pell ordinate as a quotient carrier.
Its 13-positive-variable profiles include 70 operations/degree206 and
71/162, using the indexed943 tuple. The present result instead uses the
factor4 in the odd-ordinate residue to recover the native transport quotient,
proves its sign without rank recovery, and composes with the new first-root
Carrier65. Its main count is69/174 on the smaller admissible942 tuple.
This is a measured arithmetic tradeoff, not worldwide priority or global
simplicity. The inherited first carrier and native source improvements are
explicitly credited.
