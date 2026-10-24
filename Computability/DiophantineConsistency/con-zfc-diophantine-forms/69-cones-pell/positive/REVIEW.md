# Independent internal review of the degree-82 construction

This note records a separate mathematical review of the new Pell-integrality
argument, its use in the norm merger, the positivity order, and the exact-degree
calculation. It is an internal review by another reasoning process in the same
assisted research session, not external peer review or a proof-assistant
certificate. The native compiler and refutation calibration remain the named
upstream dependencies of package 61.

## 1. Integral-coordinate saturation for consecutive Pell coefficients

**Lemma.** Let Q be an integer greater than 1. If V is an integer, y is a
rational number, and

    Q V^2 - (Q-1) y^2 = 1,

then y is an integer.

**Proof.** The equation excludes V=0 and y=0. Changing signs separately,
assume V>0 and y>0. Write y=a/m in lowest terms, with m>0. Clearing
denominators shows

    (Q-1) a^2 = m^2 (Q V^2-1).

Since gcd(a,m)=1, it follows that m^2 divides Q-1. In particular, m divides
Q-1. Define

    V' = (2Q-1)V - 2(Q-1)y,
    y' = (2Q-1)y - 2QV.

The first coordinate is an integer. Direct expansion, using

    (2Q-1)^2 - 4Q(Q-1) = 1,

gives the same norm equation for V',y'. If V>1, then

    y^2 - V^2 = (V^2-1)/(Q-1) > 0,
    (QV)^2 - ((Q-1)y)^2 = Q V^2 + Q-1 > 0.

Thus y>V and QV>(Q-1)y. Substitution into the formula for V' yields

    -V < V' < V.

Moreover, V' is nonzero, since otherwise the preserved norm equation would
give -(Q-1)y'^2=1. The numerator of y', with denominator m, is

    (2Q-1)a - 2QVm.

Modulo m it equals a, because Q is congruent to 1 modulo m. Hence it is
coprime to m: the reduced denominator of y' is exactly m. Applying absolute
values again and repeating strictly decreases the positive integral first
coordinate while preserving the reduced denominator. The process must reach
V=1, where the norm equation forces y^2=1 and therefore m=1. This proves the
lemma.

The proof also covers Q=2; there is no hidden assumption that Q is a square.
It requires Q to be an integer. No coprimality condition involving another
denominator coefficient is needed. The argument is elementary Pell descent;
this review makes no claim that the lemma is new to the literature.

## 2. Exact norm merger, without coprimality hypotheses

Let d,rho be positive integers, Q>1 an integer, and n,V integers. Put

    h(u) = (1-Q)u^2 + 2(1-Q)Vu + V^2-1,
    a = h(n),
    b = 2(1-Q)(n+V),
    A = d a + (1-Q)rho,
    N = A^2 - d b^2 rho.

Assume b is nonzero. If N=0, define the rational numbers

    i = A/(d b),
    u = n-i.

Then d i^2=rho. Also

    h(n-i) = a-bi+(1-Q)i^2
           = a-A/d+(1-Q)rho/d
           = 0.

Writing y=V+u, the latter equality is exactly

    Q V^2 - (Q-1)y^2 = 1.

The lemma proves that y, hence u and i, are integers. This establishes the
nontrivial integrality direction. Conversely, if integers i,u satisfy
d i^2=rho, h(u)=0, and n=i+u, substitution gives A=d b i and N=0. A useful
equivalent polynomial identity is

    N |_(rho=d i^2) = d^2 h(n-i) h(n+i).

The identity by itself would only recover rational candidates; the Pell
lemma supplies the required integral-coordinate conclusion.

## 3. The application has no unexamined zero-denominator branch

The release uses exactly twelve strictly positive integer inputs and defines

    f=t+1, rho=f^2-1, d=Delta c^4, Q=Delta rho,
    V=f^2(cT-R)-c.

Here c=(eta+zeta)Y+eta and Delta=(XY+Y+2)^2-1. Consequently c>=3,
f>=2, rho>=3, Delta>=15, and Q>1 without using any equation.

The two unchanged source-61 carrier equations A0=A1=0 imply c>2R before
using either the strong Pell equation or the auxiliary Pell equation. This
order was checked against the source-61 proof: the first carrier gives
C>0, q^3|Y, and 3q<R<q^4-2; the second supplies the main Pell root. The
first norm then excludes its initial index and gives

    c>8XY^3>=8q^9>2R.

Since T>=1, one has cT-R>c/2. Therefore

    V>f^2 c/2-c>=c>1.

For n>0 it follows that b=2(1-Q)(n+V)<0. Thus b is nonzero at every
candidate zero after the two carrier equations have been recovered. The
merger never divides by an unproved nonzero expression.

If the recovered integers i,u have arbitrary signs, replace them by

    i_positive=|i|,
    u_positive=|V+u|-V.

The first is positive because d i^2=rho>0. The second is positive because
V>1 and

    (V+u)^2-V^2=(V^2-1)/(Q-1)>0.

The two Pell equations remain true. Thus the new equation produces a
strictly positive source-61 solution with f=t+1 and j_source=2j. No sign
assumption on the initially recovered i or u is required.

## 4. Product combination and canonical completeness

The chosen J=6j+1 is odd and beta is odd, so q=beta J+1 is even. Both
carriers are squares modulo 4. The merger N is a square modulo 4 because
b is even. Hence

    (1+A0)(1+A1)(1+N)=1

forces A0=A1=N=0: each integral factor must be 1 or -1, and a factor -1
would require a residual equal to -2, which is not a square modulo 4.

For the reverse existence implication, source-61 canonical witnesses have

    J=1+B+...+B^(N-1),

with B even, B=-1 modulo 3, and N odd. Thus J is odd and J=1 modulo 3,
so J=1 modulo 6. Since J>1, j=(J-1)/6 is a positive integer. Retain the
source strong solution f,i and set t=f-1 and n=i+u, where u is the positive
auxiliary witness supplied by source 61. These are positive. The two
carrier equations are unchanged, while the identity in section 2 gives
N=0. No additional doubling of the strong Pell index or new congruence
condition on f is needed.

## 5. Exact degree and a surviving monomial

All twelve inputs have degree 1 and the four fixed integer ports degree 0.
Write

    q0=6 beta j, k0=eta+zeta, c0=k0 Y,
    Delta0=X^2 Y^2,
    R0=q0^3(q0-F),
    Bt0=(K0 q0+X)(q0-F-alpha)-q0 F.

The exact degrees of d,rho,Q,V,a,b,A are respectively

    12, 2, 6, 6, 13, 12, 25.

Their relevant homogeneous leaders are

    d0=Delta0 c0^4,
    Q0=Delta0 t^2,
    V0=-t^2 R0,
    a13=-2 Q0 V0 n,
    b12=-2 Q0 V0,
    A25=2 Delta0^2 c0^4 t^4 R0 n.

Since d b^2 rho has degree 38, it cannot cancel the degree-50 term of A^2.
Therefore

    in_50(N)=4 Delta0^4 c0^8 t^8 R0^2 n^2.

The source carrier leaders, unchanged by replacing 3j+1 with 6j+1, are

    in_15(A0)=-2 q0^8 k0^2 X Y^2 Bt0,
    in_17(A1)= 8 q0^10 k0 X^2 Y^3 gamma.

Their product with the merger leader yields

    in_82(P12)=
      -64 q0^24(q0-F)^2 k0^11 X^11 Y^21 t^8 n^2 gamma Bt0.

In particular, the coefficient of

    j^24 F^2 eta^11 X^12 Y^21 t^8 n^2 gamma alpha

is 64(6 beta)^24>0. To achieve the indicated minimal j exponent, the
factor (q0-F)^2 must contribute F^2 and Bt0 must contribute -X alpha.
This gives a direct noncancellation certificate independent of the values
of K0, MC, and MF. The degree is exactly 82, not just bounded by 82.

## 6. Scope of the review

The mathematical merger, all new denominator/sign branches, the ordering
of the carrier bound, canonical parity, and the displayed exact-degree
certificate pass this separate review. The review does not assert
optimality, priority in the mathematical literature, or a complete new
formal derivation of the inherited K215/compiler calibration. The 102-gate
count concerns the supplied straight-line evaluator; named registers are
polynomial abbreviations, not additional existential variables.
