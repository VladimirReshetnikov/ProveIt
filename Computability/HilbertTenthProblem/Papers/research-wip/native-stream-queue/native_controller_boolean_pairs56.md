# Two native Boolean streams and their complements in 56 operations

This complete arithmetic component costs **56=30M+26A**. It proves
native ternary geometry and the typing of two independently selectable
Boolean streams, together with their complements, using one retained
43-operation Pell kernel. It has 14 equations and 18 strictly positive
auxiliaries beyond five positive parameters. No finite controller,
ordinary-input initialization, routing or universal computation is
included in this count. The established complete universal bound is 76.

## 1. Exact semantics

The positive parameters are q,F0,F1,F2,F3. The relation holds exactly
when, for some t>=1 and H=(q-1)/2,

    q=3^t,
    Fi=H+Ti, with each Ti a length-t Boolean ternary word,
    T0+T1=H and T2+T3=H coefficientwise,
    the units digit of T0 is1.                           (1)

Equivalently T0 and T2 are arbitrary independent native Boolean words,
except that T0 starts with1; T1 and T3 are their complements. The units
digit of T2 is unrestricted. A decoded Ti may be identically zero, but
all supplied Fi are positive. This is two complementary pairs, not a
four-label one-hot relation: for example T0 and T2 may both be1 at a
position.

Supply positive H, called `Hrep` in the source, and the seventeen retained
Pell coordinates

    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y_aux.

There are therefore 18 positive auxiliaries and 23 positive coordinates
if the five parameters are also chosen existentially in a larger source.
The index r is supplied; the packed word and scale below are derived.

## 2. Source and ledger

Impose four outer equalities

    q=2H+1,
    F0+F1=3H,             F2+F3=3H,
    r=P=F0+qF1+q^2F2+q^3F3.                             (2)

Set D0=q^4 and attach the ten retained ternary Pell equations from
[the reviewed selector source](native_controller_three_selector_53.md),
using X=wD0 and Y=sD0. For clarity their mathematical form is

    tau(tau+1)=((XY)^2+X)(Yk)^2,
    c=Yk+eta, k=eta+zeta, k=r+1+hXY,
    a=Y(X+1), d=X+ac+ga(6a+8),
    d^2=1+(a^2+6a+8)c^2,
    (ic^2)^2=(a^2+6a+8)(f^2-1),
    (ic^2)^2((2r+1+jc)^2-y_aux^2)=1-y_aux^2,
    2r+1+jc=c+of.                                       (3)

All powers and products in this notation are evaluated by the literal
source. Its 13 outer instructions are

    twice_H=H+H; q_calc=twice_H+1; three_H=H+twice_H;
    sum01=F0+F1; sum23=F2+F3;
    p0=q*F3; p1=F2+p0; p2=q*p1;
    p3=F1+p2; p4=q*p3; P=F0+p4;
    q2=q*q; D0=q2*q2.

They cost 5M+8A. The unchanged kernel costs 25M+18A, so the complete
count is56=30M+26A. Comparisons implement (2) for free, followed by
the ten comparisons in (3). The independent polynomial audit records
the usual acyclic auxiliary-norm correction when its penultimate
polynomial substitutes (a^2+6a+8)(f^2-1) for (ic^2)^2.

## 3. Bounds before recovering the powers

Positivity gives H>=1 and q=2H+1>=3. Each pair in (2) sums to3H,
so

    1<=Fi<=3H-1=(3q-5)/2<2q.

Concentrating each pair's excess in its higher packing coefficient gives

    q^3+q^2+q+1<=P
      <=1+q(3H-1)+q^2+q^3(3H-1)<(3/2)q^4.

Hence, before assuming q is a power of3 or any field is belowq,

    D0>=81, r>=40, r<(3/2)D0, D0<r^2,
    X,Y>=D0, XY>=D0^2>r+1,
    a>=D0(D0+1)>2r+1,
    6r/a<9/(D0+1)<=9/82<1/2.                           (4)

These bounds are stronger than the smaller-scale thresholds explicitly
audited in the 53/54 proof. In detail, the first Pell index n is at
least r+1; its base exceeds the main base A=a+3 and c>Yk>k, so the
main index p>=n+1>=r+2>=42. Thus c>A^6>AD^2, c>2r+1 and
0<2p<=c. The retained auxiliary-rank and half-parameter arguments
recover p=2r+1. The unchanged positive difference

    (2(2XY^2+1)-1)-4(a+3)=4Y(X(Y-1)-1)-11>0

then recovers n=r+1.

The same ratio argument gives, with xi=(X+1)^(2r)/X^r,

    xi<c/k<xi(1+12r/a),
    Y>=X^r, a>X^(r+1), 0<c/k-xi<24r/(X+1).

Use the direct ternary recurrence from the retained proof: the main
congruence gives X=3^(2r+1) modulo6a+8. Both representatives are
strictly between0 and6a+8, since X<a and

    3^(2r+1)=3*9^r<X^(r+1)<a

for X>=81. Thus X=3^(2r+1) exactly. Since q^4 divides X, q is a
power of3. Now X>48r, and the retained binomial tail bound is below1/6.
The ratio error below1/2 and unit interval therefore give

    Y=floor((X+1)^(2r)/X^r),    q^4 divides binom(2r,r).   (5)

No field bound or packed-word bound P<q^4 was used in this recovery.

## 4. Paired checksums exclude every carry and overflow

Write q=3^t, N=4t and L=q^4. By Kummer's theorem, (5) gives at least
N carries when P is doubled in ternary. Normalize the four supplied
q-fields with carries c_i and chunks G_i:

    c_(-1)=0,
    Fi+c_(i-1)=Gi+q*c_i,       0<=Gi<q.

The preliminary bound Fi<=3H-1 guarantees c_i is0 or1, even with an
incoming carry. Put C=c0+c1+c2 and epsilon=c3. Then

    P=G0+qG1+q^2G2+q^3G3+epsilon*q^4,
    G0+G1+G2+G3=6H-2H*C-q*epsilon.                      (6)

First suppose P<L, so epsilon=0. All N ternary positions must generate
a doubling carry. Therefore every trit of the low chunks is1 or2 and
the units trit is2. Their total as ordinary integers is at least4H+1.
If C>=1, (6) bounds that sum by4H, a contradiction. Thus C=0;
the supplied Fi themselves are the actual native positive chunks.

If instead P>=L, the preliminary P<(3/2)L implies epsilon=1, so the
extra top ternary digit is1. Among N+1 possible carry positions, at
least N generate a carry. Every zero among the low N trits prevents
a carry regardless of its incoming carry. Hence at most one such trit
is zero. The low chunk sum is therefore at least

    4H-3^(t-1).                                         (7)

If C>=1, (6) gives at most2H-1, contradicting (7). If C=0, the last
pair instead has the exact normalized sum

    G2+G3=F2+F3-q=3H-q=H-1.

The same at-most-one-zero fact gives G2+G3>=2H-3^(t-1)>H-1,
again a contradiction. The last strict inequality follows from
H+1=(3^t+1)/2>3^(t-1). This excludes packed overflow entirely.

Consequently every Fi has exactly t native trits in{1,2}, and F0's
units trit is2. Define Ti=Fi-H. They are Boolean, and (2) gives
T0+T1=T2+T3=H. Each pair equality is coefficientwise: its local residual
belongs to[-1,1], and a least nonzero residual cannot be divisible by3.
This proves all semantics (1), without importing the false implication
that four Boolean words with a single total checksum are one-hot.

## 5. Every positive witness in the converse

Given any words satisfying (1), set Fi=H+Ti. Their pair checksums hold,
P has4t native trits in{1,2}, and its units trit is2. Doubling P
therefore generates exactly4t carries, proving the divisibility in(5).
Moreover q is odd and

    P=F0+F1+F2+F3=6H=0 modulo2.

Thus r=P is automatically even, as required by the positive
half-parameter branch. Neither an even-length restriction nor a parity
variable is needed.

Use exactly the constructive witness map in Section5 of the reviewed
53 proof, now at D0=q^4 and this r. Explicitly, with J=2r+1,

    X=3^J, w=X/D0,
    Y=floor((X+1)^(2r)/X^r), s=Y/D0,
    a=Y(X+1), A=a+3, D=A^2-1, E=XY, B=2XY^2+1,
    c=psi_A(J), d=chi_A(J), k=psi_B(r+1),
    eta=c-Yk, zeta=k-eta, tau=(chi_B(r+1)-1)/2,
    h=(k-r-1)/E, ga=(d-X-ac)/(6a+8),
    m=2cJ, f=chi_A(m), i=D*psi_A(m)/c^2,
    R=ic^2, y_aux=psi_R(J), u=chi_R(J)/R,
    o=(u-c)/f, j=(u-J)/c.

Here chi,psi are the standard positive Pell sequences. The bounds(4)
and power/binomial divisibilities verify the retained map's hypotheses;
in particular J>=4t ensures w is integral, and (5) makes s integral.
The ratio interval makes eta,zeta positive; the Pell congruences and
growth estimates make tau,h,ga positive integers. The expansion at m
gives c^2 dividing psi_A(m). Since r is even, J=1 modulo4, which gives
u=c modulo f and u=J modulo c; the retained growth proof gives u>c>J.
Thus o,j are also positive, and every equation(3) holds. This is a
parametric positive-witness proof, not a claim that the enormous final
auxiliary tuple was numerically materialized.

## 6. Controller interface and limits

This module provides two independent Boolean coordinates per time
position, with their complementary coordinates, all synchronized at the
same native base-three length. It permits four local bit pairs. Computing
either bit word or its complement as Fi-H costs one subtraction; H and
2H are already paid. Thus a proposed machine whose read, append or state
coordinate is one of these literals can reuse the same typed fields
without another kernel or any radix conversion.

Arbitrary Boolean functions of the pair are not supplied for free.
In particular a joint selector, AND, XOR, or a general four-row table
projection needs its own proved arithmetic relation. Nor do synchronized
bit planes by themselves certify a finite-state transition path or its
initial and accepting states. The possible use as a native controller
interface remains constructive work beyond this typing theorem.

## 7. Evidence

The [checker](native_controller_boolean_pairs56.py) independently builds
all14 source polynomials at the new q^4 scale, checks the exact literal
56 schedule and retained auxiliary-norm correction, tests pre-power
inequalities on arbitrary positive pair decompositions, and exhaustively
compares factorial valuation with native-field semantics through t=5.
Those domains include both field carries and packed overflow.

Independent canonical word pairs through t=6 include zero decoded words
while every supplied field remains positive. Exact main/first Pell and
ratio checks use r=50 and68, both actual admitted q=3 module values;
the unbounded auxiliary extension follows from Section5. Default execution
compares the [saved receipt](native_controller_boolean_pairs56.json).
No frozen prior source or receipt is edited. Two independent scoped
proof/source/default reviews pass, including the pre-power inequalities,
field-carry and packed-overflow exclusions, and positive converse.
