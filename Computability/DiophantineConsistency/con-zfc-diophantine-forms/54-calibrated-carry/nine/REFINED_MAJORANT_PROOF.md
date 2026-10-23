# A polynomial-quotient majorant for the nine-positive finalizer

This is a new local arithmetic improvement. It retains the numerical Jones
ratio interface and composes with any source producing positive R,N,b,g and
Gcap, with R,N>=8 and b<=R,N. Registers are polynomial abbreviations, not
additional unknowns. The source compiler remains a separate dependency.

## Definitions and statement

Use A,C,J,D,F,G,H from the round-7 CRT-reparameterized ratio construction.
Write k=iJC, J=4A-5, D=(A^2-1)C^2+1, and L=CD+1-A. Thus

    F=1+k^2 D^2(D-1),   G=A+FL,   I=(G^2-1)H^2+1.

The ratio construction has A>=33280, C>=1 and i>=1. The proof below only
needs A>=729. Define

    Nstar=2G+L,
    N1=2k^2 D(D-1)L+3C,
    N2=2k^2(D-1)L,
    N3=2k^2(L-C),
    N4=2k^2 C,
    T6=k[(1024D^2-512D-128)Nstar-64N1-40N2-28N3-21N4],
    T=T6+i^3[9C^2(64A-239)-14C(64A^2-304A+603)+1024]
          +288i+2048.

All coefficients are integers. Then T>2048 sqrt(DF) G>0, so V1=TH is a
strict polynomial majorant of sqrt(2048^2 DFI).

The supplied support-majorants package already introduced T6 and a cruder
correction. The new contribution here is the displayed correction, obtained
by exact polynomial division in A and a seventh-order remainder bound. Its
much lower degree removes a further leading block from the final equation.

## An exact seventh-order bound

Put

    t7=2048D^7-1024D^6-256D^5-128D^4-80D^3-56D^2-42D-33.

Direct multiplication gives

    t7^2-2048^2 D^13(D-1)
      =109824D^6+36608D^5+18304D^4+9984D^3
          +5460D^2+2772D+1089 >0.

Also t7>0 for D>=1, by comparing its leading coefficient 2048 with the
sum 1719 of the absolute values of the other coefficients. Hence

    t7/(2D^5)>1024D^2 sqrt(1-1/D).

This is a finite polynomial identity, not an appeal to series convergence.
Let t6=1024D^6-512D^5-128D^4-64D^3-40D^2-28D-21. Since

t6/D^4=t7/(2D^5)+33/(2D^5), direct expansion gives

    T6=k t7 Nstar/(2D^5)+E7,

where

    E7=14k^3(A-1)/D-9k^3 C/D
       +9k^3(A-1)/D^2-33k^3 C/D^2+33k^3(A-1)/D^3
       +k[(120C+192-64A)/D+(84C+120-40A)/D^2
           +(63C+84-28A)/D^3+(63-21A)/D^4]
       +(99/2)kC/D^4+(33/2)k(3-A)/D^5.

Every denominator in this proof is a real-number comparison; none appears
in the final polynomial.

## Polynomial division cancels the dangerous remainder

The two exact identities are

    J^3=(A+1)(64A^2-304A+604)-729,
    J^3=(A^2-1)(64A-240)+(364A-365).

Set s=A^2-1. Since D=sC^2+1 and k=iJC, they give

    14k^3(A-1)/D -14i^3 C(64A^2-304A+604)
      =-14i^3 C[729/(A+1)+J^3/((A+1)D)],

    -9k^3 C/D +9i^3 C^2(64A-240)
      =-9i^3 C^2(364A-365)/s+9i^3 J^3 C^2/(sD).

For A>=729,C>=1,

    0<729/(A+1)<1,
    0<(364A-365)/s<1,
    J^3/((A+1)D)<64/C^2,
    k^3 C/D^2<i^3,
    kA/D<4i.

The third bound follows from J<4A and
(A+1)(A^2-1)>A^3. For the fourth, J<4A gives
k^3 C/D^2<64i^3 A^3/(A^2-1)^2<i^3; the last inequality follows already
for A>=65. The fifth follows from JA<4(A^2-1) and C>=1.

Dropping all positive terms in the remainder therefore gives

    E7-14i^3 C(64A^2-304A+604)+9i^3 C^2(64A-240)
      >-14i^3 C-9i^3 C^2-929i^3-277i.

Here 929=896+33. For the low-order k terms, use D>=9 and
64+40/9+28/81+21/729<69, giving the bound 276i. The final negative
term is at most (33/2)kA/D^5<66i/D^4<i, giving 277i altogether.
The correction defining T supplies
14i^3 C+9i^3 C^2+1024i^3+288i+2048, so

    T>k t7 Nstar/(2D^5)+2048.

## Compare with the true radical

Put X=k^2D^3(D-1). Then DF=X+D and G=(X/D)L+CD+1.
Strict concavity of the square root gives

    2048 sqrt(DF)G
      <1024kD^2 sqrt(1-1/D)(2G+L)+2048v,
    v=(CD+1)/(2kD sqrt(1-1/D))<1.

For the last bound use k>=7C, D>=9 and
sqrt(D(D-1))>D-1. Since t7/(2D^5) is strictly above
1024D^2 sqrt(1-1/D), the preceding inequality proves
T>2048 sqrt(DF)G. Finally I<(GH)^2, proving V1=TH>2048 sqrt(DFI).

## Finalizer and its exact meaning

Keep the round-7 CRT reparameterization H=C+F(B1+jC), u=J,v=Q,
V0=PK, m=[K^2-4(C-KY)^2]Gcap-8gK^2 and Omega=Jm. Replace its old
second majorant and scale by the new V1 and q=2048^2. Set

    E0=Jn+Q,
    Theta=E0-Omega(V0+V1),
    F9=[Theta^2-Omega^2(a0+q a1)]^2-4q Omega^4 a0a1.

The same margin-first proof applies. Both V0 and V1 are unconditional strict
majorants, so any zero forces m>0 before claiming integrality. The margin
implies a1>a0, excluding a vanishing signed sum of the two radicals. Both
roots are therefore integral and J divides Q. Conversely the four ratio
conditions supply n=m(V0+V1+r0+r1)-Q/J>=0, since V1>Q. The latter follows
from F=1+k^2D^2(D-1)>=D, so sqrt(DF)>=D>C^2 and
V1>2048C^2>Q. Alternatively, H>C and sqrt(DF)>C suffice. Thus the existential predicate is unchanged.

## Source-parametric exact degree

Suppose deg R=r, deg N=n0, deg Gcap=c0, with positive diagonal leaders
rho,nu,kappa, respectively. In the intended source families C is led by
2R, and the standard dominating monomials in the ratio registers give

    deg A=r+4n0+2,  deg C=r,
    deg H=17r+32n0+19,
    deg V1=48r+92n0+52,
    deg Omega=5r+20n0+c0+12.

Independent exact expansion of T^2-2048^2 DFG^2 gives 703 terms in A,C,i.
Its leading term for these source degrees is

    9*2^18 i^6 A^15 C^18,

with degree 33r+60n0+36. The complete expanded integer polynomial is in
REFINED_DEFECT_POLYNOMIAL.json; check_refined_majorant.py derives it anew.
Every monomial has A-exponent at most 15, C-exponent at most 18 and
i-exponent at most 6; only the displayed term attains all three bounds.
Thus all other terms have smaller degree for any positive degrees of A,C,i.
The checker instantiates r,n0 separately, never assuming r=3n0.
Hence

    Delta1=V1^2-q a1
          =H^2(T^2-q DFG^2)+q DF(H^2-1)

has exact degree 67r+124n0+74. In the identity

    Theta^2-Omega^2(a0+q a1)
      =E0^2-2E0 Omega(V0+V1)
          +Omega^2[(K^2-1)+Delta1+2V0V1],

Omega^2 Delta1 uniquely dominates. Its square also dominates the norm's
subtracted term. Therefore

    deg F9=154r+328n0+4c0+196,
    diagonal leader=81*2^148*kappa^4*rho^154*nu^328.

For the old quadratic-radix source r=3t,n0=t,c0=2W+1, this is
790t+8W+200, versus the old 964t+8W+236. If
rho=16 lambda^(3ell), nu=4 lambda^ell and kappa=32 lambda^W,
its diagonal leader is 81*2^1440 lambda^(790ell+4W).
