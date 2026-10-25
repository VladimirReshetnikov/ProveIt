# Compressed whole-expression centers: eleven unrestricted integers

## Result and comparison boundary

The new literal equations have respectively **degree 298 / 147 binary gates**
and **degree 300 / 145 binary gates**, in eleven unrestricted integer unknowns.
All six authentic fixed coefficient numerals, including their complete bytes
and finite recipe, are unchanged. No intermediate register is another unknown.
The nearest-factorial incoming archive already supplied degree 298 in 150
gates; the new result here saves three gates, not another two degrees against
that latest input. The degree-300 companion likewise saves three gates against
the retained Round 19 / Round 18 300/148 endpoint.

The 298/147 equation improves both degree and cost against the previous
300/148 delivery. The 300/145 equation remains a lower-cost tradeoff. The
restricted degree floors are 298 in the rebased frame and 300 in the old
frame, not global bounds for eleven-variable consistency equations.

## 1. Complete fixed formulas

The independent variables are j,C,z,h,r,v,w,T,c,n,s, all in Z. The coefficient
ports beta,K0,MC,MF,cone_A,cone_B are fixed numerals, not variables. Their
complete values are bound in coefficients/BINDING.json; in particular
beta=2^1064921-1, cone_A=2^1113, cone_B=2^666104, and MF is already shifted.
For both endpoints define

    J=6j+1, q=beta J+1, W=12w+4, X=qW, Y=v,
    E=XY, ell=XY^2, a=E+Y, A=a+2, H=4a+3,
    Delta=a^2+H=A^2-1,
    F=(K0+W)C-z(q-1),
    R=[q(q-F)-C](q^2-1)+(MC+q MF)J.

For the 298/147 endpoint take k=R+1+h ell and b=6; for 300/145 take
k=R+1+h E and b=8. Define

    eta=c-Yk,
    Derr=(cone_A F-q)^2+(cone_B C-q)^2,
    B0=k^2(q^2-Derr)-4q^2 eta^2,
    Budget=Y^2 B0-k^2 q^b,
    Dt=1+ell(ell+1)k^2, D=Budget-4,
    P=Dt[1+D Dt s^2],
    Dm=1+Delta c^2, B=r A Dm, U=r c^2 Dm,
    I2=c^4 B=A c^2 U, Df=1+Delta I2,
    Q=Delta^2 I2, delta=Q-1,
    V=Df(c-R+4A U T)-c, Cy=QV^2-1,
    K=X(3c-2X)+2, M=2q^3, Dc=HM, S=srH M^5,
    zc=Dc T+MK+H(v-q^3),
    Ac=(zc^2+3Dc^2)(zc^3-19Dc^3),
    gamma=8Delta+4, lambda=4(gamma U-r c^4).

The two new centers are

    Psi298=lambda V+U^2 T{r c^4[(gamma-1)(c^2-2)-2]+64A Delta},
    Psi300=lambda V+U^2 T{r c^4[(gamma-1)(c^2-2)]+64A Delta}.

Use the matching center and front. Finally

    Z=S(n+Psi)-Ac,
    pa=delta Z^2, pb=delta S^2 P, pc=1024 S^2 B Df Cy,
    N=(pa+pb-pc)^2-4pa pb.

The equation is N=0. These are all ordinary integer-polynomial abbreviations;
there are no division, radical, variable-exponent, oracle or implicit-witness
gates. Each multiplication by a fixed numeral and each square counts as a
binary arithmetic gate. The JSON graphs are the complete literal equations.

## 2. Exact center shears: new zero-existence equivalence

Let Psi298_parent be the center in inherited_rebased/PROOF.md Section 6:

    [(32Delta+16)U-4r c^4]V
      +U^2 T[8U(c^2-2)+64A^3+r c^4(3c^2-16)].

Let Psi300_parent be the old center in BASELINE_PROOF.md, obtained by
replacing r c^4(3c^2-16) above with 3r c^6. The literal identities
U=r c^2+Delta r c^4 and A^3=A Delta+A give

    Psi298-Psi298_parent=U^2 T(16r c^2-64A)=epsilon298,
    Psi300-Psi300_parent=U^2 T(16r c^2-64A-14r c^4)=epsilon300.

These are exact identities in the integer polynomial ring. Both epsilons
are independent of n. For either endpoint, keep the ten outer coordinates
and set n_parent=n_new+epsilon. Then Z and the entire new polynomial equal
the parent's Z and polynomial. Conversely n_new=n_parent-epsilon. This is an
actual bijective shear of the full integer zero sets, not just necessary
Pell conditions, a rational map, or a numerical check.

It follows immediately that the new equations inherit the exact ordinary
calibration of their respective parents. The 298 endpoint uses the changed
full-modulus/weak-magnitude parent, not an invalid removal of its guard.
The remaining sections explicitly identify that parent's critical handoff.

## 3. Why the degree-298 parent is calibrated

The complete incoming proof and its source closure are retained verbatim in
inherited_rebased/PROOF.md and inherited_rebased/inherited/. That proof uses
k=R+1+h XY^2 and Budget6=Y^2 B0-k^2q^6 together, rather than deleting the
old magnitude condition on an unjustified early divisibility inference.

The unchanged even-weight norm, coprime-product and adjacent-coefficient
descent arguments recover B=u^2, Df=f^2, Dt=tau^2 and an integral auxiliary
y, with positive u,f,tau, and Budget6>=12. They also exclude S=0 and prove
S|Ac. The exact sign/parity facts needed before extraction remain valid:
Delta>1; H is odd and nonzero; D=8 or12 modulo16; P=1 modulo4 and nonzero;
delta is odd and nonzero. The only possible two-negative-radical cancellation
would require 1024B=P, excluded modulo4. The exact identities

    gcd(B,Df)=gcd(B,delta Cy)=gcd(Df,delta Cy)=1,
    Df=1 modulo3

supply positive individual squares rather than unjustified signed squares.
The proof-only I=c^2u and T_old=uT give

    f^2-Delta I^2=1,
    V=f^2(c-R+4I T_old)-c,
    (Delta I)^2 V^2-[(Delta I)^2-1]y^2=1.

In particular c^2|I. The denominator descent is integral and does not assume
the conclusion that its rational auxiliary root has denominator one.

Budget6>0 gives k,Y nonzero, B0>0 and |Y|>|q|^2. Its centered disk then
supplies the common nonzero signs of q,F,C,q-F-C, |c/k-Y|<1/2, and the
authentic packing bound

    |q|(|q|^2-1)<R<|q|^4-2.

Because |X|>=4|q| and |q|>=16, the new first-index modulus satisfies

    |ell|=|X|Y^2>4|q|^5>3R+1.

The carrier valuation gives M|H(Y-q^3), whose 2-primary part proves Y even,
and H|q^15 Kq^5 for Kq=X(X+2ac)-1. It does NOT prove q^3|Y at this point.

The first Pell recurrence gives psi_(2ell+1)(m)=m modulo2ell. Together with
literal k=R+1+h ell this yields the signed congruence

    epsilon_sign*2m=R+1 modulo |ell|.

The positive branch forces m>=(R+1)/2; the negative branch forces m>R.
Absolute main-root folding, the nonodd strong-rank lemma (using c^2|I, not
odd I/c^2), and the two auxiliary residues give the main index p=R. The
negative branch is impossible, and no wrap in the positive branch gives
2m=R+1. These are precisely the old ratio proof's needed hypotheses; it
requires |Y|>=6, not a cubic expression for Y. It yields

    R=2t+1, |Y|>(|X|-3)^t/2-1, |H|>|X|(|X|-3)^t.

The same fifth-power whole-product bound now applies. Put x=|X| and
Pi=(sign(c)X-2^R)(2^R sign(c)X+1). Then H|q^15 Pi^5, while

    |q|^15 |Pi|^5<2^(20t-10)x^25,
    |H|>x^(t+1)/2^t.

The authentic x>=2^64 and t>=36 give 43t-1526>=22, proving the divisible
integer has absolute value below |H|. Thus Pi=0 and sign(c)X=2^R.
Modulo3 fixes c>0 and X=2^R; the surviving first-index sign and strip give
k,Y>0. Only NOW q|X makes |q| a power of two, so odd H is coprime to M.
Late scale recovery gives Y=(2v_scale+1)q^3 with v_scale integral. The
uniform centered half-binomial theorem then proves 0<eta/k<1/4.

An arbitrary new zero need not satisfy Budget8>0. Soundness therefore
restores the older B0-only source, never the stronger free-scale guard.
In the native Q41 handoff set h_old=Y*h_new; then
R+1+h_old XY=R+1+h_new XY^2=k exactly. The retained construction regenerates
fresh odd strong/auxiliary witnesses (it does not pretend the incoming
multiplier is odd), restores the old positive native interval and square
coordinate, and passes that actual source zero to the compiler/refutation
theorem. The complete dependency argument is in the retained incoming proof.

Conversely the canonical source has k=2psi_(2ell+1)((R+1)/2); its recurrence
implies 4ell|(k-R-1), so new h is integral. Its Budget8>64 implies
Budget6>Budget8>64. Choose a Pell guard pair, then ONE strong pair satisfying
4s A d c^2|I, then u,r, then an intersective-quintic residue, and interpolate
T_old modulo u s r with that SAME fixed pair. Finally set

    n=Ac/S+32ufy+tau g-Psi.

Every quotient is proved integral, one norm factor vanishes, and the strong
pair is never reselected after a residue request. The shear in Section 2
introduces no further witness or choice-order obligation.

Thus, with the inherited ordinary calibration, ZFC proves that absence of
integer zeros of either new equation is equivalent to syntactic Con(ZFC).
Neither consistency nor unsolvability is proved here, and no new end-to-end
proof-assistant certificate or encoded object-ZFC proof is claimed.

## 4. Exact degree, complete remainders and actual coefficients

In the independent free ring on (A,c,r,T,R), assign weights (3,1,1,1,5),
set Delta=A^2-1, and retain the displayed U,B,Df,Q,V. Put

    Dcenter=Psi^2-1024 B Df V^2,
    Ecenter=(Q-1)Dcenter-1024 B Df(V^2-1).

For Psi298 the exact weighted degrees are80 and108, with complete top forms

    [Dcenter]_80=512 A^15 c^24 r^5 T R-8192 A^17 c^22 r^5 T^2,
    [Ecenter]_108=512 A^22 c^30 r^6 T R-24576 A^24 c^28 r^6 T^2.

For Psi300 they are82 and110, with complete top forms

    [Dcenter]_82=512 A^16 c^26 r^6 T^2,
    [Ecenter]_110=512 A^23 c^32 r^7 T^2.

check.py independently re-expands and records EVERY coefficient of these
remainders in CHECK.json: 449/881 terms for degree298 and455/888 for degree300.
No producer code is imported. It also proves both exact shear identities.

Put W0=Sn-Ac. The exact cancellation cut is

    pa+pb-pc=delta W0^2+2delta S Psi W0+delta S^2 P+S^2 Ecenter.

Here deg S=20, deg W0=35, deg delta=28 and deg Psi=54. The first three
terms have degree at most98,137,122 in the rebased frame (124 in the old
frame). The last term has degree148 for298, and150 for300. Thus the squared
inner term has degree296 for298, while -4pa pb has exact degree298 and
cannot cancel. For300 the terms tie in total degree300, but the inner-square
leader has T-degree4 and the cross product has T-degree2. Again it cannot
cancel. Explicit attained actual coefficients are

    [j^136 w^46 v^50 z^6 s^6 r^12 c^40 T^2] N298
       =2^272 3^182 beta^136 >0,
    [j^110 w^50 v^50 s^4 r^18 c^64 T^4] N300
       =2^256 3^160 beta^110 >0.

The exponent sums are exactly298 and300. These are complete-polynomial
certificates at the authentic coefficient tuple, not generic-port degrees,
syntactic degree352, or numerical line samples. All live gate leading
coefficients are independently propagated and recorded in CHECK.json.

## 5. Verification and exact scope

The 298 equation has29 additions,24 subtractions,94 multiplications:147.
The 300 equation has29 additions,23 subtractions,93 multiplications:145.

build.py --check reconstructs both graphs byte-identically. check.py verifies
all live gates in independent free polynomial rings, exact center shears and
remainders, attained actual degrees and numeral reconstruction; it authenticates
the retained source closure. audit_mutations.py rejects both alternative
operation labels at every arithmetic gate:294+290=584 mutations. A separate
check_scalar_top_forms.py imports neither builder nor checker and binds23 full
highest homogeneous forms, including all terms involving h in the new k.
All checks run with ordinary Python and python -O without removable asserts.
replay.py verifies the same portable closure in a clean temporary directory.

Finite checks certify formulas and finite algebra. The retained ordinary
Pell, interpolation, intersectivity and native/compiler/refutation theorems
remain the explicitly identified unbounded inputs. See
REBASED_FIXED_FRAME_DEGREE_FLOOR.md for the new restricted298 lower bound;
the historical fixed-frame300 theorem is preserved unchanged.
