# A shifted positive strong multiplier

This new ordinary arithmetic endpoint retains the ten strictly positive
unknowns and the coherent four fixed coefficients of the free-J103/408
endpoint. Replace only its strong ordinate by

    I=(i+q^2)c^2

instead ofI=i*mu*c^2, where mu=q^2+1. Its evaluator has102 live
operations, with exact total degree388. All frozen endpoints and the
canonical PDF/TeX remain unchanged. No new Lean or encoded object-ZFC
proof, proof of consistency or optimality claim is supplied.

## 1. Complete equation and retained definitions

Use exactly the ten coordinates

    J,F,alpha,i,T,w,Y,n,eta,zeta in Z_{>0},

the full polynomial definitions in`source/FREE_J_PROOF.md` Section1 and
the same symmetric octic equation there. The two mathematical changes are

    I=(i+q^2)c^2,
    Df=1+Delta I^2, Q=Delta^2 I^2,delta=Q-1,
    V=Df[c(T+alpha)-R]-c,
    b=c(T+alpha)-R, L=H I+b, W=1+(q-1)L,

instead of the oldL=4(A-1)I+b+c(T+alpha), and the dependent registers. In particular the
unchanged carrier still has denominatorq^3(q-1)mu^2H, withmu=q^2+1.
The first parameterV0=Xmu^2Y^2, the scaled main parameter
A=mu(XY+Y+2)+1 andH=4A-5 are unchanged. The complete102-gate literal file
provides every abbreviation with only+,-,*; no radical or division is
an evaluation operation. All four original compact44 payloads are fixed.

The same coefficient box is assumed:

    beta odd, beta>=31, K0>0, 0<MC<beta<MF<2beta.

It holds for the authentic compact44 tuple used here, and separately for
the completely calibrated BFS page tuple with its differentK0. No
consistency theorem is asserted for arbitrary unrelated ports in this
arithmetic box.

## 2. The exact properties needed in soundness

For every positive input,

    I>0, c^2|I, I>=mu*c^2.                                  (1)

The last inequality follows fromi>=1 andi+q^2>=1+q^2=mu.
These are exactly the three soundness uses of the old strong definition.
There is no soundness use ofmu|I. To make that assertion inspectable,
we list the dependence of each part of the proof.

* The unconditional strong lower bound is
  f>sqrt(Delta)I>(A-1)I>=mu^2(a+2)c^2.
  It follows from(1), and so retains the old superincreasing-root
  estimates, includingtau+f<3(A-1)I. The shorter transport
  majorant is justified separately below.
* Main folding uses positiveI>=c, the normf^2-Delta I^2=1, and
  V=-c modf. These follow from(1) and the register identities.
* Direct normalized strong rank usesc^2|I, givingc|m andm>2p;
  it has no oddness ormu-divisibility premise.
* Auxiliary index recovery usesS=Delta I, c|S,
  S^2=Delta(f^2-1), V=-c modf andV=-R modc. All are retained
  identities becausec^2|I. No division bymu is used.
* The partial-fraction modulusmu^2 is part of the carrier denominator.
  Its coprimality usesq even,mu|A-1 andH=-1 modmu, notmu|I.
* The first-index congruence usesmu^2|4V0, with
  V0=Xmu^2Y^2, not any divisibility ofI.
* The half-binomial rounding, main projection, transport and native
  restoration use the recovered indices/scales and the same outer
  registers. They impose no constraintmu|I.

Thus one must not divide the new multiplier bymu or claim that its
currenti is an old positivei. Such a literal restoration is unnecessary.

## 3. A shorter transport majorant and soundness

Repeat FREE_J_PROOF's soundness only up to its transport contradiction,
using(1). The unchanged three-root hierarchy extracts integral tau,f,y.
Main folding yieldsc=psi_A(p) withp positive and odd. The first indexn0
cannot be1; hencec>8q^5. Neitherq parity nor integralrho is needed yet.
The unchanged mask upper bound is

    R<q^4+(alpha+2)q^2<c*alpha/4.

For the last strict inequality usec>8q^5 andalpha>=1. The remaining
polynomial difference is minimized atalpha=1, where it is
q^2(2q^3-q^2-3)>0. Thus the inequality holds uniformly atq>=32.
LetT'=T+alpha, soT'>=2. IfR>=0, then

    R<cT'/4, b=cT'-R>3cT'/4>=3c/2.

Sincek<c, bothk-1 andR+1 are belowb: for the latter,
b-R>cT'/2>=c>=3. Consequently

    |e|=|k-R-1|<=max(k-1,R+1)<b.

IfR<0, e=k+|R|-1>0 and
b-e=cT'-k+1>0, so again|e|<b. Therefore, withrho still rational,

    |rho|=|e|/mu^2<b/2.                                    (2)

AssumeBt<=-1. Nowb>0 andL=HI+b>0, henceW=1+(q-1)L>0 and
WBt/(q-1)<-L. The exact signed-center relation, withKquad/H>0 and
Y/q^3>0, gives

    n<tau+f+(y-V)+|rho|-L
      <3(A-1)I+b-HI-b<0.

The last strict inequality follows fromH-3(A-1)=A-2>0. This contradicts
n>0. ThusBt>=0 andC>0, giving3q<R<q^4-2. This proves the shortened
majorant sound without smuggling in the oldcT' term.

The remainder of FREE_J_PROOF now applies with(1). Rank and signed
auxiliary-index recovery givep=R. Oddp forces oddR; ifq were odd thenJ
andR would be even, contradiction. Only afterq is even do partial
fractions yieldmu^2|e and the first-index identityn0=(R+1)/2. The ratio
and whole-product arguments recoverX=2^R and the positive main
projection. CRT givesq^3|Y,q-1|Bt; fixed-minus parity givesR=3 mod4,
and the same ratio rounding identifies the half-binomialY.

Finally rebuild the fresh unscaled source61 witnesses exactly as in
ORIGINAL_PROOF Section6.18. In particular set its own

    c_o=psi_(a+2)(R), I_o=psi_(a+2)(R*c_o), i_o=I_o/c_o^2,

and the separate positive auxiliary coordinates supplied there. It does
not reuse the scaledI or requiremu|I. All15 source coordinates,
includingJ whenJ=1, are strictly positive. The same inherited positive
source theorem therefore yields a finite syntactic refutation.

## 4. Completeness by a fresh positive final coordinate

From a finite refutation choose a canonical old free-J103/408 zero,
with its positive root witnesses. Call its strong inputi_old, keep its
outer coordinates and set

    i_new=mu*i_old-q^2=mu*(i_old-1)+1>=1.

Then(i_new+q^2)c^2=mu*i_old*c^2=I_old, preservingI, all Pell radicands
and the canonical rank/index data. Recompute the shortenedL,W; the old
n coordinate is not retained or assumed to stay positive after a
subtraction. The canonical data already supplies the integers

    s0=Y/q^3>=1, t=Bt/(q-1)>=0, rho=e/mu^2>=1,
    kappa=Kquad/H>0, u=y-V>0.

Sinceb>0, the newL=HI+b is positive, soW>=1. Choose the final variable

    n_new=W*t+rho+tau+f+u-s0-kappa.

It is an integer and is strictly positive. Indeedtau>k>Y>=s0 and

    kappa<(X^2+2(A-2)Xc)/H<X+Xc/2<Xc<f.

HereH>X,2(A-2)/H<1/2,c>=3, and the strong lower bound from(1)
givesf>(A-1)I>Xc. All other displayed terms are nonnegative. The new
normalized center is therefore exactlytau+f+y; an all-positive-root
conjugate factor vanishes. This proves completeness with all witnesses
chosen in the licensed order. No coprimality of the new strong
multiplieri+q^2 withmu or any old-i integrality is assumed.

Together Sections3--4 prove the complete two-way positive-solvability/
finite-refutation equivalence under the same ordinary calibration.
It is not a pointwise polynomial identity or a bijection of all positive
zero sets. The independent literal certificates distinguish the exact
I-coordinate substitution from the changedL/carrier and freshn map.

## 5. Exact total degree388

All variables have degree1 and fixed ports degree0. The new degrees are

    degI=6, degDf=22, degQ=degdelta=32, degV=26,
    degL=11, degW=12, degM=13, degZ=39.

WriteZ=MV+Z0. The exact carrier identity givesdegZ0=26 with leading
term-H0*q0^4*q0^3*W0*Bt0. The changed quadratic projection term has
degree17 and does not affect that leading term. For

    s=delta Z^2, u=delta M^2 Dtau,
    v=delta M^2 Df, w=M^2 Dnum,

we have degrees110,76,80,110. Their exact centered difference is

    omega=s-w=delta Z0^2+2delta Z0 M V-M^2(V^2-1).

Its unique top part has degree97 and is

    omega0=2Q0 Z00 M0 V00.

In the centered octic expression the first square has degree194 with
leadingomega0^2. Its competing termu*v+(u+v)*w has degree at most190;
the last productu*v*w*s has degree376<388. Hence the complete equation
has degree at most388 with leading formomega0^4, and this is nonzero.

For an explicit attained coefficient, let

    q0=beta*J, c0=(eta+zeta)Y, a0=q0*w*Y,
    A0=q0^2*a0, I0=q0^2*c0^2,
    R0=q0^3(q0-F), Bt0=w(q0-F-alpha).

Then

    Q0=A0^4 I0^2,
    V00=-A0^2 I0^2 R0,
    M0=4q0^8 A0,
    W0=4q0 A0 I0,
    Z00=-H0 q0^7 W0 Bt0, H0=4A0.

Their product simplifies to

    omega0=2^7*q0^56*w^10*Y^19*(eta+zeta)^10
                     *(q0-F-alpha)*(q0-F).

Selectingalpha^4,F^4,eta^40 inomega0^4 gives uniquely

    [J^224 w^40 Y^76 eta^40 alpha^4 F^4]P
        =2^28*beta^224>0.

The exponent sum is388 and the actualbeta is positive. No other fixed
port occurs in this witness. A full independent centered-norm expansion,
complete gate substitution certificate and actual-tuple degree controls
check the transcription separately from this unbounded proof.
