# Centered three-root transport: eleven positive variables, degree 257

This is a second, lower-degree endpoint, not a replacement for the lower-cost
277/111 endpoint. Its complete polynomial DAG is p11_positive_degree257.json,
built by build_centered.py. It has eleven strictly positive integer unknowns,
degree 257 and 114 live binary arithmetic operations. The inherited semantic
interfaces are the same as in PROOF.md. No new formal calibration is claimed.

## 1. Complete register specification

Use the eleven unknowns j,F,alpha,i,T,X,Y,n,eta,zeta,gamma and the whole
compact44 fixed tuple beta,K0,MC,MF, with the already-shifted MF port.
Define all registers of PROOF.md except its Vbar,L,W,Zbar. In particular,

    J=3j+1; q=beta J+1; C=q-F-alpha; E=XY;
    k=eta+zeta; c=kY+eta; a=E+Y; H=4a+3;
    Delta=a^2+H=(a+2)^2-1; ell=EkY;
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J;
    Rhat=q^3(q+F+alpha); M=q^3(q-1);
    Bt=(q K0+X)C-qF; Dtau=ell(ell+k)+1;
    I=i c^2; Df=1+Delta I^2; Q=Delta^2 I^2; delta=Q-1;
    V=Df(cT-R)-c;
    r0=k-R-1; S=4qY; U=qS;
    Dstar=U(X+ac)+H(U gamma+SX-r0);
    A1=Dstar^2-U^2(1+Delta c^2).

The new centered transport uses

    B0=cT+Rhat; L=Df+B0;
    hstar=4q Df+L; W=1+(q-1)hstar;
    Zbar=M(ell+k+n+L+V)+(q-1)Y-q^3 W Bt.

Keep exactly the same three-root norm and unit-product finalizer:

    A=M^2 Dtau; Bf=M^2 Df; Cnum=M^2(QV^2-1);
    Tn=delta^2 A Bf; Rn=delta Cnum;
    Jn=delta(Zbar^2-A-Bf)-Cnum;
    Ncenter=Jn^2-4[Tn+Rn(A+Bf)];
    N8=Ncenter^2-64 Tn Rn Zbar^2;
    P11=N8+A1+N8 A1.

All named registers are polynomial abbreviations, not additional witnesses.
All divisions below occur in the proof only.

## 2. Radical and denominator recovery before any sign bootstrap

The unconditional separation proof in PROOF.md applies unchanged. It uses
only I>=c^2, not the transport weight or center. Thus Dtau,Df,Dy are distinct
positive rationals, where Dy=(QV^2-1)/(Q-1), and no signed sum of their square
roots vanishes. The octic norm N8=0 gives

    Zbar/M=tau_*+f_*+y_*,
    tau_*^2=Dtau, f_*^2=Df, y_*^2=Dy.

Three-root rational extraction makes all roots rational. The first two are
integers because their squares are integers. The adjacent-coefficient Pell
descent applied to QV^2-(Q-1)y_*^2=1 makes y_* an integer as well. Write
t=abs(tau_*), f=abs(f_*), y=abs(y_*). Then t<ell+k.

Because M divides Zbar, reduction modulo q^3 and q-1 respectively gives
q^3|Y and (q-1)|Bt. This uses W=1 modulo q-1 and gcd(q,q-1)=1,
not the sign of a recovered transport variable. Put s=Y/q^3>0.

A1=0 makes Dstar/U an integer by rational-square integrality, so
abs(Dstar/U)^2-Delta c^2=1. Its sign is immaterial at this stage.
Classifying this positive absolute main Pell root and the first Pell root
t gives p,m1>=1, c=psi_(a+2)(p) and k=2 psi_(2XY^2+1)(m1).
Since c>=3, p>=2. If m1=1 then k=2 and c=2Y+1, whereas
c>=2(a+2)>=4Y+4, impossible. Therefore

    c>8XY^3>=8q^9.

These conclusions use no positivity of C or the recovered r, and no bound
on R. They avoid the apparent circularity in centering at V.

## 3. A small bound for the centered auxiliary gap

The authentic masks give abs(R)<Rhat, as proved in PROOF.md. For every
positive input, abs(V)<Df B0, delta>Df, abs(V)>1 and

    0<y-abs(V)=(V^2-1)/(delta(y+abs(V)))
                 <abs(V)/delta<B0.

Also Df>sqrt(Df)=f because Df>1. Thus if V>0,

    L+V-f-y=(Df-f)+B0-(y-V)>0.

The weight hstar bounds the centered gap plus an exceptional negative-V
case, rather than bounding the full auxiliary root of size O(Df Rhat).

## 4. Bootstrap C>0 without assuming the recovered transport gap positive

Suppose C<=0. Set d=-C>=0 and B=-Bt>0; explicitly
B=(qK0+X)d+qF. Since K0>=1,

    qB>=q^2 d+q^2 F.

Using alpha=q-F+d and the authentic mask inequality
0<(MC+q MF)J<2q^2 gives

    R=(q(q-F)+d)(q^2-1)+(MC+q MF)J
      <qB+q^4+q^2.

The norm equation gives the real equality

    tau_*+f_*+y_*
      =ell+k+n+L+V+s+W B/(q-1).

If V>0, its right-hand side is strictly greater than t+f+y by Section3
and ell+k>t, an immediate contradiction. The case V=0 never occurs.

If V<0, the integer cT-R is nonpositive; hence R>=cT>=c>8q^9.
In particular q^4+q^2<R/2, so R<2qB. Furthermore
abs(V)=Df(R-cT)+c<Df R. Section3 then gives

    L+V-f-y>-2 Df R.

Since W>4q(q-1)Df,

    W B/(q-1)>4q Df B>2 Df R.

Again the right side of the displayed norm equality is greater than
t+f+y, impossible. Therefore C>0.

Now the authentic coefficient bounds give 3q<R<q^4-2. Together with
c>8q^9 this implies V=Df(cT-R)-c>1.

## 5. Soundness and canonical completeness

Define recovered positive coordinates

    f_old=f; i_old=i; u=y-V;
    r=n+L+V-f_*-y_*.

The auxiliary norm gives u>0. By Section3 and the signed-root bound,
r>=n+L+V-f-y>n>0. The first carrier register with this r and weight
hstar equals M tau_*. The strong and auxiliary equations and A1 all hold.
Thus the weighted source interface, whose soundness holds for every positive
integer hstar, yields a finite ZFC refutation.

Conversely choose canonical outer and normalized strong source witnesses,
then its positive auxiliary T,u and y=V+u. Compute L,hstar,W only after
these choices. Since Df>k, hstar=4q Df+L>L+k. The weighted source theorem
supplies the positive transport witness

    r=Wt0+tau-ell-k-s>qW-2k>L,

where t0=Bt/(q-1)>=q. Set

    n=r-L-V+f+y=r-L+f+u>0.

The new Zbar equals M(tau+f+y), and N8=0. The canonical main carrier
supplies positive gamma and A1=0. There is no new congruence requirement
on the strong Pell pair. Thus this equation has a positive zero exactly
when the same inherited source has a zero.

N8 and A1 are both squares modulo four, so P11=0 iff N8=A1=0 by the
same two-unit product argument as PROOF.md. Negating solvability yields
the same ordinary mathematical equivalence with Con(ZFC), retaining all
named compiler/calibration dependencies and no consistency assumption.

## 6. Exact centered degree cancellation

Let z=Zbar-MV, used only to express the identity

    Jn=delta[z(z+2MV)-A-Bf]-M^2(V^2-1).

The degrees of Df,Q,V,L,hstar,W,z,Zbar are respectively
14,18,18,14,15,16,21,22. The leading term of Jn is uniquely
2Q0 M0 V0 z0, of degree61. The correction subtracted from Jn^2 in
Ncenter has degree102, below122; the final octic tail has degree198,
below244. Consequently deg(N8)=244 and deg(P11)=257.

Put q0=3 beta j, k0=eta+zeta, I0=i k0^2Y^2,
Df0=i^2 k0^4 X^2Y^6, Q0=i^2 k0^4 X^4Y^8,
R0=q0^3(q0-F) and Bt0=(K0q0+X)(q0-F-alpha)-q0F.
Then M0=q0^4, V0=-Df0 R0 and z0=-4q0^5 Df0 Bt0, so

    in244(N8)=2^12 Q0^4 q0^36 Df0^8 R0^4 Bt0^4.

Multiplication by the exact degree13 main-carrier head from PROOF.md shows
that the coefficient of

    j^52 i^24 eta^49 X^38 Y^85 F^4 alpha^4 gamma

is exactly 2^19(3 beta)^52>0. Minimum q0-degree forces the F^4 term of
(q0-F)^4 and the X^4 alpha^4 term of Bt0^4. This coefficient is independent
of K0,MC,MF and proves exact degree on the authentic fixed tuple, not merely
on a generic symbolic coefficient slice.

## 7. Limitations

This proof establishes a new relative ordinary construction and supplies
literal algebra/degree checks. It does not reprove the native machine
calibration or supply a Lean theorem for the final consistency equivalence.
The extra three arithmetic gates relative to the 277-degree endpoint are
reported, not concealed. The attempted four-root/ten-variable merger is
not a theorem: retaining all source residue channels remains unresolved.
