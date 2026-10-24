# Adaptive main carrier and a centered auxiliary norm

## Verified candidate

Twelve **strictly positive integer** variables
`j,F,alpha,i,T,X,Y,r,eta,zeta,n,gamma`.
The polynomial has exact degree **110**, with **102 live binary operations**
(57 multiplications, 29 additions, 16 subtractions) in `adaptive_centered12.json`.
This improves the inspected package61 twelve-positive degree118/104 point.
It does not improve the nine-positive or ten-unrestricted variable counts.

The four fixed ports beta,K0,MC,MF are the **whole package44 compact tuple**,
with beta=2^590069-1 and MF already shifted. Using symbolic ports in the
builder only specifies a family until the parent packet binds those fixed
numerals. No new native compiler/calibration theorem is claimed.

### Full definition

All letters other than the twelve witnesses are polynomial abbreviations:

```
J=6j+1; q=beta J+1; C=q-F-alpha;
E=XY; k=eta+zeta; c=kY+eta; a=E+Y;
A=a+2; H=4a+3; Delta=a^2+H=A^2-1;
ell=EkY; b0=X+ac;
R=((q-1)(q-F)+alpha)(q^2-1)+(MC+qMF)J;
v=k-R-1;
W=(q-1)k+1; M0=q^3(q-1);
Bt=(qK0+X)C-qF;
Z=M0(ell+k+r)+(q-1)Y-q^3 W Bt;
A0=Z^2-M0^2[ell(ell+k)+1];
S=4qY; M=qS;
Dstar=M b0+H(M gamma-v+SX);
A1=Dstar^2-M^2(1+Delta c^2);
I=ic^2; D=1+Delta I^2; Q=Delta^2 I^2; d=Q-1;
B=cT-R; V=DB-c; t=AI+n;
U=d[(V+t)^2+D]-QV^2+1;
L=2d(V+t);
N=U^2-L^2 D;
P=(1+A0)(1+A1)(1+N)-1.
```

These are ordinary integer polynomials, with fixed powers only.

## New elementary centered-norm lemma

Let A>=2, c>=3, i,n,T>0, let R be any integer, and define Delta,I,D,Q,d,B,V,t
as above. Then D>c+1 and t^2>D. Indeed

```
(AI)^2-D=I^2-1>0.
```

Suppose N=0. We first prove L!=0 rather than divide provisionally. If L=0,
then V+t=0 and U=dD-Qt^2+1<dD-QD+1=1-D<0, contrary to N=U^2=0.
Therefore f=U/L is rational with f^2=D; rational-root integrality makes f an
integer. Set y=V+t-f. Direct expansion gives

```
d y^2=QV^2-1.
```

The signs of f,y are unrestricted. However |V|>1, since B is an integer:
B<=0 gives V<=-c, while B>=1 gives V>=D-c>1. Consequently

```
d(y^2-V^2)=V^2-1>0,
```

so u=|y|-V>0. The positive f0=|f| and u satisfy the package61 normalized
strong and auxiliary equations:

```
f0^2-Delta(ic^2)^2=1,
(V+u)^2-Delta(f0^2-1)u(2V+u)=1.
```

Thus this is a sound elimination of two positive variables f,u in favor of n.
It is not a claim that the coordinate change maps every source witness.

### Canonical completeness

Use package61's normalized canonical strong witness f and reselected auxiliary
pair V=chi_S0(R)/S0, y=psi_S0(R), with S0=Delta I, R>=5, and the
canonical parity R=3 modulo 4. The odd-index identities in retained
source/SIGNED_INDEX_LEMMA.md, section 5, give V=-c modulo f^2 and
V=-R modulo c. Since gcd(c,f)=1 and f^2=1 modulo c,
T=(V+c+R f^2)/(c f^2) is a positive integer. This is the actual newly
selected input T, and it realizes V=f^2(cT-R)-c exactly. Thus the source has
V>1 and y>V. Set n=f+y-V-AI. This is an integer. It is positive:

* f>(A-1)I, so AI-f<I.
* R>=5 and S0>=2 give
  V>=chi_S0(5)/S0=16S0^4-20S0^2+5>S0^4=Q^2.
* From d(y^2-V^2)=V^2-1, d=Q-1>=3 and V>=2, we have y<2V and
  y-V=(V^2-1)/(d(y+V))>V/(4Q)>Q/4>I.
  The last inequality follows from Q=Delta^2 I^2, Delta>=3, I>=9.

Therefore n>0. Taking t=AI+n=f+y-V gives U=Lf and hence N=0.
Unlike the package61 divided norm, this reduction needs no canonical residue
of y modulo an extra divisor; the positive gap alone supplies completeness.

## Adaptive two-stage main carrier

Retain package61's first carrier A0. It recovers q^3|Y and a transport
quotient exactly as proved there. More explicitly, tau=Z/M0 is an integer,
|tau|<ell+k, and with s=Y/q^3 and zt=Bt/(q-1),

```
tau=ell+k+r+s-W zt.
```

Hence zt>0, Bt>0, and C>0. Thus 3q<R<q^4-2. Since J=6j+1 and beta=1 mod3,
q=2 mod3. Also q is even.

Because H=4Y(X+1)+3 and q^3|Y, gcd(q,H)=1, gcd(Y,H)|3, H odd. For
mu=S/gcd(S,H), where S=4qY, we have mu>=4qY/3>R+1. Both S and
M=4q^2Y divide4XY^2 before q|X has been proved.

A1=0 makes Dmain=Dstar/M an integer. It is positive: v<k, c>kY and H<6a,
so Dstar>M ac-Hk>ak(MY-6)>0. It follows that
Dmain^2-Delta c^2=1 and M|H(SX-v). Reducing modulo S gives mu|v.

The unchanged first-Pell and normalized-strong/auxiliary argument of
package61 gives indices n0,p with k=2psi_(2XY^2+1)(n0), c=psi_A(p), n0<p,
and then p=R. Its preliminary half-interval bounds do not use q|X:
n0=1 would force eta=zeta=1 and c=2Y+1<psi_A(2); hence n0>=2,
k>8XY^2 and c>8XY^3>=8q^9>2R. Also c>2p. The direct normalized-rank lemma
supplies c|m and m>2p from f^2-Delta(ic^2)^2=1, avoiding the ordinary
strong-rank lemma's larger-growth hypothesis. The signed auxiliary lemma
then gives p=R.

The recurrence k=2n0 mod4XY^2 and mu|v imply mu|2n0-R-1. Since n0<R and
mu>R+1, this yields2n0=R+1. Consequently v is a positive multiple of
4XY^2, hence of M. Returning to M|H(SX-v) yields q|HX, hence q|X.
Restore w=X/q>0, h=v/(XY)>0, and gamma_old=gamma+w-v/M.
The restored gamma_old is integral and positive because
Dmain>(a+1)c and c>X, so H gamma_old=Dmain-ac-X>c-X>0.

The first transport quotient now restores the positive shifted old z exactly
as in package61. All other source witnesses are recovered there, using the
centered-norm lemma to furnish f,u.

For completeness take canonical source data, choose the first-carrier r as
in package61, and set gamma=gamma_old-w+v/M. Canonical v is a positive
multiple of4XY^2, so v/M>=XY/q^2=wY/q>=wq^2>w; hence gamma>0.
The same source repunit gives J=1 mod6. Reselect the auxiliary pair and n
as above. This proves both existence implications relative to the inherited
native source and syntactic-refutation calibration.

## One equation from three residuals

For every positive input q is even, so M0 is even and M is divisible4.
Therefore A0=Z^2 mod4 and A1=Dstar^2 mod4. N=U^2 mod4 since L is even.
If P=0, each of the three integer factors1+A0,1+A1,1+N is+/-1. The value-1
would make its residual-2=2 mod4, impossible for a square residue. Thus

```
P=0 iff A0=A1=N=0.
```

No nonnegativity of these residuals is assumed.

## Exact degrees

Let q0=6 beta j, k0=eta+zeta, R4=q0^3(q0-F),
Bt2=(K0 q0+X)(q0-F-alpha)-q0F. The exact highest homogeneous parts are

```
[A0]_15=-2 q0^8 k0^2 X Y^2 Bt2;
[A1]_13=32 q0^2 k0 X^2 Y^4(4q0^2Y gamma+R4);
[N]_82=4 i^10 k0^20 X^12 Y^32 R4^2.
```

For N, work first in the cut ring Z[A,i,c,B,n] with weights(2,1,2,4,1).
The exact sparse expansion contains455 monomials and its weighted degree82
part is exactly4 A^12 i^10 c^20 B^2. Substitution
A=a+2, c=kY+eta, B=cT-R gives the stated top homogeneous part.

Thus degree(P)<=110. Its degree110 part is the product of the displayed
three forms, and the coefficient

```
[j^18 eta^23 X^16 Y^39 i^10 alpha gamma F^2] P
    =1024(6 beta)^18>0.
```

This certifies exact degree for every authentic beta>0, not just for generic
symbolic coefficient ports. Named registers are not additional unknowns.

## Comparison and evidence scope

Package61 at pin9cca523d9f27ad39d52993f4065cbd7e58f8bdd4 has12positive,
degree118,104operations. This construction has12positive,110,102. The
thirteen-positive intermediate with the adaptive carrier has degree30
instead of package61's34; its circuit has not been minimized here.

The new existence reductions have ordinary mathematical proofs as above.
The native compiler, calibration to syntactic refutations, and the named
Pell classification/rank/auxiliary lemmas remain inherited. No new proof
assistant or object-language ZFC certificate is asserted. The improvements
are within the inspected repository, not a worldwide priority or global
simplicity claim. Further work should independently audit the proof and
bind/rebuild the exact compact numeral tuple in the delivery packet.
