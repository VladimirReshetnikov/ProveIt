# Two divisibilities and an index quotient in one Pell root

## Result and scope

The polynomial specified below has **fourteen strictly positive integer
unknowns**, exact total degree **26**, and a literal evaluator with **92
binary arithmetic operations**. A second polynomial has fourteen positive
unknowns, exact degree30, and85 operations. The universal mathematical
equivalence is proved relative to the explicitly supplied ordinary compiler
and Pell lemmas. For the complete authentic coefficient tuple, ordinary
mathematics formalizable in ZFC proves that either polynomial has a positive
zero exactly when the fixed ZFC proof calculus has a finite refutation.
Negation gives the requested equivalence with syntactic Con(ZFC).

This is not a newly kernel-checked Lean/Rocq proof or an exported derivation
in the repository's object-language ZFC calculus. Finite checks below verify
literal circuits, constants, identities, degrees and provenance; they do not
establish the unbounded compiler theorem by testing.

The comparison snapshot is ProveIt commit
`beb0192cb8dc36f78c369c080f2adfbc1887a486`. Package59 supplies a
fourteen-positive degree52/79 point; package58 supplies fifteen-positive
degree24/90, degree26/88 and degree30/79 points. Our fourteen-positive
degree26/92 and degree30/85 points are new tradeoffs within this inspected
collection. No global simplicity minimum, worldwide priority, smaller
nine-positive variable bound, or consistency/inconsistency proof is claimed.

## 1. Complete fixed coefficient binding

Use the **whole** compact tuple `wang943-complement67-shared-anchor-length8807-prime581197`
from package44. Put B=2^590069 and beta=B−1. The other ports are
K0=DC+B DR, MC, and MF=MF_native+B−1. The high mask is already shifted.
The four binary payloads, recipes, literal K215 transitions and tiles, exact
source pins, native mathematical adapter and an independent finite auditor
are included under `coefficients/`. `COEFFICIENT_BINDING.json` records every
raw/compressed hash and byte count. They are fixed numerals, not unknowns.

The generic ordinary source interface requires B=2^d, d>=4,
0<MC,MF_native<B−1, MC=2 modulo4, MF_native=4 modulo8, and
popcount(MC)+popcount(MF_native)=d. The authentic adapter supplies these
conditions, its native computation semantics, and canonical completeness.
Its padding witnesses have q=B^N and J=1+B+...+B^(N−1), with
N=581197^n odd and greater than1. Since590069 is odd, beta=1 modulo3.
These additional congruences are used only where stated.

## 2. The degree26 polynomial

The fourteen inputs, all strictly positive, are

    j,F,alpha,z,f,i,T,x,Y,r,eta,zeta,u,gamma.

Every other name in the following display is a polynomial abbreviation:

```
J=3j+1; q=beta J+1; C=q-F-alpha; X=x+q;
E=XY; k=eta+zeta; c=kY+eta; a=E+Y;
H=4a+3; Delta=a^2+H=(a+2)^2-1; ell=EkY;
R=((q-1)(q-F)+alpha)(q^2-1)+(MC+qMF)J;
S=4qY; M=qS=4q^2Y; v=k-R-1;
Dstar=M(X+ac)+H(M gamma-v+SX);
U=Delta(f^2-1); I=ic^2; V=f^2(cT-R)-c;

A0=[q^3(ell+r)+Y]^2-q^6[ell(ell+k)+1];
Am=Dstar^2-M^2(Delta c^2+1);
At=q[K0 C-F-z(q-1)]+XC;
Aa=(V+u)^2-Uu(2V+u)-1;
As=I^2-U;

P26=A0^2+Am^2+At^2+Aa^2+As^2.
```

This is an integer polynomial, with no variable exponent, radical, division,
quantified intermediate register or unspecified coefficient. The literal
DAG is `circuits/p14_degree26.json`. Multiplication by a fixed numeral is
charged as an operation; fixed numeral leaves and reuse are free.

## 3. Why the nested root carrier works

The first equation A0=0 implies q^3 divides Y: if an integer n satisfies
n^2=q^6 A with integer A, then q^3 divides n, since a rational square root
of an integer is integral. Thus s=Y/q^3 is a positive integer and
tau=ell+r+s satisfies tau^2=ell(ell+k)+1.

The restriction J=3j+1 makes q=2 modulo3. Since q divides Y and
H=4Y(X+1)+3, gcd(q,H)=gcd(q,3)=1. Moreover H is odd and
gcd(Y,H) divides3, whence

    gcd(S,H) divides3,   mu=S/gcd(S,H)>=4qY/3.

For Y>=q^3 and R<q^4−2 this gives mu>R+1. Both S and M divide4XY^2:
for M this follows from 4XY^2/M=XY/q^2=Xsq. Crucially this argument
does **not** yet assume q divides X.

From Am=0, g=Dstar/M is an integer. Reducing M g=Dstar modulo S
gives S | H(k−R−1), so mu | k−R−1. After the Pell indices are recovered
below, this determines k−R−1 as the canonical multiple of4XY^2. In
particular M divides v. Then reduction modulo M gives

    M | HSX,  hence q | HX,  hence q | X.

Thus the single monic root restores both the omitted index quotient h and
the omitted divisibility quotient w. The order is essential: no use of
q|X is made while establishing the index congruence.

## 4. Soundness, with the bootstrap in full

Suppose P26=0. All five integer squares are nonnegative, so every residual
vanishes. Restore Y=sq^3 and tau as above. The cleared transport At=0 is

    (K0+X/q)C=F+z(q−1).

Its right side and its leading coefficient are strictly positive, even
before X/q is known integral. Hence C>0. The ordinary mask estimates
therefore give q>=16 and

    q(q^2−1)<R<q^4−q^3+q^2−1<q^4−2,  R−2>3q+1.

These estimates use only the positive rational coefficient K0+X/q in the
transport argument. They follow directly from
G=(q−1)(q−F)+alpha=q alpha+(q−1)C,
q<=G<=q^2−q, and
0<(MC+qMF)J<(q−1)(1+2q). The deliberately supplied coordinate
X=x+q gives X>q *before* divisibility recovery, so

    E=XY>q^4>R+2,  a>R+2,  a+2<2E.

The eta,zeta parametrization gives k>=2 and kY<c<k(Y+1).

The monic-root lemma applied to Am=0 gives integer g=Dstar/M.
It is positive: with b0=X+ac, v<k, b0>akY and H<5a,

    Dstar>M b0−Hk>ak(MY−5)>0.

Thus g^2−Delta c^2=1. Together with the first norm, elementary Pell
classification gives positive indices n,p such that

    tau=chi_P(n),  k=2 psi_P(n),  P=2XY^2+1,
    g=chi_A(p),    c=psi_A(p),    A=a+2.

The first fundamental positive solution is (2XY^2+1,2) for discriminant
XY^2(XY^2+1); a second coordinate1 is excluded by consecutive squares.
Since P>A and c>k, monotonicity gives p>n.

The recurrence gives k=2n modulo4XY^2. Since S divides4XY^2 and
mu dividesS, the carrier congruence gives

    2n=R+1+t mu

for an integer t. The strict inequalities 0<R+1<mu and n>0 force t>=0.
Consequently n>24 and p>=26. These facts imply all hypotheses of the
ordinary strong-rank lemma in `upstream/ORDINARY_KERNEL.md`, Sections4–5:

    c>A(A^2−1)^2,  c>2p,  c>2R.

For the first bound it suffices to use p>=6 and
psi_A(6)=32A^5−32A^3+6A>A(A^2−1)^2. The second follows from ordinary
Pell growth for A>=3 and p>=2. For the third use c>=psi_A(2)=2A>2R.

As=0 gives U=I^2 with I=ic^2>1, so f>=2. The cited strong-rank lemma
applied to (ic^2)^2=Delta(f^2−1) gives an index m with

    f=chi_A(m),  p|m,  c|m,  m>2p,
    I=Delta psi_A(m),  c^2 | f^2−1.

The last divisibility is a conclusion of that lemma; one must not obtain it
by informally cancelling Delta. The inherited source includes the proof,
including the possibly nonfundamental squarefree-Pell parameter case.

The auxiliary residual Aa=0 is exactly

    I^2 V^2−(I^2−1)(V+u)^2=1.

It excludes V=0 and V+u=0. Put y=abs(V+u)>0. Our quotient gives
V=−c modulo f and V=−R modulo c, the latter using c^2|f^2−1.
Also c^2 divides I. The signed auxiliary-index lemma from the same source
now applies: the auxiliary Pell index is congruent to ±p and ±R modulo c;
the bounds 0<p,R<c/2 force p=R. This does not assume V positive.
For compatibility with the ordinary source quotient, set T_old=fT>0.

Since n<p=R, the multiple 2n−R−1 of mu has absolute value less than
R<mu. It therefore vanishes. Thus 2n=R+1 and

    v=k−R−1=k−2n

is a positive multiple of4XY^2. Positivity follows from n>=2 and
psi_P(n)>n. In particular M|v. The carrier calculation of Section3 now
gives q|X. Set w=X/q>0 and h=v/E>0. They are integers.
Restore

    gamma_old=gamma−v/M+w.

This is an integer, and g=X+ac+H gamma_old. Because n>=2,
k>=4P>X, hence c>X; and g>sqrt(Delta)c>(a+1)c. Therefore
gamma_old>(c−X)/H>0. The shifted transport equation is now exactly
(K0+w)C=F+z(q−1), with old source coordinate z_old=z+1.

We have recovered all strictly positive ordinary source witnesses:
J,F,alpha,z_old,f,h,i,T_old,s,w,tau,eta,zeta,y,gamma_old.
They satisfy all six source factors equal to1. The identified ordinary
compiler theorem extracts a blank K215 halt and hence a finite refutation
of the specified ZFC calculus. This proves soundness.

## 5. Completeness, with each positive replacement justified

Conversely a finite refutation supplies the canonical normalized witnesses
of the authentic compact adapter. Transfer the strong coordinate by
i=Delta i_normalized, as in package58. Then
I=ic^2, I^2=Delta(f^2−1), c|I and f^2=1 modulo c.
Canonical indices have p=R=2n−1, n>=3, R=3 modulo4,
X=2^R, Y=sq^3, and k>XY. These are inherited facts, proved in the supplied
ordinary source/native adapter, rather than observations from finite tests.

Because590069 and N=581197^n are odd, the geometric sum
J=1+B+...+B^(N−1) is1 modulo3 and greater than1. Thus j=(J−1)/3>0.
Canonical X=2^R with R>3q gives x=X−q>0. The source proves w>q>F,
which makes its unshifted transport coordinate z_old>=2; set z=z_old−1>0.

Supply Y directly. Put r=tau−ell−s. Since ell>k, the first norm gives
tau<ell+k and

    tau−ell=(ell k+1)/(tau+ell)>k/3>XY/3>s.

Thus r>0, and A0=0. As above, v=k−2n is a positive multiple of4XY^2,
so v/M is an integer. Define gamma=gamma_old+v/M−w. The positive
multiple v is at least4XY^2, so

    v/M>=XY/q^2=wY/q>=wq^2>w.

Thus gamma>gamma_old>0. The resulting Dstar is exactly M g, proving Am=0.

The new auxiliary witnesses use the squared-modulus reconstruction of
package58. Write R=2r0+1 with r0 odd. The elementary odd Pell polynomial
Q_r satisfies

    chi_t(2r+1)=t Q_r(t^2),
    Q_r(0)=(-1)^r(2r+1),
    Q_r(1-A^2)=(-1)^r psi_A(2r+1).

Take V*=chi_I(R)/I and y*=psi_I(R). They are positive integers,
I^2 V*^2−(I^2−1)y*^2=1, and V*>1. The displayed identities give
V*=−c modulo f^2 and V*=−R modulo c. Since gcd(c,f)=1, the number

    T=(V*+c+Rf^2)/(cf^2)

is a positive integer. It makes V=V*. Moreover
(I^2−1)(y*^2−V*^2)=V*^2−1>0, so u=y*−V*>0. Thus Aa=0.
The unchanged strong condition gives As=0, and the shifted transport gives
At=0. Every input of P26 is positive and P26 vanishes. This proves the
converse existence implication without changing the fixed coefficient tuple.

## 6. Exact degree and operation count

The residual degrees are respectively11,13,3,13,10 for
A0,Am,At,Aa,As. To expose the necessary cancellations use

```
A0=q^6[r^2+ell(2r−k)−1]+2q^3(ell+r)Y+Y^2;
Dold=X+ac+gamma H; L=−v+SX;
Am=M^2[(X+gamma H)^2+2ac(X+gamma H)−Hc^2−1]
   +2M Dold H L+H^2L^2.
```

These are exact polynomial-ring identities, not identities restricted to
solutions. All inputs have degree1 and all fixed ports degree0. Put
q0=3 beta j, X0=x+q0, k0=eta+zeta, and R4=q0^3(q0−F).
Only Am^2 and Aa^2 contribute to degree26, and their homogeneous leaders are

    [Am]_13=32 q0^2 k0 X0^2 Y^4 (4q0^2Y gamma+R4),
    [Aa]_13= 2 X0^2 Y^2 f^4 u R4.

Thus

    [P26]_26=[32 q0^2 k0 X0^2 Y^4 (4q0^2Y gamma+R4)]^2
                 +[2 X0^2 Y^2 f^4 u R4]^2.

This is nonzero for the authentic beta>0. For example the coefficient of
x^4 Y^4 f^8 u^2 j^6 F^2 is exactly4(3 beta)^6>0; the main-root
square contains no f or u and cannot affect this coefficient. This proves
exact degree26 for the fixed instance, not a generic upper bound.

The literal92-gate circuit has49 multiplications,27 additions and16
subtractions. No fixed power is treated as one gate, and all gates are live.

## 7. The degree30/85 tradeoff

Use fourteen positive inputs J,F,alpha,z,f,i,T,w,Y,r,eta,zeta,u,gamma.
Now q=beta J+1, X=wq, and keep the other common abbreviations. Put
M=4qY, v=k−R−1, Dstar=M(X+ac)+H(M gamma−v), and
At=(K0+w)C−F−z(q−1). Retain A0,Am,Aa,As and the five-square sum.
The literal circuit is `circuits/p14_degree30.json`.

No restriction modulo3 on J is needed. After q^3|Y, a prime common to qY
and H must be3. If3|q then27|Y, so H=3 modulo27 and its3-adic
valuation is exactly1. If3 does not divide q, gcd(q,H)=1 and
gcd(Y,H)|3. Since H is odd, gcd(4qY,H)<=3 in either case.
Consequently M/gcd(M,H)>R+1, and M divides4XY^2. The same ordered
index argument recovers p=R and 2n=R+1, then
h=v/E>0 and gamma_old=gamma−v/M>0. Completeness takes
gamma=gamma_old+v/M>0. The first and auxiliary gaps are unchanged.

The residual degrees are12,14,2,15,10. With q0=beta J,
X0=wq0 and R4=q0^3(q0−F), only Aa^2 reaches degree30:

    [P30]_30=4 X0^4 Y^4 f^8 u^2 R4^2.

The coefficient of w^4 J^10 Y^4 f^8 u^2 F^2 is4 beta^10>0.
The provided evaluator has45 multiplications,24 additions and16
subtractions, totaling85 gates. It exchanges four degrees for seven gates.

## 8. Logical boundaries and further work

The new root carrier proves the two existential equivalences by reconstructing
integer witnesses in both directions. It is not a same-coordinate identity
with arbitrary predecessor witnesses. The cofinal J restriction, positive
X shift, positive transport shift, and fresh auxiliary Pell witnesses are
all justified above; omitting any of these justifications would leave a gap.

The new assertions use elementary divisibility, rational-root integrality,
finite recurrences and the identified ordinary rank/encoding theorems.
They are formalizable in ZFC without assuming Con(ZFC). The inherited
calibration supplies the fixed syntactic consistency interpretation. A
future proof-assistant certificate must formalize this actual carrier and
its native adapter; the existing closed nine-variable Lean theorem does not
automatically certify a different literal polynomial.

Useful next questions are whether the two congruence levels can share a
smaller modulus, whether an auxiliary root can remove a further positive
coordinate without losing the degree advantage, and whether the fourteen-
variable circuit admits a lower-cost nonnegative combination of its five
residuals. Any such step must preserve the ordered recovery of p=R before
using q|X. Global minimality remains entirely open.
