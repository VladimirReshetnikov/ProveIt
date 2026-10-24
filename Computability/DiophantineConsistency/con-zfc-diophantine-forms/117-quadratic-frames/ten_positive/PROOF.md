# A two-root consistency equation in ten positive variables

## Result and precise inherited boundary

The polynomial in `equation.json` has ten strictly positive integer unknowns,
93 binary arithmetic operations, and exact total degree 278. It has a positive
zero if and only if the pinned source-61 system has a positive zero, equivalently
(by the inherited ordinary native/compiler/calibration theorem) a finite
syntactic refutation of ZFC exists. Consequently that ordinary proof gives

    ZFC |- [no positive zero] <-> Con(ZFC).

This is an ordinary mathematical reduction. It is not a newly encoded proof
in object ZFC or a completed Lean/Rocq formalization. In particular, it is not
a proof of either consistency or absence of zeros. All sources are pinned to
ProveIt commit 84e16e43092614bae262ca59651cb9d77e31a255.

The immediate arithmetic parent is `candidates/ten-positive-zero-offset`,
whose original compact44 instance has 99 operations and degree 368. The present
instance uses the entire coherent BFS-renamed compact44 tuple from
`candidates/one-page-short10`, so that its four coefficients have a short,
closed printed recipe. The inherited coefficient-uniform proof and the
separate BFS source transfer are included. We do not identify the original
and renamed K0 numerals or replace any coefficient independently.

Square-root saturation was already used in the repository's nine-variable
folded-saturation route. The new contribution here is its use with the
adjacent-coefficient auxiliary norm, a modular noncollision proof, and an
upper center that permits the much smaller transport weight. The degree
calculation uses both exact center cancellations.

## 1. Complete polynomial

The ten unknowns are

    J,F,alpha,i,T,w,Y,n,eta,zeta > 0.

For the fixed tuple beta,K0,MC,MF, use the notation

    q=beta J+1, C=q-F-alpha, X=wq, k=eta+zeta, c=kY+eta,
    mu=q²+1, A=mu Y(X+1)+1, Delta=A²-1, H=4A-5,
    V0=X mu² Y², ell=V0 k, D=ell(ell+k)+1,
    R=[(q-1)(q-F)+alpha](q²-1)+(MC+q MF)J,
    e=k-R-1, Bt=(K0+w)C-F,
    I0=i c², Bf=1+Delta D I0², Q=Delta² D I0², delta=Q-1,
    b=c(T+alpha)-R, V=Bf b-c, Cy=Q V²-1,
    P=A I0 D, W=1+(q-1)b, Kpos=X(3c-2X)+2,
    P1=q³(q-1), M=P1 mu² H,
    Z=P1 mu²[H(n+V+P)+Kpos]
             +H[mu²((q-1)Y-q³ W Bt)-P1 e],
    s=delta Z², u=delta M² D Bf, v=M² Cy.

The single equation is

    (s-u-v)²-4uv=0.                                      (1)

Every displayed abbreviation is an integer polynomial. There are no variable
exponents, rational operations, additional existential variables, or radicals
in (1). The circuit calls I0 `I`, Bf `Df`, D `Dtau`, H `Hp`, and P `Pcenter`.
Its coefficient tuple satisfies

    beta odd, beta>=31, K0>0, 0<MC<beta<MF<2beta.

The exact rational identity used only in the proof is

    Z/M=n+V+P+Kpos/H+Y/q³-W Bt/(q-1)-e/mu².             (2)

## 2. Root extraction without a hierarchy assumption

At every positive input, q>=32, A>4, c>=3, I0>=c², D>1,
Q-1>c²-1>0, Bf>c+2, and Bf<Q-1. If b=0, then V=-c. If b!=0,
|V|>=Bf-c>1. Hence Cy>0 in both cases. Put, initially as positive
real numbers,

    r=sqrt(D Bf), y=sqrt(Cy/delta).

The identity

    (x²-a-b)²-4ab = product_(eps,eta in {+1,-1})
                    (x-eps sqrt(a)-eta sqrt(b))

shows that (1) gives Z/M=eps*r+eta*y for some signs. The prefactor is
delta² M⁴, which is nonzero. The two roots cannot coincide: if r²=y²,
then (Q-1)D Bf=QV²-1. Reducing this integer equality modulo D gives
0=-1, because D divides Q. This contradicts D>1.

A nonzero rational signed sum of two unequal positive square roots of rational
numbers makes each root rational: if x=eps*r+eta*y, then x!=0 and
2 eps*x*r=x²+r²-y². Thus r and y are rational. Since r²=D Bf is an
integer, r is an integer. Also gcd(D,Bf)=1 because Bf=1 modulo D. Unique
factorization then gives positive integers tau,f with D=tau² and Bf=f².

The adjacent-coefficient descent lemma applies to

    QV²-(Q-1)y²=1

and makes y an integer. A proof of that lemma is reproduced in the report
and retained parent. It does not require Q to be a square. Only after this
step define the genuine strong ordinate

    I=I0*tau.

Then I is a positive integer, c² divides I, and

    f²-Delta I²=1, Q=(Delta I)², V=f²b-c.

These are exactly the strong and auxiliary hypotheses used by the parent.
Notice that no independent variable for tau or I was added.

## 3. Source recovery and the shorter transport weight

The retained all-index Pell folding argument recovers c=psi_A(p), with p
positive and odd, from the strong and auxiliary equations. The first norm
gives k=2 psi_(2V0+1)(n0). Its n0=1 case would force c=2Y+1 strictly
between psi_A(1)=1 and psi_A(2)=2A, an impossibility. Therefore n0>=2 and

    c>8X mu²Y².                                        (3)

This conclusion is reached before transport, index divisibility, or parity.
It proves Kpos>0 and, using the unchanged mask bound
R<q⁴+(alpha+2)q², also

    b>0, |e/mu²|<b/2, 0<y-V<b/2.                     (4)

These estimates use only I>=c², which has just been recovered. In particular
the proof does not assume that the polynomial I0 itself is a Pell ordinate.

The key unconditional upper center is

    P²-r²=D(I0²D-1)>0.

Thus r<P. Write temporarily s0=Y/q³>0, t=Bt/(q-1), rho=e/mu²,
and kappa=Kpos/H>0, all as rational numbers. Equations (1)-(2) give

    n=eps*r-P+(eta*y-V)-kappa-s0+W*t+rho.               (5)

If Bt<=-1, then W*t<=-b-1/(q-1)<-b. Equations (4)-(5), r<P,
and eta*y-V<=y-V imply n<0. This contradicts n>0. Therefore Bt>=0,
C>0, and the unchanged masks give

    3q<R<q⁴-2.

The remainder of the parent's recovery proof has the same hypotheses:

* c²|I and the two auxiliary residues V=-c modulo f and V=-R modulo c
  yield p=R by the normalized rank and signed index lemmas.
* Odd p makes R odd. If q were odd, beta odd would make J even and the
  defining expression for R even. Thus q is even and J is odd.
* Only now apply gcd(mu²,q³(q-1)H)=1 to (2). All of n,V,P,r,y are
  integers, so mu² divides e.
* The first-norm index comparison gives n0=(R+1)/2. Writing R=2h+1,
  h>=48, the zero-offset ratio estimate gives Y>X^h/3 and X^(h+1)<H.
* Let Kquad=X(X+2(A-2)c)-1. The identity
  Kpos=H Xc-2 Kquad and H odd show H|q³(q-1)Kquad. The projection
  identity gives H|q³(q-1)(X-2^R)(2^R X+1). Its entire absolute value
  is strictly below H, so X=2^R. No nonunit projection factor is cancelled.
* The same partial fractions recover H|Kpos, q³|Y, and q-1|Bt.
  Fixed-minus parity gives R=3 modulo4, and ratio rounding identifies Y
  as the required half-binomial coefficient.

Fresh unscaled source-61 witnesses now follow exactly as in the retained
zero-offset proof. This supplies a finite refutation via the calibrated
source theorem. Positivity of J=1 is handled by that source theorem itself,
not by an inadmissible conversion to (J-1)/2>0.

For clarity, the rational estimate used above is, for a=Y(X+1),
A=mu*a+1 and Pfirst=2X mu²Y²+1,

    (X+1)^(2h)/X^h < psi_A(2h+1)/psi_Pfirst(h+1)
      < (X+1)^(2h)/X^h * (1+1/a)^(2h).

The retained zero-offset proof establishes this from the elementary Pell
growth bounds, including its strict lower comparison. Our change does not
alter A, Pfirst, c, k, X or Y.

## 4. Constructive completeness, including the new center

A finite refutation supplies canonical source data J,F,alpha,w,Y with
X=2^R, R=3 modulo4, 3q<R<q⁴-2, q³|Y, and Bt=(q-1)t for t>=0.
Use the same A, mu and first parameter as above and set

    c=psi_A(R), k=2 psi_(2V0+1)((R+1)/2),
    tau=chi_(2V0+1)((R+1)/2).

The retained ratio/rounding proof gives Y<c/k<Y+1, so eta=c-kY and
zeta=k-eta are positive integers. Also rho=(k-R-1)/mu² is a positive
integer.

We must choose a fresh strong witness; retaining an arbitrary old I is not
enough. Let L=c²*tau. The Pell matrix [[A,Delta],[1,A]] has determinant1,
so its reduction belongs to the finite group GL2(Z/LZ). A positive power
is the identity. Choose any such index m and put

    I=psi_A(m), f=chi_A(m), I0=I/tau, i=I/(c²*tau).

All are positive integers and I0=i c². This proves existence of the exact
saturated strong witness. The finite-period argument is an ordinary finite
group argument formalizable in ZFC; no exponent appears in the polynomial.

Put S=Delta I and Q=S². At the canonical odd index R define

    V*=chi_S(R)/S, y*=psi_S(R),
    T*=(V*+c+R f²)/(c f²).

The retained odd-index polynomial identities, using R=3 modulo4,
give V*=-c modulo f² and V*=-R modulo c. Since f²=1 modulo c,
T* is an integer and V*=f²(cT*-R)-c. These are exactly the original
auxiliary completeness formulas; they allow every strong I with c²|I.

Here R>=5. Monotonicity gives

    V* >= chi_S(5)/S =16Q²-20Q+5 > Q²,
    u=y*-V* = psi_S(R-1)/S >=8Q-4.

The gap identity follows from chi_S(R)-S psi_S(R)=-psi_S(R-1).
Since f²<Q and Q/c>q>alpha, we obtain T*>Q/c>alpha. Thus T=T*-alpha
is a positive integer, and the equation's V equals V*.

The projection yields the positive integer kappa=Kpos/H, with kappa<Xc.
Set s0=Y/q³>=1, keep W=1+(q-1)b, and choose

    n=Wt+rho+tau*f+u-P-s0-kappa.                       (6)

This is an integer. It is positive for the following explicit reasons.
First P<Q, since Q/P=Delta² I0/A>1. Second, (3) gives X<c/8 and Y<c,
so Xc+Y<c² for c>=3; hence s0+kappa<Xc+Y<c²<Q. Consequently
P+s0+kappa<2Q, whereas u>=8Q-4>2Q. All other terms in (6) are
nonnegative. Thus n>0. Equation (2) now equals tau*f+y*, so one factor
of the two-root norm vanishes. This constructs a positive zero.

The two directions prove equivalence of positive zero existence. No
pointwise bijection with the old positive zero set is asserted.

## 5. Exact degree 278

The four ports have degree0; the ten unknowns degree1. Let

    z=Z-M(V+P), d=P²-D Bf=(I0 D)²-D,
    B=2M(P+V)z+z²+M²d,
    C0=delta B-M²(V²-1).

The following is an exact polynomial identity, with no division:

    N = C0² +4delta M² P V C0
        -4delta M⁴ P²(V²-1)
        +4delta M⁴ d(Q V²-1).                         (7)

The relevant degrees, obtained from the actual graph and the two exact
center cancellations, are

    deg(Q)=48, deg(M)=13, deg(V)=42, deg(P)=28,
    deg(z)<=19, deg(d)=46, deg(B)<=74, deg(C0)<=122.

The four summands of (7) have degree at most244,266,240,278, respectively.
Thus deg(N)<=278. Its unique leading contribution is
4 Q0² M0⁴ d0 V0². Writing q0=beta J and k0=eta+zeta, its full value is

    2^10 q0^146 i^10 w^28 Y^60 k0^32 (q0-F)².           (8)

In particular, the coefficient of

    J^146 i^10 w^28 Y^60 eta^32 F²

is 2^10 beta^146>0. Its exponents sum to278. This proves exact total
degree278 for either complete coherent tuple. The other three fixed
ports cannot cancel the leading form.

The emitted graph has93 live binary operations:55 multiplications,
22 additions and16 subtractions. Its direct syntactic degree bound is316;
claiming that syntactic number as the exact degree would miss (7).

## 6. Scope of verification

The standalone checker verifies topology, liveness, complete formula cuts,
the two-root identity, both center identities, the entire leading form,
all four exact coefficient payloads, and independent evaluations. The
coefficient constructor reconstructs the four integers from the printed
436-character seed and finite arithmetic recipe. Separate independent
review checks the mathematical extraction, transport, completeness and
degree arguments. Finite toy Pell examples are regression controls;
they are not proofs of unbounded refutation equivalence.
