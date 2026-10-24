# Radical-only strong scaling and two upper centers: 126 operations, degree 718

This is an ordinary mathematical existence-equivalence proof relative to the
same compact44 coefficient binding and the same package61 source theorem as
`candidates/ten-positive-scaled-norm/PROOF.md` at commit
`ec80841c07e91be8956ce6ed4af9a9c0b782d3d9`. It is not a proof-assistant certificate.
The original theorem is ten positive unknowns, 124 operations, exact degree816.
The new theorem keeps the ten positive unknowns, uses126 operations, and has
exact total degree718. It trades two additions for a98-degree reduction.
No global minimality or literature-wide novelty claim is made.

## 1. Definition

Use the original fixed ports and every register through the transport numerator
unless changed explicitly below. The unknowns, all strictly positive, are
`j,F,alpha,i,T,w,Y,n,eta,zeta`. In the source notation:

    J=2j+1, q=beta J+1, C=q-F-alpha, X=wq,
    a=(X+1)Y, k=eta+zeta, c=kY+eta, mu=q^2+1,
    A=mu(a+2)+1, H=4A-5, Delta=A^2-1, a'=A-2,
    V0=X mu^2 Y^2, Dtau=V0(V0+1)k^2+1,
    R=[(q-1)(q-F)+alpha](q^2-1)+(MC+q MF)J,
    e=k-R-1, Bt=(K0+w)C-F.

The strong ordinate is now `I=i c^2`: it does not contain mu. Put

    Df=1+Delta I^2, Q=Delta^2 I^2, delta=Q-1,
    T'=T+alpha, b=cT'-R, V=Df b-c,
    Dnum=Q V^2-1, Dmain=Delta c^2+1.

The two upper centers and the transport weight are

    Cf=mu A I, Ct=(V0+1)k, L=b+cT', W=1+(q-1)L.

Put `P1=q^3(q-1)`, `M=P1 mu^2 H` and

    Z=P1 mu^2 [H(n+V+Cf+Ct)+X+a'c]
       +H[mu^2((q-1)Y-q^3 W Bt)-P1 e].

Finally define

    fs=delta Z^2,
    fa=delta M^2 Dtau,
    fb=delta M^2 mu^2 Df,
    fc=M^2 Dnum,
    fd=delta (P1 mu^2)^2 Dmain,
    N=F16(fs;fa,fb,fc,fd),

where `F16` is exactly the original28-operation sixteen-fold norm. The literal
whole source is `circuit718.py`,126 rows,74 multiplications,32 additions and20
subtractions. Every row and every input is live.

The carrier identity is

    Z/M=n+V+Cf+Ct+(X+a'c)/H+Y/q^3-W Bt/(q-1)-e/mu^2.

The new conceptual move is to distinguish two uses of a scale. The old proof
put mu inside the strong Pell ordinate to separate roots. Root separation
only needs the root itself multiplied by mu. Moving that scale outside the
Pell radicand lowers the degree of the auxiliary Pell register. Upper centers
then remove the large positive terms from the transport majorant.

## 2. Unconditional root separation

Fix any positive input, without imposing N=0. All mask, modulus, first-kernel
and main-kernel bounds of originalSection5 are unchanged. In particular
`q>=16`, `mu>=257`, `a>=17`, `c>=3`, `kY<c<2kY`, and `H>X`.

Define positive roots

    tau=sqrt(Dtau), f=sqrt(Df), y=sqrt(Dnum/delta), d=sqrt(Dmain)/H,
    rf=mu f.

Here I>=c^2 and Delta>(A-1)^2. Thus

    f>(A-1)I=mu(a+2)I,   f<A I,
    rf>mu^2(a+2)c^2>V0 k c>=3V0 k.

The upper inequality f<A I follows from
`(A I)^2-Df=I^2-1>0`; I>=9. Also

    V0 k<tau<(V0+1)k=Ct, 0<d<c.

As `k+2c+1<=3c<6kY<2V0k`, we have

    rf>tau+2c+1.

Moreover f>3mu and f>2c, directly from f>mu(a+2)c^2. Consequently
`f^2-c>2mu f=2rf`, since `f(f-2mu)>mu f>c`.

If b=0 then V=-c. Because Q-1>c^2-1,
`c<y<c+1`. Also tau>V0 k>4kY>2c+1>y+d, using c<=2kY-1. Thus the roots have the superincreasing order

    d < y < tau < rf.

If b!=0, then `|V|>=Df-c=f^2-c`, and `y>|V|`. Thus the order is

    d < tau < rf < y,

again superincreasing. All radicands are positive and no nonempty signed
subsum of these four roots vanishes.

## 3. Soundness

The sixteen-fold norm identity is unchanged except that its second root is
rf. Thus N=0 gives a rational signed sum of tau,rf,y,d. The original rational
signed-sum lemma, combined withSection2, makes each root rational. Since
mu!=0, f is rational. The integer-square argument gives integral tau,f,Dm=Hd;
adjacent-coefficient descent gives integral y.

The first-index modulus argument is unchanged, because mu^2 is coprime to
q^3(q-1)H. Thus `rho=e/mu^2` is an integer. Define

    g=(eps4 Dm-X-a'c)/H, s=Y/q^3>0, t=Bt/(q-1).

The carrier equation is now

    n=(eps1 tau-Ct)+(eps2 rf-Cf)+(eps3 y-V)+g-s+Wt+rho.       (S)

First-Pell classification and main-Pell classification are unchanged. As in
original6.6, the first index cannot be1, so
`c>8 X mu^2 Y^2>=8q^5`. The unchanged mask estimate
`R<q^4+(alpha+2)q^2` implies `b=c(T+alpha)-R>0`, and hence V>0.

The auxiliary estimates still hold with I=i c^2:

    y-V<b/2, |rho|<b/2+cT'/2.

For the first inequality use `Df<Q-1`, which follows from Delta>=3 and I>=1;
then use the same difference-of-squares calculation as original6.7. The bound
on rho is purely a bound on k,R,mu and cT', so its original proof is unchanged.

A sharper bound on g is useful. Since `Dm<A c`, `a'=A-2`, `H>X`, H>3 and c>=3,

    |g| < [(2A-2)c+X]/H
        < (1/2+1/(2H))c+1
        < (2/3)c+1 <= c.

The first two parentheses in(S) are strictly negative, because tau<Ct and
rf<Cf. If Bt<=-1, then b>0 gives L>0 and W>0, and `Wt<-L`. Consequently

    n < b/2+c+b/2+cT'/2-L = c-cT'/2 <= 0,

as T'=T+alpha>=2. This contradicts n>0. Therefore Bt>=0. This is the only
transport-sign step that needs replacement.

The remaining original soundness proof,6.8 through6.18, applies with the
following explicit observations. The outer bounds on R and C follow from
Bt>=0 exactly as before. The strong Pell solution has c^2|I, so the unchanged
rank lemma gives c|m, m>2p, and then the unchanged auxiliary index lemma forces
p=R. The first index is(R+1)/2; the fixed-minus parity lemma yields R=3 mod4.
The first-kernel ratio bounds force the Archimedean projection X=2^R, then
q^3|Y and(q-1)|Bt. The unscaled reconstruction of original6.18 uses fresh
unscaled strong witnesses and is independent of the discarded factor mu.
Every source coordinate is positive. Package61's source theorem therefore
gives a finite syntactic refutation of ZFC.

No assumption that the scaled first or strong roots have their canonical
signs has been introduced. The old main-root sign argument still handles
eps4; the other three signs remain arbitrary throughout soundness.

## 4. Completeness

Start with a finite refutation and package61's canonical source solution.
All outer witnesses and the mu-scaled first/main kernels are chosen exactly
as in originalSection7. They give positive eta,zeta, integral rho>=1,
positive integral g, and integral t>=0. In particular c=psi_A(R), R=3 mod4,
R>3q, and Y is the required half-binomial.

For the strong pair choose m=R c, I=psi_A(m), f=chi_A(m).
The original composition argument proves c^2|I; hence i=I/c^2 is positive.
No mu divisibility is needed. Put S=Delta I, so Q=S^2.

The auxiliary completeness lemma gives

    V*=Q_v(S^2), v=(R-1)/2>=24,
    T*=(V*+c+R f^2)/(c f^2),
    y=V*+u, u>0, Q V*^2-(Q-1)y^2=1.

Its standard polynomial bound implies `V*>=(3Q)^v`.
The inequalities Cf<S, Ct<S, and s<S are elementary:
`mu A<Delta` gives Cf<S; Section2 gives Ct<rf<Cf; and
`s<=Y<c<I<S`. Also c<S and f^2<Q, so

    T*>V*/S^3 >=(3S^2)^v/S^3>S>alpha.

The last inequality uses alpha<q<Delta<=S. Thus T=T*-alpha is a positive
integer and V=V*.

Finally y<2V*, and

    u=(V*^2-1)/[(Q-1)(y+V*)]>V*/(4Q)>3S>Cf+Ct+s.

For the penultimate inequality, v>=2 and S>=2 already suffice.
Set

    n=Wt+rho+g+(tau-Ct)+(rf-Cf)+u-s.

All terms are integral. The first three are nonnegative, while
`u>Cf+Ct+s` and tau,rf>0 imply n>0. The all-plus factor of the norm vanishes
by the carrier identity. This constructs a positive zero of N.

The comparison uses a fixed canonical strong pair; there is no circular
choice involving the transport weight. W is evaluated only after the
witnesses above have been chosen.

## 5. Exact degree718 by formal Laurent series

For rigor, put each unknown equal to t times an independent indeterminate.
Work in K((t^-1)), where K is the rational-function field in these ten
indeterminates over the fixed coefficient field. Every radicand has a square
leading coefficient, so it has a formal Laurent square root with the chosen
leading term. The sixteen-fold norm is unchanged by sign choices.

Write O(t^d) to mean degree at most d in this Laurent field. The polynomial
register degrees are

    q1, mu2, a3, A5, H5, Delta10, I5, Df20, Q30, V24,
    Cf12, Ct9, L4, W5, M13.

Let Zrem=Z/M-V-Cf-Ct. The exact carrier identity gives

    Zrem=n+(X+a'c)/H+Y/q^3-W Bt/(q-1)-e/mu^2.

Here Zrem has degree6. Its leading form is `r0=R0 Bt0`, because
L0=-R0 and W0=q0 L0. Choose formal roots with leading terms V,Cf,Ct:

    y=V+O(t^-6), rf=Cf+O(t^2), tau=Ct+O(t), d=O(t^2).

These follow directly by expanding the square roots of the exact identities

    y^2-V^2=(V^2-1)/(Q-1),
    rf^2-Cf^2=-mu^2(I^2-1),
    tau^2-Ct^2=1-(V0+1)k^2.

Among the16 factors `Z/M-eps1 tau-eps2 rf-eps3 y-eps4 d`:

* 8 have the opposite y sign and degree24, leading term2V0;
* 4 match y but have the opposite rf sign and degree12, leading term2Cf0;
* 2 match y and rf but have opposite tau sign and degree9, leading term2Ct0;
* 2 match all three, and degree6, leading termr0.

Thus the rational product has exact degree
`8*24+4*12+2*9+2*6=270`. Multiplication by `delta^8 M^16`, of degree
`8*30+16*13=448`, gives exact degree718.

The leading form, in terms of polynomial leading forms, is

    N718 = 2^14 Q0^8 M0^16 V0^8 Cf0^4 Ct0^2 (R0 Bt0)^2.             (L)

Here V0 in(L) denotes the leading form of the auxiliary V, not the first-kernel
register named V0. For complete disambiguation define

    q0=2 beta j, k0=eta+zeta, c0=k0Y, mu0=q0^2,
    A0=mu0 w q0 Y, Delta0=A0^2, I0=i c0^2,
    Df0=Delta0 I0^2, Q0=Delta0 Df0,
    R0=q0^3(q0-F), Bt0=w(q0-F-alpha),
    Vtop=-Df0 R0, Cftop=mu0 A0 I0,
    Cttop=w q0 mu0^2 Y^2 k0, M0=4 q0^8 A0.

Then use Vtop,Cftop,Cttop in(L). Every factor is a nonzero polynomial because
beta>0. This proves exactness, not merely an upper bound. There is no reliance
on numerical interpolation for the upper bound.

## 6. Finite evidence and limits

`verify718.py` authenticates all four compact44 gzip files and decoded values,
checks the literal source topology/liveness, compares it to a separately written
formula evaluator at20 points modulo2^127-1 with the actual ports, and evaluates
four affine lines over two prime fields. The full gate-based upper bound832
allows exact finite differences on833 values; all four lines have degree718 and
the leading coefficient predicted by(L). The result is `CHECKS718.json`.

The ordinary proof inherits the existing compiler/calibration theorem. These
finite checks do not prove that theorem, do not constitute Lean/Rocq/ZFC
formalization, and do not by themselves prove the unbounded equivalence.
