# Eleven positive unknowns by absorbing the index quotient

## Result and comparison

This construction uses exactly eleven strictly positive integer unknowns:

    J,F,alpha,z,i,T,s,w,eta,zeta,t.

It gives one polynomial of exact total degree 1154, evaluated by 123 binary
arithmetic operations, or a two-equation system of maximum degree 1152 in
119 operations. The inherited positive transport-coordinate shift gives a
two-equation version in 118 operations. All binary additions, subtractions,
and multiplications, including multiplication by a numeral, are counted;
comparisons in a system are free under the repository convention. The
generator checks that all inputs, coefficient ports, and gates are live.

The new result removes one of the twelve supplied positive unknowns and one
of the three equations in the direct, moderate-degree Pell-norm family.
It does not improve the separate Jones nine-variable bound, the cited Sun
ten-integer reduction, the minimum degree 1022 of the twelve-positive family,
or the historical minimum 67 operations for a single equation. Its novelty
is a divisibility absorption argument, not a new representation theorem.

The old index quotient h is not set to a fixed value or discarded. Its
divisibility is enforced through the already quantified carrier t. The
resulting weaker divisibility suffices because the Pell index has a short
range, and the full quotient is reconstructed later.

All four coefficient ports beta,K0,MC,MF must be a single complete authentic
normalized blank-K215 tuple, with MF the shifted high mask. They are fixed
integers, not additional unknowns. The theorem is uniform in such tuples;
the containing release must bind all four ports together. In particular,
the old materialized tuples or any separately proved improved tuple may be
used. Numerical tests with arbitrary ports have only an algebraic meaning.

## 1. Explicit polynomial

Let all eleven supplied unknowns be positive. Define polynomial abbreviations

    q=beta J+1, s0=s+3q, Cw=q-F-alpha,
    X=wq, Y=s0 q^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y,
    H=4a+3, Delta=a^2+H=(a+2)^2-1,
    ell=EkY, A=1+ell(ell+k), G=1+Delta c^2,
    b0=X+ac,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    Nt=(K0+w)Cw+q-F-z(q-1),
    I=ic^2, D=1+Delta I^2, Q=Delta(D-1)=(Delta I)^2,
    d=Q-1, v=cT, b=c+RD,
    e=Q(Dv^2+b^2)-1, Baux=2Qvb,
    Cstar=E+2(X+Y)+s0 q^2,
    M=I(2T+R Cstar i c), L0=1+HM,
    S=HE, L=E L0,
    W=L b0+H(E t+k-R-1).

Define an integer polynomial by the eight conjugate factors

    N = product over g^2=G, tau^2=A, f^2=D of
        [ d(W-Lg-SM tau)^2-S^2 e+S^2 Baux f ].       (1)

Each of g,tau,f independently takes the two formal signs. The product is
invariant under the formal sign changes and hence lies in the integer
polynomial ring. These radical symbols do not add quantified unknowns.
Formal signs are not being assumed to give independent Galois automorphisms.

The proposed single equation is

    Nt(1+N)-1=0.                                  (2)

The simpler two-equation form is

    Nt=1, N=0.                                    (3)

The generator gives a fully division-free scalar evaluator. Explicitly put

    n=(SM)^2 A, dn=d n,
    HP=S^2 Q Dv^2, HU=S^2 Q b^2, He=HP+HU-S^2,
    j=4HP HU,
    Tr=2d(W^2+L^2G), Kn=[d(W^2-L^2G)]^2,
    AA=2(dn+He), cc=(dn-He)^2-j,
    at=Tr-AA, bt=cc-Kn, co=16dn j,
    vr=co-at(at Tr+2bt), ur=bt^2-at^2 Kn,
    left=ur(Tr vr-ur), right=Kn vr^2,
    N=right-left.

For a system, the last equation is evaluated directly as left=right. The
scalar identity is the predecessor's quadratic-remainder norm identity
with H replaced by S, and does not depend on a discriminant being nonzero.

## 2. Outer bounds and unit extraction

Put x0=d(W^2+L^2G). Then Tr=2x0 and

    Kn=x0^2-4d^2 W^2 L^2G.

Consequently N=(ur-x0 vr)^2 modulo 4. At an integer zero of (2), Nt and
1+N are units. The possibility 1+N=-1 would give N=-2, contradicting this
square residue. Thus N=0 and Nt=1. Conversely (3) implies (2).

The authentic coefficient interface and Nt=1 give the standard outer bounds

    q>=16, Cw>0, q-F>0, 3q<R<q^4-2.

Here Cw>0 is immediate once Nt=1: if Cw<=0, then

    Nt <= q-F-z(q-1) = 1-F-(z-1)(q-1) <=0,

because K0+w>0. The standard bound on R then uses the native mask bounds;
no Pell root or index quotient has yet been recovered.

The deliberate shift of s gives

    Y=(s+3q)q^3 >3q^4>3R,
    X>=q>=16, E=XY>R+1,
    k>=2, kY<c<k(Y+1).

Unlike the twelve-variable proof, no assertion k>E or R<k is used at this
point. Such assertions would be circular without the deleted index equation.

## 3. A root bound that does not use the index equation

For any coherent strong and auxiliary branches,

    f^2=D,
    d y^2=e-Baux f=Q(vf-b)^2-1,

we claim

    |y|<M sqrt(A).                                 (4)

The absolute value bound applies to complex auxiliary roots and all their
conjugates. It is not restricted to the real positive branch.

Write A0=a+2 and Z=v sqrt(D)+b. The outer bounds imply Delta>R+2,
I>=c^2, and

    Q-b=Delta I^2(Delta-R)-c-R>0.

For example the first term is greater than 2Delta c^4, which exceeds
c+R because Delta>R and c>=2. Hence b<=d. Also sqrt(D)<Delta I<d.
Since Z>1,

    |y|^2 <=(QZ^2+1)/d <[Z(1+1/d)]^2,

where the numerator of the second strict difference is QZ^2-d>0.
Using b/d<=1 and sqrt(D)/d<1 gives

    |y|<Z+v+1<cT((a+2)I+1)+c+RD+1.                (5)

Set rho=(1+1/Y)/E. We have c/ell<rho and (a+3)rho<2. Dividing the
T-dependent part of (5) by sqrt(A)>ell bounds it strictly by 2TI.
The exact identity

    (a+2)^2 rho
      =E+2Y+X+6+Y/X+5/X+4/Y+8/E+4/(EY)

has a final four-term remainder less than 1. Also Y/X=s0 q^2/w<=s0 q^2.
Since X>=16, this gives

    (a+2)^2 rho<Cstar-2.

The remaining small terms satisfy (c+1)/ell<2. Therefore

    |y|/sqrt(A)
      <2TI+R(Cstar-2)i^2c^3+2
      <=2TI+R Cstar i^2c^3=M,

proving (4). These estimates are the sharp predecessor bound with its
h-dependent hypotheses removed and individually rechecked. They use only
the outer inequalities stated above.

We also have G>A and b0>sqrt(A). Indeed

    Delta c^2>k^2Y^2(E+Y)^2>k^2(E^2Y^2+EY)=A-1,

and b0=ell+E eta+Yc+X>ell+k>sqrt(A). Hence every complex root x of
the inner polynomial (product over tau,f) has

    x=M tau+y,  |x|<2M sqrt(A).                    (6)

## 4. Main root and rational-root recovery

At N=0 choose a factor with g=+/-sqrt(G) and put x=(W-Lg)/S. If
g=-sqrt(G), then

    x=t+(k-R-1)/E+(M+1/H)(b0+sqrt(G))
      >2M sqrt(A),

because t>=1, k>=2, E>R+1 make the first two terms positive. This
contradicts (6). If G were a nonsquare, quadratic conjugation of the
rational-coefficient inner polynomial would force this forbidden branch
whenever the positive branch is a root. Thus g is a positive integer and
x is rational.

Take a finite normal splitting field containing a coherent tau,f,y. If
tau is irrational, an automorphism negates tau while fixing x. Subtracting
the two equations x=M tau+y gives

    2M sqrt(A)<=|y|+|y'|<2M sqrt(A),

by (4), a contradiction. Thus tau is rational, hence an integer. Then
y=x-M tau is rational, and f=(e-dy^2)/Baux is rational because Baux>0.
Since f^2=D is an integer, f is an integer too.

The rational Pell saturation lemma now makes y integral. In the form used
here, the lemma says that if m>=2 and V are integers and y is rational with

    m^2 V^2-(m^2-1)y^2=1,

then y is an integer. To prove it, write y=u/v reduced, v>0. Then
v^2 divides m^2-1. The integer Pell equation with discriminant
(m^2-1)/v^2 has solutions (m,v) and (m|V|,|u|). If their fundamental-unit
indices are j,l, divisibility of the first abscissa by m forces l to be
an odd multiple of j: reduce l modulo 2j, reflect to [0,j], and use
strict growth together with chi_(n+2j)=-chi_n modulo chi_j. Ordinate
divisibility then gives v|u, whence v=1. The zero-coordinate cases are
excluded by the equation, and the discriminant is positive and nonsquare.

Apply the lemma with m=Delta I and V=vf-b. Thus y and x are integers.
Reducing W=Lg+Sx modulo E gives the crucial, initially weaker condition

    E divides H(k-R-1).                            (7)

No attempt is made to cancel H prematurely.

## 5. Recovering the main Pell index without the index congruence

Write chi_A0,psi_A0 for the ordinary Pell sequences for A0=a+2. Their
fundamental positive integer-coordinate unit is (A0,1), since any positive
ordinate gives an abscissa at least A0. The recovered main and strong norms
give positive integers p,m with

    g=chi_A0(p), c=psi_A0(p),
    |f|=chi_A0(m), I=psi_A0(m).

Since I=ic^2, strong divisibility first gives p|m. Write m=pj. The
composition identity gives

    psi_A0(m)=c psi_(chi_A0(p))(j).

Modulo c, chi_A0(p)^2=1, so gcd(chi_A0(p),c)=1, and
psi_(chi_A0(p))(j)=j chi_A0(p)^(j-1). Thus c|j, so in particular

    c|m, m>=pc>2p.                                (8)

This direct normalized argument needs neither a lower bound on n nor the
ordinary-strong large-c rank lemma. Also c>2Y>6R. We have p>=2, because
c>Y>1. Since A0>=3, the recurrence gives
psi_A0(p)>=(2A0-1)^(p-1)>=5^(p-1)>2p for p>=2 (or one can prove the
last inequality by induction), so c>2p.

The integral auxiliary equation is

    Q V^2-(Q-1)y^2=1,
    V=c(Tf-1)-Rf^2,
    Q=(Delta I)^2=Delta(f^2-1).

Let S0=Delta I. Pell classification at S0 shows that
S0|V|=chi_S0(j0), |y|=psi_S0(j0), where j0 is positive and odd. Write
j0=2r+1. The standard odd-index polynomial Q_r satisfies

    chi_S0(2r+1)=S0 Q_r(S0^2),
    Q_r(1-A0^2)=(-1)^r psi_A0(2r+1),
    Q_r(0)=(-1)^r(2r+1).

Modulo |f|, the identities Q=1-A0^2 and V=-c imply

    psi_A0(j0)=+c or -c modulo |f|.

Squaring and using the Pell doubling formula gives

    chi_A0(2j0)=chi_A0(2p) modulo chi_A0(m).

Because 0<2p<m by (8), signed index reduction implies

    j0=+p or -p modulo m, hence modulo c.

For completeness, reduce 2j0 modulo 2m using chi_(u+2m)=-chi_u
modulo chi_m, then reflect into [0,m]. A negative signed representative
cannot equal chi_(2p), since 2chi_(m-1)<chi_m; strict growth then forces
the representative index to be 2p. This is precisely the asserted signed
congruence and uses no positivity of f or V.

On the other hand Q is divisible by c^4, f^2=1 modulo c, and V=-R
modulo c. The identity Q_r(0)=(-1)^r j0 gives j0=+R or -R modulo c.
Combining the two congruences yields R=+p or -p modulo c. Since

    0<R<c/2 and 0<p<c/2,

we obtain

    p=R.                                          (9)

This is obtained before recovering h or the main congruence modulo H.

## 6. The short-range index argument and full compiler reconstruction

The first norm is

    tau^2-k^2 EY(EY+1)=1.

Its fundamental positive unit is (2EY+1,2): ordinate 1 is excluded by
the gap between consecutive squares, and ordinate 2 is attained. Thus,
putting P0=2EY+1,

    |tau|=chi_P0(n), k=2psi_P0(n), n>=1.

Since P0>A0 and c>k, monotonicity gives n<p=R. Define

    g0=gcd(E,H), mu=E/g0.

Because H=4XY+4Y+3,

    gcd(Y,H)=gcd(Y,3)<=3,
    gcd(XY,H) divides X gcd(Y,H),
    mu>=Y/3>R.                                    (10)

Condition (7) gives k=R+1 modulo mu. Also P0=1 modulo E, so the Pell
recurrence gives k=2n modulo E and hence modulo mu. Therefore

    2n=R+1 modulo mu.

But 1<=n<=R-1 implies |2n-R-1|<R<mu. Thus

    2n=R+1.                                       (11)

The full divisibility E|(k-R-1) now follows from k=2n modulo E. Set

    h=(k-R-1)/E.

It is an integer and positive: R>3q>=48 gives n>=25, and
k=2psi_P0(n)>2n=R+1. This restores the exact omitted index equation.

Divide the carrier identity by E:

    L0 b0+H(t+h)=L0 g+H(M tau+y).

Since L0=1 modulo H, it follows that g=b0 modulo H. Set
gamma=(g-b0)/H. This is an integer, and it is positive. Indeed n>=2
implies k>=4P0>X, hence c>X; then g>(a+1)c gives g-b0>c-X>0.

We have recovered all equations of the authentic normalized compiler:

    tau^2-ell(ell+k)=1,
    (X+ac+Hgamma)^2-Delta c^2=1,
    f^2-Delta i^2c^4=1,
    Q[c(Tf-1)-Rf^2]^2-(Q-1)y^2=1,
    k-hE-R=1, Nt=1.

Absolute values of tau and y are harmless. If needed, replace f,T
simultaneously by -f,-T. The inherited signed-quotient normalized compiler
soundness theorem extracts a blank K215 halting computation. No assumption
of consistency is used in this reconstruction.

## 7. Completeness, including both positive coordinate changes

Take a canonical positive normalized compiler witness for a blank K215
halt. Its existing theory gives X=2^R, R>3q, and Y>2^R. Since q>=16,
the elementary inequality 2^(3q)>3q^4 implies

    s_old=Y/q^3>3q.

Thus s=s_old-3q is a positive integer and preserves the same X,Y,E and
all original witness data. This is a proved restriction on canonical
witnesses, not an assumption about arbitrary prospective roots.

Define the new carrier by

    t=L0 gamma+M tau+y-h.

It is an integer and positive: h=(k-R-1)/E<k/E, whereas
tau>ell=EkY>k/E and M>=1. The identity

    W=Lg+S(M tau+y)

then holds, so the coherent factor in (1) vanishes and Nt=1. This proves
completeness for both the equation and system.

For the 118-operation system replace Nt=1 by

    (K0+w)Cw=F+z(q-1).

This means z_old=z+1. Every new solution gives an old one. Conversely
canonical compiler witnesses have Cw>0 and w=2^R/q>q>F, so
(K0+w)Cw-F>0 and the original transport equation gives z_old>=2.
Thus the shifted positive variable exists. This shift changes neither
the count eleven nor either residual degree.

Composing with the established K215 syntactic-refutation calibration and
negating existential solvability proves in ZFC that absence of solutions
to (2), (3), or the shifted system is equivalent to Con(ZFC). This is an
ordinary mathematical proof formalizable in ZFC, not a new end-to-end
Lean/Rocq certificate and not a proof deciding either side of Con(ZFC).

## 8. Exact degree certificate

Let N_old denote the sharp half-carrier norm of source35/source37, using
the original variables s0 and t_old, and the same whole coefficient tuple.
Its weighted carrier is W_old=L0 b0+H t_old. In the localization at E,

    N=E^16 N_old(t+(k-R-1)/E), s_old=s+3q.           (12)

Each of the eight factors is multiplied by E^2. Since N_old has t-degree
at most 16, denominators clear, and (12) is a genuine polynomial identity.

The predecessor proves exact degree 1056 and leading form

    (N_old)_1056
      =2^46 i^48 k0^96 w^74 s0^176 q0^646(q0-F)^16,
    q0=beta J, k0=eta+zeta.

The rational shift (k-R-1)/E has total degree -2, below the supplied
carrier's degree 1. In every monomial, replacing one t by that shift
lowers total degree by at least 3, so it cannot affect the highest form.
The affine substitution s_old=s+3q has invertible linear highest part
s0=s+3q0, so the displayed highest form remains nonzero. Since
E has leading form w s0 q0^4 and degree 6, (12) gives

    deg(N)=1056+16*6=1152,
    N_1152=2^46 i^48 k0^96 w^90 s0^192 q0^710(q0-F)^16.

The transport factor has leading form

    Nt_2=w(q0-F-alpha)-zq0,

which is nonzero for every authentic beta>0. Hence the product (2) has
exact degree 1154; the system's residual degrees are exactly 2 and 1152.
The transport shift preserves this highest form. No generic-coefficient
assumption or numeric interpolation is needed for these exact degrees.

## 9. Provenance and validation boundary

All source paths below lie under the requested report directory at commit
22e75dd6b87b1b199bb08c778d7cf075ae5aae08. The new generator is self-contained;
the inherited proofs are mathematical dependencies, not executed imports.

* 35-cancel12/sections/positive.tex: sharp weight, half carrier, norm
  evaluator, rational Pell saturation, exact degree 1056 and leading form.
* 37-wave5/positive/PROOF.md: independent sharp-weight presentation and
  explicit signed-quotient reconstruction boundary.
* 35-cancel12/sources/catalogue/25-hybrid12/upstream/ORDINARY_BLANK_PROOF.md:
  outer bounds, signed auxiliary residues, index reduction, Y>2^R,
  the full native compiler semantics, and transport shift.
* 34-integer14/positive/SHIFTED12_PROOF.md: the previous twelve-positive
  degree frontier, including degree1022 at124 operations.

The finite checker independently evaluates the formal eight-factor norm,
tests the scalar norm and carrier identities, audits every gate, checks
the mod4 finalizer and transport shift, and performs full univariate
polynomial arithmetic over two finite fields against the analytic leading
form. Parameter tests stress the bound with k=2 and arbitrarily larger X,
where the deleted hypothesis k>E is false. Such diagnostics corroborate
the transcription and algebra; the unbounded argument above supplies the
number-theoretic proof.

