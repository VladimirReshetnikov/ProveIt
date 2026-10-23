# Eleven positive unknowns: a lean carrier and the smaller absorption modulus

## Result and dependency boundary

The recommended equation uses exactly eleven strictly positive integer unknowns,
has exact total degree 954, and is evaluated by 113 binary arithmetic operations.
Its two-equation version has maximum residual degree 952 in 109 operations;
the inherited positive transport shift saves one further operation.
It improves the upstream eleven-positive degree-1140/129-operation companion
and degree-1154/123-operation main form on both measures. It does not establish
a ten-positive-variable result or a global lower bound.

Three changes are proved here: the inner-separator-free norm still works before
recovering the omitted index quotient; the absorption modulus can be Y instead
of E=XY; and a lean carrier K=IT, delta=ell improves the predecessor's carrier.
The latter also gives a separate twelve-positive degree-897/108-operation form.

All four coefficients beta,K0,MC,MF are fixed, not supplied unknowns. They must
be the entire coherent native tuple in COEFFICIENT_BINDING.json, whose payloads
are in the sibling coefficients directory. It is the independently regenerated
package39/44 complemented, shared-anchor tuple with base 2^590069. MF is the
already-shifted MF_source. No individual coefficient may be changed in isolation.
The numerical identities and new reduction are uniform in any complete authentic
normalized compiler tuple. The inherited native compiler and K215 syntactic
refutation calibration remain mathematical dependencies, not newly checked
proof-assistant certificates. No consistency assumption enters this reduction.

## 1. Literal integer polynomial

All eleven inputs J,F,alpha,z,i,T,s,w,eta,zeta,t are positive. Define

    q=beta J+1, s0=s+3q, Cw=q-F-alpha,
    X=wq, Y=s0 q^3, E=XY, k=eta+zeta, c=kY+eta,
    a=E+Y, H=4a+3, Delta=a^2+H=(a+2)^2-1,
    ell=EkY, A=1+ell(ell+k), G=1+Delta c^2, b0=X+ac,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    Nt=(K0+w)Cw+q-F-z(q-1),
    I=ic^2, D=1+Delta I^2, Q=(Delta I)^2, d=Q-1,
    v=cT, b=c+RD, e=Q(Dv^2+b^2)-1, Baux=2Qvb,
    K=IT, u=k-R-1, S=HY,
    L=Y(1+HK), W=Yb0+H[Y(t+b+ell)+u].

Define the polynomial N by the eight formal factors

    N=product [d(W-Lg-S tau)^2-S^2 e+S^2 Baux f],
       g=+/-sqrt(G), tau=+/-sqrt(A), f=+/-sqrt(D).

Every sign is included. This is a formal invariant product over an integer
polynomial ring, so it is an integer polynomial, with no additional quantified
radical or register variables. Independent signs do not assert independent
Galois automorphisms after specialization.

The single equation and two-equation system are respectively

    P=Nt(1+N)-1=0;                 Nt=1, N=0.

The inert JSON circuits implement a division-free evaluation. Put

    dn=d S^2 A, HQ=S^2 Q,
    HP=HQ Dv^2, HU=HQ b^2, He=HP+HU-S^2, j=4HP HU,
    Tr=2d(W^2+L^2G), Kn=[d(W^2-L^2G)]^2,
    AA=2(dn+He), cc=(dn-He)^2-j,
    at=Tr-AA, bt=cc-Kn, co=16dn j,
    vb=co-at(at Tr+2bt), ur=bt^2-at^2 Kn,
    N=Kn vb^2-ur(Tr vb-ur).

This is the universal quadratic-remainder identity used in package44, with
its scaling H replaced by S. It is valid even for zero or square radicands.
The system compares its last two terms directly, rather than subtracting.
Every binary addition, subtraction and multiplication, including multiplication
by a literal, is charged; comparisons themselves are not charged.

## 2. Unit guard and bounds without an index quotient

Let x0=d(W^2+L^2G). Since Tr=2x0 and Kn=x0^2 modulo 4,
N=(ur-x0 vb)^2 modulo 4. A zero of P gives integer units Nt,1+N.
The option N=-2 is impossible, so N=0 and Nt=1. Conversely the system gives P=0.

The authentic outer compiler interface gives, before recovering any Pell root,

    q>=16, Cw>0, q-F>0, 3q<R<q^4-2,
    X>=q, Y=(s+3q)q^3>3q^4>3R,
    E=XY>R+1, k>=2, kY<c<k(Y+1), a+2<2E.

In particular c>2Y>96 and I>=c^2. Neither k>E nor R<k is assumed here.
The positivity of Cw follows from Nt=1: if Cw<=0, then
Nt<=q-F-z(q-1)=1-F-(z-1)(q-1)<=0. The remaining R bounds use the
inherited whole-tuple native mask bounds, just as in package38.

Write g=sqrt(G), f=sqrt(D), tau=sqrt(A) for positive real roots in bounds.
Then g<(a+2)c<2Ec and f<(a+2)I<2EI. Direct expansion gives

    1<A<Delta c^2<=Delta I=sqrt(Q),             (1)

since Delta c^2-A>k^2[EY(2Y^2-1)+Y^4]-1>0.
Also c<I^2, R<E and D<4E^2I^2 imply

    b+cf<6E^3I^2,      d>(1/2)E^4I^2,
    (b+cf)/d<12/E.                             (2)

The decisive sharpened comparison, replacing package44's use of k>E, is

    Ig-cf=(I^2-c^2)/(Ig+cf)
          >I^2/(4Ig)>I/(8Ec)=ic/(8E)>12/E.   (3)

Here Ig>cf follows from the positive numerator, I>=c^2 and c>=2 justify
I^2-c^2> I^2/2 and Ig+cf<2Ig, and ic>96 gives the last inequality.
Thus Ig-cf>(b+cf)/d. This is weaker than Ig-cf>1, but precisely sufficient.

## 3. Outer recovery with the lean carrier

For formal x define

    C(x)=d(x^2+A)-e,
    F(x)=[C(x)^2+D Baux^2-4d^2 x^2 A]^2-4C(x)^2 D Baux^2.

Its roots have a coherent description x=tau'+y, (tau')^2=A, (f')^2=D,
d y^2=Q(vf'-b)^2-1. This description follows by factoring quadratics,
not by division. It includes complex auxiliary y.

For Z=b+vf>1, |y|^2<=[QZ^2+1]/d and |y|<Z+Z/d, since the squared
difference is (QZ^2-d)/d^2>0. Since T>=1, Z<=T(b+cf), so (2)-(3) give

    |y|<b+Tcf+T(Ig-cf)=b+ITg,
    |x|<tau+b+ITg.                             (4)

At N=0, some sign g' gives F((W-Lg')/S)=0. A negative choice would give

    x=b+ITg+(t+u/Y)+ell+(b0+g)/H.

We have t+u/Y>0 because k>=2 and Y>3R. Also tau<ell+k (k>=2), whereas

    (b0+g)/H>2ac/(4a+3)>c/3>k.

The last inequalities use a>=2, c>kY and Y>3. Thus x exceeds the upper
bound in (4), a contradiction. If G were nonsquare, actual quadratic
conjugation of Q(sqrt(G)) would take the positive-sign root of the rational
polynomial F to this forbidden negative-sign root. Therefore g is a positive
integer and x=(W-Lg)/S is rational.

## 4. Inner roots and rational Pell saturation

The exceptional-root exclusion from package44 applies unchanged and needs only
(1). If C(x)=0 at F(x)=0, substituting x^2=e/d-A gives the integer identity

    d^2 A^2-d e A+Q^2v^2b^2D=0.

Reduction modulo Q would force Q|A(A-1), impossible since 0<A(A-1)<Q.
Similarly F(0)=0 would imply Q|(A-1)^2, again impossible. Thus x,C(x)
are nonzero. Define

    U=C(x)^2+D Baux^2-4d^2x^2 A,
    f'=-U/(2C(x)Baux),
    tau'=(C(x)+Baux f')/(2dx), y=x-tau'.

All denominators are nonzero. The polynomial identity gives (f')^2=D,
(tau')^2=A and d y^2=Q(vf'-b)^2-1. These rational square roots are integers.

The inherited Pell saturation lemma says that m>=2, V integers and y rational
with m^2V^2-(m^2-1)y^2=1 imply y integer. For clarity, writing y=p/r reduced
gives r^2|m^2-1. The integer-coordinate Pell equation with discriminant
(m^2-1)/r^2 has solutions (m,r) and (m|V|,|p|). If their fundamental-unit
indices are j,l, divisibility of their abscissas forces l an odd multiple of j:
reduce l modulo 2j, reflect to [0,j], and use chi_(n+2j)=-chi_n modulo chi_j
and strict growth. The ordinate addition law then gives r|p, hence r=1.
The discriminant is positive nonsquare and the zero-coordinate cases are
excluded by the equation. Apply this lemma with m=Delta I and V=vf'-b.
Thus y and x are integers.

Reducing W=Lg+Sx modulo Y now gives only

    Y divides H(k-R-1).                         (5)

No cancellation of H and no recovery of gamma or h occurs yet.

## 5. Index recovery, then the smaller absorption modulus

The remainder of package38's signed index argument applies before using (5).
Here are its needed steps and their order. Put A0=a+2. The main and strong
norms give positive indices p,m with g=chi_A0(p), c=psi_A0(p),
|f'|=chi_A0(m), I=psi_A0(m). From I=ic^2 and strong divisibility p|m;
write m=pj. The composition formula modulo c shows c|j, so c|m and m>2p.
Since c>1, p>=2; recurrence growth gives c>2p. Also c>2Y>6R.

For the auxiliary equation QV^2-(Q-1)y^2=1, with
V=c(Tf'-1)-R(f')^2, classification at Delta I gives an odd index j0.
The standard odd-index polynomial satisfies

    chi_s(2r+1)=s Q_r(s^2),
    Q_r(1-A0^2)=(-1)^r psi_A0(2r+1),
    Q_r(0)=(-1)^r(2r+1).

Modulo |f'|, Q=1-A0^2 and V=-c; signed index reduction, using 2p<m,
gives j0=+p or -p modulo m, hence modulo c. Modulo c, Q=0 and V=-R,
so j0=+R or -R modulo c. Because p,R are positive and below c/2, p=R.
These steps do not require either main congruence modulo H or the index equation.

The first norm tau'^2-k^2 EY(EY+1)=1 has fundamental integer-coordinate
unit (2EY+1,2). Thus, with P0=2EY+1,
|tau'|=chi_P0(n), k=2psi_P0(n), n>=1. As P0>A0 and c>k, monotonicity
forces n<p=R. In particular 1<=n<=R-1.

Now set mu=Y/gcd(Y,H). Since H=4Y(X+1)+3,

    gcd(Y,H)=gcd(Y,3)<=3,       mu>=Y/3>R.       (6)

Equation (5) gives k=R+1 modulo mu. Since P0=1 modulo Y, the Pell
recurrence gives k=2n modulo Y, hence modulo mu. Consequently
2n-R-1=0 modulo mu. Its absolute value is strictly below R<mu, so

    2n=R+1.                                    (7)

This is the new smaller-modulus absorption. The final full divisibility does
not get weakened: P0=1 modulo E also gives k=2n modulo E, so E|k-R-1.
Set h=(k-R-1)/E. It is an integer and positive because R>48 gives n>=25
and k=2psi_P0(n)>2n=R+1.

Divide the carrier identity by Y, using u/Y=hX:

    b0+H(t+b+ell+hX)=(1+HK)g+H(tau'+y).

Reduction modulo H gives g=b0 modulo H. Thus gamma=(g-b0)/H is an
integer. Since n>=2, k>=4P0>X; hence c>X and g>(a+1)c, so gamma>0.

All normalized compiler equations have now been recovered, with Nt=1 and
k-hE-R=1. Absolute values of tau',y are harmless; if f'<0, replace
f',T simultaneously by their negatives. The inherited signed-quotient
soundness theorem permits this signed T and extracts a blank K215 halt.
This invokes precisely the same signed-quotient boundary as packages38 and44.

There is also a direct explicit bridge to the pinned ordinary signed theorem:
set i_ordinary=Delta*i and I_ordinary=i_ordinary*c^2=Delta*I. Then
I_ordinary^2=Delta((f')^2-1)=Q, so its ordinary strong equation and auxiliary
equation are exactly satisfied. Every coordinate required positive by that
theorem remains positive. Its Section 2 permits h,f,T,tau,y,gamma to be signed,
and Sections 5-7 prove extraction without restoring a positive T. Thus no
unquoted stronger signed-normalized theorem is being smuggled into the argument.

## 6. Completeness and all positive coordinates

Take a canonical positive normalized compiler witness. Its theory gives
X=2^R, Y>2^R and R>3q. Since q>=16 and 2^(3q)>3q^4,
s_old=Y/q^3>3q, so the supplied s=s_old-3q is positive and integral.
Keep all the other retained coordinates and put

    t=gamma+ITg+tau+y-b-ell-hX.

This is integral. The auxiliary Pell equation gives
y>=|vf-b|>=b-vf. Moreover ell>k and tau<ell+k give

    tau-ell=(ell k+1)/(tau+ell)>ell k/(2ell+k)>k/3,
    hX<k/Y<k/3.

Using Ig>cf from the exact identity in (3),

    t>=gamma+T(Ig-cf)+(tau-ell)-hX>0.

The carrier identity W=Lg+S(tau+y) follows immediately, so a coherent
norm factor vanishes and Nt=1. No Pell index is enlarged, and no new
unproved divisibility is imposed on a canonical witness.

The shifted two-equation version uses
(K0+w)Cw=F+z(q-1), corresponding to old z=z+1. Every new positive root
gives an old one. For canonical witnesses, Cw>0 and w=2^R/q>q>F make
(K0+w)Cw-F>0, so old z>=2 and the shifted variable is positive.

Existence is therefore equivalent to blank K215 halting. Composing with
the inherited syntactic-refutation calibration and negating proves in ZFC:
the displayed positive equation has no solution if and only if Con(ZFC).
This is a proof of the equivalence, not of either truth value.

## 7. Exact degree, including the lean-carrier cancellation

First omit absorption and the s shift, using the twelve-positive norm
W0=b0+H(t+b+ell), L0=1+HIT and scale H. Set leading forms

    q0=beta J, X0=wq0, Y0=sq0^3, E0=X0Y0,
    k0=eta+zeta, c0=k0Y0, I0=ic0^2, ell0=E0c0, H0=4E0,
    d0=E0^4 I0^2, B=R0 E0^2 I0^2,
    R0=q0^3(q0-F), V=I0 T ell0.

Degrees are H:6, ell:11, d:46, B:38, V:23. Formal positive-leading
Laurent expansions give

    tau-ell=k/2+lower degree terms,
    (b0+g)/H=c0/2+terms of degree below5,
    (b0-g)/H has degree -1,
    T(Ig-cf)=iT c0/(2E0)+terms of degree below1.

The last equality follows directly from (Ig)^2-(cf)^2=I^2-c^2.
These expansions are only used for polynomial-degree proofs, not to claim
numerical square roots are rational.

For each conjugate factor let Z=W0-Hb-H sa tau-L0 sg g. Then the factor is

    2dHbZ+dZ^2-H^2b^2-H^2QDv^2+H^2+sf 2H^2Qb vf.

Four factors, sf unequal to sg, have degree119 and leading form
-sg 4H0^2 d0 B V. For sf=sg, the leading degree119 terms cancel. The
remaining quadratic terms are lower than the linear terms below. In detail,
the leading-square cancellation uses

    d I^2 G-Q D c^2=Q(I^2-c^2)-I^2G;

the rest of Z has degree at most17, so its cross term has degree at most92;
the separate term H^2b^2 has degree88. The four matched factors have

    sa=-1, sg=+1: degree107, leader 4H0^2 d0 B ell0;
    sa=-1, sg=-1: degree107, leader 4H0^2 d0 B ell0;
    sa=+1, sg=-1: degree101, leader H0^2 d0 B c0;
    sa=+1, sg=+1: degree97, leader H0^2 d0 B [2t-k0-iT c0/E0].

The last bracket is nonzero because t is independent. Thus the unabsorbed
lean norm has exact degree 4*119+2*107+101+97=888 and leading form

    2^12 H0^16 d0^8 B^8 V^4 ell0^2 c0
       [2t-k0-iT c0/E0].                        (8)

For the eleven-positive form there is the exact polynomial identity

    N=Y^16 Nlean(t+(k-R-1)/Y),  s_old=s+3q.     (9)

Each of the eight factors is scaled by Y^2. The rational t shift has
degree0, below t's degree1; the carrier degree is at most16, so denominators
clear in (9), and no highest-degree term changes. The affine s substitution
has invertible linear highest part s+3beta J, so nonvanishing is preserved.
Multiplication by Y^16 adds64 degrees. Hence deg N=952. Multiplication by
Nt adds its nonzero degree2 leader w(q0-F-alpha)-zq0, so deg P=954.
These degrees hold for every authentic beta>0, not only a sampled tuple.

## 7a. Explicit twelve-positive companion

For positive J,F,alpha,z,h,i,T,s,w,eta,zeta,t, use Y=sq^3 without the s shift.
Retain the same definitions of the core registers and add Nk=k-hE-R.
Use S=H, L=1+HIT, W=b0+H(t+b+ell), and the identical norm evaluator.
The equation is Nk Nt(1+N)-1=0, or the three-equation system
Nk=1,Nt=1,N=0. Its inert circuit is positive12_none_lean_product.json.

The mod4 norm guard gives N=0 and Nk=Nt=epsilon for a common unit sign.
The authentic weak interface from package44, including its Cw=0 boundary,
supplies q>=16, 3q<R<q^4-2<E and k=R+epsilon+hE>E. Hence all bounds
(1)-(4) hold, even without the s shift, since Y>=q^3>=4096. Negative-g
exclusion is easier: the previous expression has t instead of t+u/Y.
The rational reconstruction and saturation give integral g,tau',f',y,x;
reducing the unscaled carrier modulo H gives integral gamma, positive since
c>X. The explicit ordinary signed bridge just given recovers epsilon=1
and extracts the compiler. Its common-unit proof is pinned in the preserved
ORDINARY_BLANK_PROOF.md, Sections 3-7, and is also invoked in package44.

For canonical completeness set t=gamma+ITg+tau+y-b-ell. The same inequality
now reads t>=gamma+T(Ig-cf)+(tau-ell)>0. Thus this companion has the same
existence condition. Formula (8) proves its norm degree888; Nk,Nt add7+2,
giving exact product degree897. It takes108 operations, or103 for the
three-equation system and102 after the valid positive transport shift.
It strictly improves package44's degree901/112-operation full carrier.

For reference the same construction using the predecessor full carrier
K=IT+1,delta=(a+2)c-ell has norm degree956 and product958; the short
carrier delta=ac-ell has degrees960,962. Absorbing modulo E instead of Y
adds another32 degrees. All are dominated by the recommended lean form
on degree and operation count. The builder supports their comparison formulas,
but their dominated circuits are omitted from the recommended release.

## 8. Independent diagnostics and provenance

build_absorbed.py is newly authored. check_absorbed.py independently multiplies
formal radicals in an eight-dimensional algebra, evaluates full univariate
polynomial arrays over three finite fields with the actual bound coefficient
tuple, checks all four raw and compressed payload hashes, audits gate ordering
and counts, tests the mod4 guard, and stresses the new no-h bounds with k=2
and arbitrarily larger X. These are corroborating finite diagnostics, not
proofs of the unbounded compiler theorem or formal ZFC kernel certificates.

Immutable upstream dependency pin: 124c07c0b77a9e20e84676514d8b1ff78536ea3f,
repository VladimirReshetnikov/ProveIt, directory
Computability/DiophantineConsistency/con-zfc-diophantine-forms.

- 38-batching11/eleven/ELEVEN_POSITIVE_PROOF.md, blob
  b3d8477a33943970074fb8b942ae78e7789ec71d: rational saturation, signed
  index recovery, positivity of the s shift, and inherited compiler boundary.
- 44-b4-sparse/positive/PROOF.md, blob
  4d1ccabdfa3f1fa794061967a5f1e2d5792f6913: inner-separator removal,
  modulus-Q exceptional-root exclusion, universal scalar norm, and root identity.
- 38-batching11/eleven/OPTIONAL_TRANSLATION_PROOF.md, blob
  27904b026c1662c0f33b0083bd43f922718bedb9: degree1140 comparison.
- 35-cancel12/sources/catalogue/25-hybrid12/upstream/ORDINARY_BLANK_PROOF.md,
  blob eb747622af368f7349fe30b598fb847b2491b2ac: explicit ordinary signed
  domain and extraction (Sections 2,5-7), common-unit signs (Sections3-5),
  canonical Y>2^R and X=2^R (Section6), and normalized-to-ordinary coordinate
  map (Section7). This whole file is preserved verbatim, including its own
  historical source pin and formalization limitations.

The three texts are preserved as inert upstream mathematical references.
No upstream program has been imported or executed.
