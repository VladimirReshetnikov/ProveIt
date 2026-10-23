# A free Pell ordinate and an adaptive quotient modulus

## Result and scope

The fixed polynomial below has fourteen strictly positive integer unknowns,
exact total degree 30, and an 83-operation division-free evaluator. Its
positive solvability is equivalent, by the stated ordinary mathematical
reductions and inherited compiler/Pell theorems, to a finite syntactic ZFC
refutation. Negating gives the equivalence, provable in ZFC, of its
unsolvability and Con(ZFC). No consistency assumption, solution search,
global-minimality claim, or new end-to-end Lean/Rocq certificate is involved.

Compared with the fourteen-positive degree-52/79-operation equation in
package 55, degree drops by 42.3077% for four additional gates. Package 58
has a fifteen-positive degree-30/79-operation equation: the new point uses
one fewer positive unknown and four more operations at that same degree.
The fifteen-positive 66-operation equation remains a different tradeoff.

The new ingredient is to combine the integral-root scale carrier with an
adaptive index-quotient modulus U=Y^2. Its adequacy follows from an early
gcd bound and the first Pell congruence, before the missing index quotient
or the principal Pell index has been recovered. Earlier ingredients are
credited explicitly below.

## 1. Complete polynomial definition

The fourteen supplied coordinates, all strictly positive integers, are

    J,F,alpha,z,f,i,T,Y,w,rho,eta,zeta,e,gamma.

The fixed leaves beta,K0,MC,MF are the WHOLE package-44 compact native
tuple in native/COEFFICIENT_BINDING.json. Thus beta=2^590069-1,
K0 is its K port, and MF is its already shifted MF_source port. All four
compressed integers, their exact hashes, the literal 430 transitions,
943 Wang tiles, coefficient generator and proof are included under native/.

Define polynomial abbreviations (not extra quantified witnesses):

    q=beta J+1, q2=q^2, q3=q^3, C=q-F-alpha,
    X=wq, E=XY, k=eta+zeta, c=kY+eta,
    a=E+Y, H=4a+3, Delta=a^2+H=(a+2)^2-1,
    ell=EkY, b0=X+ac, G=1+Delta c^2,
    R=[(q-1)(q-F)+alpha](q^2-1)+(MC+q MF)J,
    r=k-R-1, U=Y^2,
    Dstar=U b0+H(U gamma-r), M=Dstar^2-U^2 G,
    I=i c^2, Aaux=Delta(f^2-1), W=I^2-Aaux,
    V=f^2(cT-R)-c, y=V+e,
    Na=Aaux(V^2-y^2)+y^2,
    Lt=(K0+w)C-F-z(q-1),
    A0=[q^3(ell+rho)+Y]^2-q^6[ell(ell+k)+1].

The equation is

    P=A0^2+M^2+W^2+Na^2+Lt^2-1=0.                (1)

Every exponent is fixed. The polynomial contains no division, roots,
bit operations, recurrence evaluation, or hidden existential registers.
polynomial.json is the literal 83-gate arithmetic circuit; build.py
reconstructs it. An integer equation without positivity restrictions
would require an explicit domain translation and is not asserted here.

## 2. The local norm minimum

For every positive tuple, a>0, Delta>0 and c>=3, so I>=9. If f=1,
Aaux=0 and W=I^2>1. Thus W^2+Na^2>1. If f>=2, Aaux>1. In this case
Na cannot vanish. Indeed Na=0 would imply

    Aaux V^2=(Aaux-1)(V+e)^2.

Neither V nor V+e can vanish (otherwise both would, contradicting e>0).
The displayed equality would make Aaux(Aaux-1) a rational square.
A rational square root of an integer is integral, whereas

    (Aaux-1)^2 < Aaux(Aaux-1) < Aaux^2.

This contradiction proves Na^2>=1. Equation (1) therefore forces

    A0=M=W=Lt=0, Na=+1 or -1.

With W=0, Aaux=I^2 and Na=I^2 V^2-(I^2-1)y^2. Modulo four this is
the square V^2 or y^2 according as I is odd or even. Consequently Na=-1
is impossible. Conversely these five equalities imply (1). We have proved
the exact tuplewise equivalence

    P=0 iff A0=M=W=Lt=0 and Na=1.               (2)

This uses only elementary integer algebra, not a compiler assumption.

## 3. Recover Y's scale and the source bounds first

From A0=0, the rational number [q^3(ell+rho)+Y]/q^3 has square
ell(ell+k)+1, an integer. It is therefore an integer. Hence q^3 divides Y,
and

    s=Y/q^3>0, tau=ell+rho+s>0,
    tau^2-ell(ell+k)=1.                         (3)

No bound on a missing index has been used. In particular Y>=q^3 and
X=wq>=q. The authentic beta gives q>=16.

Let z_old=z+1. The identity

    (K0+w)C+(q-F)-z_old(q-1)=1+Lt

restores the unshifted transport equation with value +1. It gives C>0:
if C<=0, its left side is at most
q-F-z_old(q-1)=1-F-(z_old-1)(q-1)<=0. Thus
1<=F<=q-1 and alpha+C=q-F. The authentic four ports satisfy
0<MC<B-1 and B-1<MF<2(B-1), where B=beta+1. Since
J=(q-1)/(B-1), the inherited elementary packing estimate gives

    3q+1<R<q^4-2, E>=q^4>R+2, a>E>R,
    k>=2, kY<c<k(Y+1).                         (4)

For explicit verification, the gap G0=(q-1)(q-F)+alpha is
q alpha+(q-1)C, between q and q^2-q. The mask term is strictly
between zero and (q-1)(1+2q). These imply the slightly weaker familiar
R<q^4-q^3+q^2-1<q^4-2, sufficient here. Positive C actually gives
G0<=q^2-q-1 and the stronger R<q^4-q^3. Either bound proves (4).

## 4. The new adaptive-modulus lemma

After (3), set U=Y^2 and mu=U/gcd(U,H). Since

    H=4Y(X+1)+3,

we have gcd(Y,H)|3. For each prime p,

    min(2 v_p(Y),v_p(H))<=2 min(v_p(Y),v_p(H)).

Thus gcd(Y^2,H) divides 9, and in particular is at most 9. Consequently

    mu>=Y^2/9>=q^6/9>q^4>R+2.                  (5)

The strict inequality uses q>=16. Moreover

    U divides 4XY^2                            (6)

identically; it does not require X to be a decoded power of two. These
are exactly the two properties required by the quotient-absorption proof.
No conclusion about the missing h or about the main index is being used
to establish them.

This is the crucial improvement over U=4q^4. When Y is supplied directly,
U=Y^2 has polynomial degree two, while its arithmetic size still exceeds
the required q^4 threshold after scale recovery. The old scaled variable
Y=sq^3 obscured this distinction between arithmetic size and degree.

## 5. Positive principal root and an early index bound

The equation M=0 makes g=Dstar/U a rational square root of G. Hence g is
an integer. It is positive before the index is identified. Indeed r<k,
U=Y^2, a>3, and H<5a, so

    Dstar/U=b0+H(gamma-r/U)>b0-Hk/U,
    b0/H>ac/H>c/5>kY/5>k/Y^2=k/U.

The last inequality follows from Y>=q^3>=4096. Thus g>0 and

    g^2-Delta c^2=1, U divides H(k-R-1).        (7)

Pell classification of (3) and (7) supplies n,p>=1 with

    P0=2XY^2+1, A=a+2,
    tau=chi_P0(n), k=2 psi_P0(n),
    g=chi_A(p), c=psi_A(p).

Here chi and psi are the usual integer-coordinate Pell sequences.
Since P0>A and c>k, monotonicity gives p>n. The elementary recurrence
congruence gives

    k=2n modulo 4XY^2.

Combining (6) and (7) yields 2n=R+1 modulo mu. Since 0<R+1<mu,
positivity of n implies

    2n=R+1+t mu for an integer t>=0,
    n>=(R+1)/2>=25, p>=26.                    (8)

This is an early lower bound; it does not assume the deleted equation
k-hE-R=1. Standard Pell growth now gives

    c>A Delta^2, c>2p, c>2R.                  (9)

For example psi_A(p)>=(2A-1)^(p-1)>=A^25>A(A^2-1)^2 proves the
first bound. The recurrence gives c>2p; and c>=psi_A(2)=2A>2R by (4).

## 6. Restore the ordinary strong kernel in the correct order

The equality W=0 is (ic^2)^2=Delta(f^2-1). Together with (9), the
inherited ordinary strong-rank lemma (upstream/ORDINARY_KERNEL.md,
section 4, also reproduced in upstream/FOURTEEN_PROOF.md) yields

    f=chi_A(m), p|m, c|m, m>=c>2p,
    I=Delta psi_A(m), c^2|(f^2-1).             (10)

This rank lemma is a named inherited mathematical theorem. It handles
possible nonfundamentality of A; merely cancelling Delta in W=0 would
not establish it. Its strict large-c hypothesis has been proved in (9).

Put T_old=fT and y_old=|V+e|. Then T_old>0 and

    V=c(T_old f-1)-R f^2,
    I^2 V^2-(I^2-1)y_old^2=1.

The ordinate y_old is nonzero: otherwise I^2 V^2=1, impossible for I>=9.
The signed auxiliary-index lemma from upstream/ORDINARY_KERNEL.md,
section 5, now applies using (9)-(10). For clarity its two congruences are
V=-c modulo f and V=-R modulo c. The odd auxiliary Pell index is congruent
to +/-p modulo m and to +/-R modulo c. Since c|m and 0<p,R<c/2, it follows
that p=R. The same lemma is detailed in upstream/FOURTEEN_PROOF.md,
section 4. No h or main gamma congruence is used by this step.

We now know n<p=R. Thus |2n-R-1|<R<mu. Its divisibility by mu forces

    2n=R+1.

The first Pell congruence therefore shows that r=k-R-1=k-2n is a
positive multiple of 4XY^2. In particular it is divisible by E and by
the FULL U, not just by mu. Consequently

    h=r/E>0, gamma_old=gamma-r/U

are integers. Equation (7) gives g=b0+H gamma_old. Since n>=2,
k>=4P0>X, so c>X; also g>(a+1)c. Therefore
g-b0>c-X>0 and gamma_old>0.

All fifteen coordinates of the inherited ordinary-strong positive kernel
are restored, with z_old=z+1, s=Y/q^3, tau from (3), T_old=fT,
y_old=|V+e| and the recovered h,gamma_old. Its six source factors equal
one. The ordinary native compiler with the whole compact tuple and the
K215/refutation calibration give a finite ZFC refutation.

## 7. Constructive completeness

A finite ZFC refutation supplies canonical normalized compiler witnesses.
Use the authentic compact tuple's ordinary interface, converting its
normalized strong coordinate by i=Delta i_normalized. The canonical
identities include p=R=2n-1, R=3 modulo four, X=wq=2^R, Y=sq^3,
and c=psi_A(R). Thus r=k-R-1 is a positive multiple of 4XY^2, hence U.
Set gamma=gamma_old+r/U>0; then Dstar=Ug and M=0.

The root carrier also preserves canonical positivity. Since ell>k,

    tau<ell+k,
    tau-ell=(ell k+1)/(tau+ell)>k/3.

Canonical n>=2 gives k>XY. Therefore k/3>XY/3>Y/q^3=s, and
rho=tau-ell-s is a positive integer. Keeping the directly supplied
Y=sq^3 gives A0=0.

The transport shift retains a positive coordinate. As X=2^R, R>3q and
q>=16, w=2^R/q>q>F. Since C>0,
(K0+w)C-F>0. The old transport identity reads

    (z_old-1)(q-1)=(K0+w)C-F,

so z_old>=2 and z=z_old-1>0, giving Lt=0.

For completeness of the auxiliary substitution, let I=Delta i_normalized c^2.
The canonical normalized strong equation gives I^2=Delta(f^2-1).
Set

    V=chi_I(R)/I, y_old=psi_I(R).

For odd R=2r0+1, the integer polynomial Q_r0 satisfies

    chi_t(2r0+1)=t Q_r0(t^2),
    Q_r0(0)=(-1)^r0(2r0+1),
    Q_r0(1-A^2)=(-1)^r0 psi_A(2r0+1).

Since R=3 modulo four, r0 is odd. Reduction modulo f^2 and c gives
V=-c modulo f^2 and V=-R modulo c. The canonical normalized equation
also gives gcd(c,f)=1 and f^2=1 modulo c. Hence

    T=(V+c+R f^2)/(c f^2)

is a positive integer and V=f^2(cT-R)-c. This is the inherited
squared-modulus lemma, with its polynomial proof retained in
upstream/SQUARED_MODULUS_PROOF.md. No arbitrary old quotient is assumed
to be divisible by f; new auxiliary witnesses are chosen explicitly.
The Pell identity gives Na=1. Since R>=3 and I>1,
V>=4I^2-3>1 and

    (I^2-1)(y_old^2-V^2)=V^2-1>0.

Thus e=y_old-V>0. Finally W=0 by construction. All fourteen supplied
coordinates are positive and (2) gives P=0.

Soundness and completeness establish positive existence equivalence.
Their arithmetic and induction arguments, composed with the identified
compiler and calibration theorems, are formalizable in ZFC. Negation
gives the asserted unsolvability/Con(ZFC) equivalence.

## 8. Exact degree and operation count

Every supplied witness has degree one and fixed numerals have degree zero.
Put

    q0=beta J, X0=w q0, k0=eta+zeta,
    E0=X0Y, c0=k0Y, R0=q0^3(q0-F).

The residual degrees are A0:12, M:14, W:10, Na:15, Lt:2. The relevant
cancellations are exact polynomial identities:

    A0=q^6[2ell rho+rho^2-ell k-1]
           +2q^3Y(ell+rho)+Y^2,
    D0=b0+H gamma,
    D0^2-G=2ac(X+H gamma)+(X+H gamma)^2-Hc^2-1,
    M=U^2(D0^2-G)-2UH rD0+H^2r^2,
    Na=V^2-(Aaux-1)e(2V+e).

For M, the first summand has degree at most 13; the other two have degree
14 and the nonzero joint leading form

    8 X0^2 Y^2 R0(k0Y^3+2R0).

For Na, V has leader -f^2R0, and Aaux has leader E0^2f^2. Thus

    Na_lead=2 E0^2 f^4 e R0,
    P_lead=4 beta^10 J^10 w^4Y^4 f^8e^2(beta J-F)^2.   (11)

Only Na^2 reaches degree 30. In particular the coefficient of
J^12 w^4Y^4 f^8e^2 is 4 beta^12, and the coefficient of
J^10 F^2 w^4Y^4 f^8e^2 is 4 beta^10; both are nonzero. This proves
degree 30 with the actual fixed tuple, rather than a syntactic degree bound.

The literal evaluator has 44 multiplications, 23 additions and
16 subtractions: 83 operations. Multiplication by a numeral, squaring,
and every other binary operation are charged. Reuse and fixed leaves are
free, so this is arithmetic-circuit complexity, not bit complexity or
expanded coefficient height. All fourteen witness ports, all four fixed
ports and all 83 gates are live.

## 9. Provenance and reproducibility boundary

The comparison is pinned to ProveIt commit
beb0192cb8dc36f78c369c080f2adfbc1887a486. SOURCE_PINS.json records exact
upstream paths, commits, Git blob hashes and byte hashes. Some compact
coefficient input files are pinned to their earlier source commit, as
recorded in native/SOURCE_PINS.json; the current file identities are
authenticated too. Copied notices and license terms remain in native/.

The inherited components are the compact native coefficient compiler (44),
ordinary strong-rank and signed auxiliary-index theorem (36's preserved
ordinary proof), index quotient absorption (50), auxiliary-gap minimum
with squared modulus (55, 51), integral-root scale carrier and positive
first-gap bound (58), and the justified positive transport shift. The
new choice U=Y^2 and its proof are not quoted from these packages.

verify.py checks circuit wiring/counts/liveness, authenticated source bytes,
actual coefficient payloads, independent scalar transcriptions, exact
univariate polynomial rays through the entire circuit, and finite tests of
the arithmetic gcd/scale lemmas. Those finite checks certify implementation
properties and explicit finite cases; the universal semantic equivalence
rests on sections 2-7 and the named inherited mathematical theorems.
No finite test decides whether a ZFC refutation or a positive zero exists.
