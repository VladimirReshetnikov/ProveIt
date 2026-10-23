# Translating an already quantified carrier

## Results

All six new circuits use twelve strictly positive integer unknowns and the same four **fixed**, coherently bound compiler coefficients. The single-equation degree/operation pairs are

| Carrier correction | Degree | Binary operations | System degree | System operations |
|---|---:|---:|---:|---:|
| no correction | 1081 | 110 | 1072 | 106 |
| b | **1041** | **111** | 1032 | 107 |
| b+M(ac−ell) | 1033 | 114 | 1024 | 110 |
| b+M((a+2)c−ell) | 1025 | 116 | 1016 | 112 |
| even-M, half-corrected | 1023 | 119 | 1014 | 115 |
| half-corrected plus auxiliary approximation | **1022** | **124** | 1013 | 120 |

All system entries have three equations. All operation counts charge every binary addition, subtraction and multiplication, including by a numeral, while sharing intermediate expressions. All degrees are exact, not merely syntactic bounds. The first row is the previous package30 polynomial with a cheaper evaluator. The other rows are different polynomials whose zero sets are equisolvable, not claimed identical.

The principal recommendation is the 111-operation degree-1041 form: it preserves the operation count of package30's degree-1081 form and improves package24's degree-1069 form at 123 operations. The other rows describe genuine further degree/cost tradeoffs, not a global minimum. Twelve is not a minimum number of variables: the separate Jones nine-variable reductions have much larger degrees.

## 1. Fixed compiler interface

Use one complete tuple (beta,K0,MC,MF) satisfying the normalized blank-K215 interface. In particular MF is the shifted high mask. No mixing of ports from different tuples is permitted. The release's binding supplies the selected four fixed integers and their finite recipe. The mathematical theorem below is uniform in any complete tuple satisfying that interface, including package30's materialized Wang943 tuple.

The supplied variables are

    J,F,alpha,z,h,i,T,s,w,eta,zeta,t > 0.

Retain the following definitions from package30:

    q=beta J+1, C=q−F−alpha, X=wq, Y=sq³, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
    Delta=a²+H=(a+2)²−1,
    ell=EkY, A=1+ell(ell+k), G=1+Delta c², b0=X+ac,
    R=((q−1)(q−F)+alpha)(q²−1)+(MC+q MF)J,
    Nk=k−hE−R, Nt=(K0+w)C+q−F−z(q−1),
    I=ic², D=1+Delta I², Q=Delta(D−1)=(Delta I)²,
    d=Q−1, v=cT, b=c+RD,
    P=QDv², U=Qb², e=P+U−1, Baux=2Qvb,
    M0=k(I²+T²).

Every symbol other than the twelve supplied variables and four fixed ports is a polynomial abbreviation, not an additional quantified unknown.

For the first four rows put M=M0. For the last two put M=2M0. In every case let

    L=HM+1, W=b0+H(t+sigma).

The corrections are respectively

    sigma=0;
    sigma=b;
    sigma=b+M(ac−ell);
    sigma=b+M((a+2)c−ell);
    sigma=b+M0[2((a+2)c−ell)−k];
    sigma=b+M0[2((a+2)c−ell)−k]+v(a+2)I.

The fifth and sixth corrections can be written b+M delta, with

    delta=(a+2)c−ell−k/2,

but their displayed polynomial definitions contain no division: M=2M0 cancels the denominator. There are no variable exponents or rational coefficients.

## 2. Complete scalar polynomial

Define computed expressions

    n=(HM)² A, dn=d n,
    HP=H²P, HU=H²U, He=HP+HU−H²,
    j=4 HP HU,
    Tr=2d(W²+L²G), Kr=d(W²−L²G), Kn=Kr²,
    AA=2(dn+He), cc=(dn−He)²−j,
    at=Tr−AA, bt=cc−Kn, co=16 dn j,
    vr=at(at Tr+2bt)−co,
    ur=bt²−at² Kn,
    N=ur²+Tr ur vr+Kn vr².

The promised polynomial and system are

    Nk Nt(1+N)−1=0,

or

    Nk=1, Nt=1, N=0.

This is a literal integer polynomial specified by a finite straight-line circuit. The JSON files enumerate all gates and all supplied variables. Squaring Kr rather than multiplying d² by (W²−L²G)² saves one binary multiplication in every variant. This is an exact ring identity.

## 3. Why the scalar expression is the norm

For a formal argument x put

    Cx=d(x²+M²A)−e,
    F(x)=(Cx²+D Baux²−4d²x²M²A)²−4 Cx² D Baux².

Then

    N = H^16 F((W−L sqrt(G))/H) F((W+L sqrt(G))/H).

The right side is a polynomial. More explicitly N is the product of the eight factors

    d(W−HM tau−L g)² − H²e + H² Baux f,

where independently tau=±sqrt(A), g=±sqrt(G), f=±sqrt(D). Formal signs here are a polynomial device and do not assert independent Galois automorphisms.

To verify the scalar formula without field assumptions, use

    (C²+j−K)²−4jC²=(C²−K−j)²−4Kj.

After eliminating tau and f, the remaining polynomial in z has the shape

    [(d z²)²−AA(d z²)+cc]²−co(d z²).

For z=W±L sqrt(G), the two quantities x=d z² have sum Tr and product Kn. Reduction modulo x²−Tr x+Kn gives ur+vr x. Its norm is ur²+Tr ur vr+Kn vr². This proof works when any radicals specialize to zero, squares, or coincident quadratic fields.

## 4. Uniform soundness under positive carrier corrections

The inherited package30 proof, included as upstream/INHERITED_POSITIVE12_PROOF.md, establishes the following facts from Nk=Nt=epsilon, epsilon in {1,−1}, before recovering eliminated roots:

    q≥16, X≥q, Y≥q³, E=XY,
    3q<R<q⁴−2, k=R+epsilon+hE>E,
    kY<c<2kY,
    sqrt(G)−sqrt(A)>kY²,
    2(v sqrt(D)+b)<M0 kY²< M0 sqrt(A).

These are consequences of the entire authentic compiler tuple and transport interface, not assertions for arbitrary ports. They imply for any M≥M0 that every complex root x of F satisfies

    |x|<M sqrt(G),

and that F(0) is nonzero. The package30 rational-recovery proof also needs

    d M² A>2Q(Dv²+b²),

which follows from these same inequalities and is preserved by replacing M0 with 2M0.

The new carrier leaves every one of these bounds unchanged. Its correction sigma is positive whenever nonzero. Indeed b>0. Also

    ac−ell = kY²+a eta >0,
    (a+2)c−ell >0,
    (a+2)c−ell−k/2 > k(Y²−1/2)>0.

Thus W>0 in every variant.

The identity Tr=2x0 and Kn=x0²−4d²W²L²G, with x0=d(W²+L²G), shows

    N ≡ (ur+x0 vr)² (mod 4).

At a solution of the product equation, 1+N cannot equal −1. The three integer factors are units, so N=0 and Nk=Nt=epsilon with a common unit sign. The three-equation system directly gives epsilon=1.

Choose a vanishing factor F((W−Lg)/H). If G is nonsquare, its two actual quadratic conjugates would provide two roots of F with distance 2L sqrt(G)/H, exceeding the common bound 2M sqrt(G) since L=HM+1. Thus g is integral and x=(W−Lg)/H is rational. Since W>0 and |x|<M sqrt(G), the selected g must be positive.

The inherited explicit rational-recovery formulas recover rational f and tau with f²=D and tau²=A; both are integers. The rational auxiliary root y=x−M tau obeys

    Q(vf−b)²−(Q−1)y²=1.

Because Q is an integer square, the rational Pell saturation lemma makes y integral. Hence x is integral. The congruence W≡b0 (mod H), unchanged by every new correction, gives g≡b0 (mod H), so gamma=(g−b0)/H is integral. It is positive because g>(a+1)c and c>X. The original normalized blank-machine interface, including its signed quotient extension, now recovers the accepting K215 computation and epsilon=1 exactly as before.

All denominators and zero cases in this recovery are covered by the inherited proof: Cx>0 for real x, Baux>0, d>0, M>0, and F(0)≠0. No new rationality assumption or sign change of an affine main-root expression is introduced.

## 5. Constructive completeness and positivity of the translated variable

Take a canonical positive normalized blank-compiler witness, including positive g,tau,y,gamma. Package30 uses

    t_old=gamma+Mg+M tau+y.

Set t=t_old−sigma. This is an integer. Its defining identity gives W=Lg+H(M tau+y), so N=0 and Nk=Nt=1. It remains essential to prove t>0, rather than assuming a translation preserves the positive domain.

For sigma=b, M tau>b follows from the bound above, and t>0.

For sigma=b+M delta with delta=ac−ell or delta=(a+2)c−ell or its half-corrected counterpart, one has delta<g. Indeed ell/c>E/2>2, hence (a+2)c−ell<ac<g; the other deltas are smaller. Therefore

    t=gamma+M(g−delta)+M tau+y−b>0.

For the final auxiliary correction, use M=2M0 and

    (a+2)I<2 sqrt(D).

The latter follows from D=1+((a+2)²−1)I² and a+2≥2. Consequently

    M tau >4(v sqrt(D)+b)>v(a+2)I+b.

The same displayed formula for t, with the additional subtraction v(a+2)I, is still strictly positive. This proves completeness without enlarging a Pell index, imposing divisibility, or changing the canonical coefficient calibration.

Thus all six constructions are equisolvable with blank halting of K215. Composing with the inherited proof calibration and negating yields, in ZFC, that their absence of solutions in the stated positive domain is equivalent to Con(ZFC). This is a mathematical equivalence proof, not a consistency proof or a new Lean/Rocq certificate.

## 6. Exact degrees by the eight factors

All four fixed coefficients have degree zero. Scale every supplied variable by a formal parameter Z and work in the Laurent-series field over the rational function field of those variables and fixed coefficients. The three positive-leading formal square roots exist because their leading forms are squares. This is only a device for reading the polynomial's homogeneous leading terms; no assumption about numerical square roots is made.

The common degrees are

    deg(E,H)=6, deg(Y)=4, deg(k)=1, deg(c)=5,
    deg(ell)=11, deg(A,G)=22, deg(I)=11, deg(D)=34,
    deg(Q,d)=46, deg(b)=38, deg(M0,M)=23.

Write a bar over a symbol for its leading homogeneous form. Then

    Hbar=4Ebar, cbar=kbar Ybar, ellbar=Ebar kbar Ybar,
    M0bar=kbar Ibar², bbar=Rbar Dbar,
    sqrt(D) has degree17 and leading form Ebar Ibar.

The positive-leading expansions satisfy

    sqrt(G)−sqrt(A) = (ac−ell) + a term of degree5,
    sqrt(G)−sqrt(A)−(ac−ell) has leading form 2cbar,
    sqrt(G)−sqrt(A)−((a+2)c−ell) has degree1 and leading form −kbar/2,
    ((a+2)c−ell−k/2)−(sqrt(G)−sqrt(A))
        has degree−1 and leading form cbar/(2Ebar).

The first difference sqrt(G)−sqrt(A) has degree9 and leading form kbar Ybar². These follow by expanding

    sqrt(G)=sqrt((a+2)² c²−c²+1),
    sqrt(A)=sqrt((ell+k/2)²+1−k²/4).

For example sqrt(G)=(a+2)c−c/[2(a+2)]+lower-degree terms, while sqrt(A)=ell+k/2+terms of degree at most−9. There is no vanishing leading coefficient for authentic beta>0.

For the b-based variants write

    Zsg,sa = W−Hb−HM sa sqrt(A)−L sg sqrt(G).

The corresponding factor becomes

    2dHb Zsg,sa + d Zsg,sa² − H²b² − H²QDv²
       + H² + sf H²Baux sqrt(D).

Here the last radical term has degree119. The four (sa,sg) pairs give these degree lists, each repeated for the two f signs except in the last row:

| Correction | Degrees of Zsg,sa | Degrees of the eight factors | Sum |
|---|---|---|---:|
| b | 40,40,38,38 | 130,130,130,130,128,128,128,128 |1032|
| b+M(ac−ell) |40,40,38,34|130,130,130,130,128,128,124,124|1024|
| b+M((a+2)c−ell) |40,40,38,30|130,130,130,130,128,128,120,120|1016|
| half-corrected |40,40,38,28|130,130,130,130,128,128,119,119|1014|
| half-corrected plus auxiliary |40,40,38,29|130,130,130,130,128,128,119,118|1013|

In the first three rows each leading factor is 2 dbar Hbar bbar times its nonzero Z-leading form. In the half-corrected row the two special leading terms are the opposite nonzero f terms of degree119.

For the last row the special branch is (sa,sg)=(−1,+1). Put f0=(a+2)I and delta=(a+2)c−ell−k/2. There

    Zsg,sa=H v f0 + H M(delta+sqrt(A)−sqrt(G)) + b0+Ht−sqrt(G).

Its degree29 leading term is Hbar vbar fbar. At one f sign the two degree119 contributions add; at the other they cancel. The next surviving degree118 term is

    2 dbar Hbar² bbar Mbar cbar/(2Ebar),

which is nonzero. To check that no omitted term has degree118 or greater: f0−sqrt(D) has degree5, so the correction from replacing f0 by sqrt(D) contributes degree107; b0+Ht−sqrt(G) has degree at most7; and all remaining square terms have degree at most104. Thus the final factor has exactly degree118.

The product degree is the sum of the eight nonzero factor degrees in this Laurent field, and the product is the integer polynomial N. This proves all five exact norm degrees. For the unshifted baseline, the inherited proof gives N_top=Hbar^16 Ubar^8≠0 and degree1072. Finally Nk and Nt have exact degrees7 and2 with nonzero leading forms, so the product polynomial has degree deg(N)+9. Every claim holds for the actual fixed tuple, not merely for generic coefficient values.

## 7. Verification and scope

The new emitter contains no received executable imports. Its accompanying checker independently multiplies the eight radical factors using an eight-dimensional formal algebra; it checks positive, negative, zero, and degenerate inputs modulo several primes. Additional tests check the unit congruence, all gates and ports live, the factorization underlying the cheaper Kn evaluation, the exact degree claims by full finite-field univariate polynomial arithmetic, and synthetic radical-kernel witnesses. These finite diagnostics support the displayed identities but do not replace the mathematical proofs or verify the inherited compiler by finite testing.

Sources are pinned at commit 8c6eec9d19ef80538c8e61ff6e0180040583446a. Package24 motivates deliberate leading-term cancellation; package30 supplies the scalar trace norm and the separating bound. The new idea is translating the already quantified carrier by increasingly accurate polynomial approximations to the auxiliary and radical expressions while proving that the translated positive variable remains positive.

