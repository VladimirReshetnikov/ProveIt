# A degree-ten separating weight for the twelve-positive-variable equation

## Result

The mathematical construction is uniform in one complete four-port normalized blank-K215 compiler tuple. The delivered circuits are bound by COEFFICIENT_BINDING.json to the complete package31 wang943-mixed-121x8801 tuple, sharing the four materialized payloads with the Sun construction. The ports are fixed integers beta,K0,MC,MF, with MF the shifted high mask. They must be rebound together, never individually. The equation is a literal integer polynomial; all named intermediates below are computed registers, not additional variables.

There are twelve positive supplied unknowns J,F,alpha,z,h,i,T,s,w,eta,zeta,t. New system/equation operation and exact-degree pairs are:

| Carrier correction sigma | System ops / degree | Single equation ops / degree |
|---|---:|---:|
| b | 107 / 952 | 112 / 961 |
| b+v f0 | 111 / 940 | 116 / 949 |
| b+v f0+M(ac-ell) | 114 / 936 | 119 / 945 |
| b+v f0+M((a+2)c-ell) | 116 / 932 | 121 / 941 |

Each system has three equations. The fourth row dominates the preceding lowest-degree twelve-positive scalar form, degree1022 at124 operations, on both degree and operation count. The first row is a lower-cost alternative. These are not global optimality or variable-count claims.

The genuinely new step is to replace the old weight k(I^2+T^2), degree23, by u(u+T), u=k^4 i, degree10. This exploits inequalities between already constrained variables, rather than a syntactic bound valid at arbitrary points. The final carrier correction also combines the old main-root approximation with a positive approximation of the auxiliary root.

## Definition

Retain the exact common interface:

q=beta J+1, C=q-F-alpha, X=wq, Y=sq^3, E=XY,
k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
Delta=a^2+H=(a+2)^2-1,
ell=EkY, A=1+ell(ell+k), G=1+Delta c^2, b0=X+ac,
R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
Nk=k-hE-R, Nt=(K0+w)C+q-F-z(q-1),
I=ic^2, S=Delta I, D=1+IS, Q=S^2, d=Q-1,
v=cT, b=c+RD, P=QDv^2, U=Qb^2, e=P+U-1, Baux=2Qvb.

The new weight and carrier are

u=k^4 i, M=u(u+T), L=HM+1, f0=(a+2)I,
W=b0+H(t+sigma).

Use any correction sigma in the table. Define

n=(HM)^2 A, dn=d n, HP=H^2P, HU=H^2U,
He=HP+HU-H^2, j=4 HP HU,
Tr=2d(W^2+L^2G), Kn=[d(W^2-L^2G)]^2,
AA=2(dn+He), cc=(dn-He)^2-j,
at=Tr-AA, bt=cc-Kn, co=16 dn j,
vr=at(at Tr+2bt)-co, ur=bt^2-at^2 Kn,
N=ur(ur+Tr vr)+Kn vr^2.

The system is Nk=Nt=1, N=0. The single equation is Nk Nt(1+N)-1=0. The new circuits also share H^2Q between HP and HU, following package31, and Horner-factor the final quadratic norm. The emitter stores the negative of the displayed ur and writes N as Kn vr^2-u(Tr vr-u). The system compares these two terms directly, saving one subtraction. Every binary arithmetic operation, including multiplication by a literal, is charged. All powers are expanded into multiplications.

## Exact norm identity and inherited interface

For x a formal variable, put Cx=d(x^2+M^2 A)-e and

F(x)=(Cx^2+D Baux^2-4d^2 x^2 M^2 A)^2-4Cx^2 D Baux^2.

The displayed scalar expression is identically

N=H^16 F((W-L sqrt(G))/H) F((W+L sqrt(G))/H).

Equivalently it is the product of eight factors

d(W-HM tau-L g)^2-H^2 e+H^2 Baux f,

where tau=±sqrt(A), g=±sqrt(G), f=±sqrt(D). This is a polynomial identity; it does not assert independent automorphisms of specialized square roots. The trace/product proof in package34/positive/SHIFTED12_PROOF.md applies verbatim, because it is an identity in formal registers and places no condition on M.

For the authentic coefficient tuple, the weak common-interface theorem permits Nk=Nt=epsilon with epsilon=±1 and gives

q>=16, X>=q, Y>=q^3, E=XY, 3q<R<q^4-2,
k=R+epsilon+hE>E,
kY<c<k(Y+1),
sqrt(G)-sqrt(A)>kY^2, sqrt(A)>kY^2.

These statements are not claimed for arbitrary four integers substituted for the compiler ports. They are precisely the inherited bootstrap from the full normalized compiler interface.

## New separating-weight lemma

Let B=kY^2. Since X>=16 and k>E=XY, we have Y<k/16. Further Y>=4096, k>65536, R<k, and

a+2=E+Y+2<9k/8,
c<k(Y+1)<17kY/16.

The strict inequality sqrt(D)<(a+2)I follows from D=(a+2)^2 I^2-I^2+1 and I>1. Thus

v sqrt(D)/B
 < (9/8)(17/16)^3 k^3 i Y T
 < (44217/524288) k^4 i T
 < uT/8.

Similarly,

b/B = c/B+RD/B
 < 1+(81/64)(17/16)^4 k^6 i^2 Y^2
 < 1+(6765201/1073741824)k^8 i^2
 < 1+u^2/128.

Here c/B<(Y+1)/Y^2<1; D<(a+2)^2i^2c^4 was used before the displayed bound. Since u^2>128,

2(v sqrt(D)+b)/B < uT/4+2+u^2/64
                         < uT/4+u^2/32 < u(u+T)=M.

Consequently

2(v sqrt(D)+b)<M kY^2
 < min(M sqrt(A), M(sqrt(G)-sqrt(A))).

This recovers both separating roles of the old M with degree10 instead of23. Importantly, no assertion M>=k(I^2+T^2) is needed or made.

## Soundness, including rational saturation

The square-mod-four argument is unchanged: put x0=d(W^2+L^2G). Then Tr=2x0, Kn=x0^2 modulo4, so N=(ur+x0 vr)^2 modulo4. At a zero of Nk Nt(1+N)-1, the three integer factors are units and N cannot be-2. Hence N=0 and Nk=Nt=epsilon=±1.

The new bound implies d M^2 A>2Q(Dv^2+b^2), because d>=Q/2. Therefore Cx>Q(Dv^2+b^2)+1>Baux sqrt(D)>0 for real x. Every complex root of F has the form x=M tau+y, where tau^2=A, f^2=D and d y^2=Q(vf-b)^2-1. Its modulus is less than M sqrt(G), and F(0) is nonzero.

If G were nonsquare, a zero of the norm would give two conjugate roots of F at distance2L sqrt(G)/H>2M sqrt(G), a contradiction. Thus the selected g is integral and x=(W-Lg)/H is rational. All listed sigma are positive. For the two main-root corrections, ac-ell=kY^2+a eta>0. Thus W>0 and g must be positive.

For rational x, the nonzero denominators in the inherited reconstruction are justified by Cx>0 and x!=0. Explicitly

f=-(Cx^2+D Baux^2-4d^2x^2M^2A)/(2Cx Baux),
tau=(Cx+Baux f)/(2d x M), y=x-M tau.

They give rational f,tau with integer squares D,A, so f,tau are integers. The auxiliary equation is S^2(vf-b)^2-(S^2-1)y^2=1. Rational Pell saturation, as proved in the inherited source, gives integral y; it is a special Pell statement, not false general nonmonic-root integrality. Therefore x is integral, and W=b0 moduloH, L=1 moduloH give g=b0 moduloH. The recovered gamma=(g-b0)/H is positive since g>(a+1)c and c>X. The inherited signed-quotient/common-unit endpoint restores epsilon=1 and extracts blank K215 halting.

No new unbounded compiler claim is hidden in the weight argument: its conclusion restores exactly the same normalized equations as package34. The final implication to negation of Con(ZFC) uses that same inherited calibrated endpoint.

## Completeness and positivity

Start with a canonical positive normalized compiler witness, with positive g,tau,y,gamma and the retained eleven coordinates. Set t_old=gamma+Mg+M tau+y and t=t_old-sigma. Then W=Lg+H(M tau+y), so a norm factor vanishes and Nk=Nt=1.

For sigma=b, M tau>2(v sqrt(D)+b)>b, so t>0. For every auxiliary-shifted variant, f0<2sqrt(D), so M tau>v f0+b. For delta=ac-ell or (a+2)c-ell, one has 0<delta<g: indeed ell/c>E/2>2, hence (a+2)c-ell<ac<g. Therefore

t=gamma+M(g-delta)+(M tau-v f0-b)+y>0.

This requires no enlargement of a Pell index, new divisibility, or alteration of another witness. The equivalence is direct. Negating it and composing with calibrated K215 gives in ZFC: absence of a positive solution iff Con(ZFC). This is not a proof of either side and is not a new Lean/Rocq certificate.

## Uniform exact degrees

Assign degree1 to all twelve supplied variables and degree0 to the four fixed ports. The inherited degrees are

deg(E,H)=6, deg(Y)=4, deg(c)=5, deg(ell)=11,
deg(A,G)=22, deg(I)=11, deg(D)=34, deg(Q,d)=46,
deg(v)=6, deg(b)=38.

The new M has degree10 and leading form k_bar^8 i^2. Formal positive-leading square roots have

sqrt(G)-sqrt(A): degree9, leading k_bar Y_bar^2;
sqrt(G)-sqrt(A)-(ac-ell): degree5, leading2c_bar;
sqrt(G)-sqrt(A)-((a+2)c-ell): degree1, leading-k_bar/2;
f0-sqrt(D): degree5, leading I_bar/(2E_bar).

These follow from the two binomial expansions in package34 and from (f0-sqrt(D))(f0+sqrt(D))=I^2-1. They are calculations in a Laurent-series field over the rational function field in the supplied variables, so they prove polynomial degree rather than assuming numerical radicals rational.

For an auxiliary-shifted variant put delta=0, ac-ell, or (a+2)c-ell, and

Z0=HM(delta-sa sqrt(A)-sg sqrt(G))+b0+Ht-sg sqrt(G).

Then W-HM sa sqrt(A)-L sg sqrt(G)=Hb+Hv f0+Z0. In an eight-factor norm term, the f-positive branch has a unique degree119 leader4 H_bar^2 Q_bar b_bar v_bar f_bar. The f-negative branch has two potentially largest terms:

2dHb Z0 + 2H^2 b v [Q(f0-sqrt(D))-f0].

The latter has degree107 with nonzero leader. All remaining terms have degree<=102 (or92 for H^2Qv^2(f0^2-D)). The four Z0 degrees are

27,27,25,25 for delta0;
27,27,25,21 for delta=ac-ell;
27,27,25,17 for delta=(a+2)c-ell.

Therefore the four f-negative degrees are respectively

117,117,115,115;
117,117,115,111;
117,117,115,107.

In the final special branch both degree107 contributions add, rather than cancel: its leader is H_bar^2 Q_bar b_bar times the sum

M_bar k_bar + v_bar I_bar/E_bar.

This is a nonzero polynomial (the displayed quotient simplifies in the Laurent coefficient field); all authentic beta>0 slices retain it. The other f-negative leaders are nonzero by the stated radical expansions. Thus exact norm degrees are940,936,932. For sigma=b without auxiliary shift, all eight factors have degree119, because the f-term strictly dominates the cross term of degree<=117; the norm degree is952. Nk,Nt add exact degrees7 and2. This proves all table entries uniformly, not just at sampled coefficients.

## Checks and provenance

The emitter is newly authored, contains no executable upstream imports, and emits inert JSON straight-line records. Separately authored finite-field evaluators compute full polynomial specializations, not tropical bounds; all degrees in the table are reproduced, both at generic test ports and at the actual four fixed port residues. The fixed-instance checker verifies all four decompressed payload hashes and performs twelve full univariate replays over two primes, including the exact recommended-form diagonal leader. These diagnostics do not replace the uniform proofs. An independent radical-product evaluator and positive-bound tests accompany the release.

Sources at pin22e75dd6b87b1b199bb08c778d7cf075ae5aae08:
- package34 positive/SHIFTED12_PROOF.md, blob570e94b70f08520f5346b1f620d7c14ffbbe24a4;
- package34 positive/upstream/INHERITED_POSITIVE12_PROOF.md, blob1257bbbe7272190f670a46aab10472430ece55f9;
- package31 positive12/build_refactored12.py, blobdec0213467cc689ce3715092f867437c417659f2, inspected as text only, for H^2Q sharing and scalar norm factorization.

A more complicated half-corrected variant is emitted as a diagnostic, but is dominated by the degree941/121-operation form and is not recommended. The unshifted degree1081 diagnostic is likewise dominated. No upstream executable was run.

### Independent leading-coefficient cross-check

On the diagonal where all twelve supplied variables equal a single indeterminate Z, the recommended ac2_aux norm has leading coefficient

-2^152 beta^544 (beta-1)^8 (beta^5+64)

at degree932. Multiplication by Nk Nt adds the nonzero leader2 beta^4, giving

-2^153 beta^548 (beta-1)^8 (beta^5+64)

at degree941. This supplies a particularly simple nonvanishing certificate for every authentic beta>2. A separate reviewer derived it from sixteen linear radical factors and independently checked full univariate specializations over four finite fields, including the actual smallest-tuple beta residue. Its check is in ../short/check_positive_weight_review.py; the argument above establishes the matching degree upper bound.
