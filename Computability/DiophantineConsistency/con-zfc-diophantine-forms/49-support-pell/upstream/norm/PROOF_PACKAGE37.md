# Smaller positive separating norms, with exact degree 1061

## Results, meaning, and fixed instance

There are twelve supplied strictly positive integers

    J,F,alpha,z,h,i,T,s,w,eta,zeta,t.

All other names are polynomial abbreviations, not existential coordinates.
Every binary addition, subtraction, and multiplication, including multiplication
by a fixed numeral, is charged. Comparisons in a system are free.

| Family | Product degree / operations | System degree / operations | Shifted system operations | SOS degree / operations |
|---|---:|---:|---:|---:|
| source30 short weight, plain carrier | 1081 / 109 | 1072 / 104 | 103 | 2144 / 112 |
| source24 middle weight, old full carrier | 1073 / 118 | 1064 / 113 | 112 | 2128 / 121 |
| source24 tight weight, old full carrier | 1069 / 120 | 1060 / 115 | 114 | 2120 / 123 |
| middle weight, new half carrier | 1069 / 117 | 1060 / 112 | 111 | 2120 / 120 |
| tight weight, new half carrier | 1065 / 119 | 1056 / 114 | 113 | 2112 / 122 |
| shifted w, tight weight, half carrier | 1061 / 120 | 1052 / 115 | 114 | 2104 / 123 |

The first row's product is **exactly source30's polynomial**, evaluated two
operations more cheaply. Its unshifted system is the same zero set with fewer
gates. Rows two and three use exactly source24's polynomial skeletons, with a
different, explicitly selected whole coefficient tuple: they must not be called
identical fixed polynomials to source24. The half-carrier rows and shifted-w row
are new polynomial skeletons. A shifted system changes the supplied transport
coordinate by z_old=z+1; it is not a literal polynomial identity at unchanged z.

All files bind the entire source30 compact Wang943 tuple:
beta=2^(5^10)-1, K0=K, MC=MC, MF=MF_source, where MF_source is the shifted mask.
`COEFFICIENT_BINDING.json` retains its complete four payload hashes and pinned
finite recipes. Never splice individual coefficient ports. The parent delivery
also contains the four reconstructed binaries under `../coefficients/`.

The inherited blank-machine compiler and K215 calibration imply, by ordinary
mathematics formalizable in ZFC, that each displayed presentation has no positive
solution iff Con(ZFC). This does not prove consistency, assert global minimality,
or supply a new kernel-checked end-to-end proof. The source30 interface is kept
unchanged, not inferred merely from coefficient hashes or numerical tests.

## 1. Common interface and explicit polynomials

Let omega=w except in the shifted-w family, where omega=w+q. Define

    q=beta J+1, Cw=q-F-alpha, X=omega q, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
    Delta=a^2+H=(a+2)^2-1,
    ell=EkY, A=1+ell(ell+k), G=1+Delta c^2, b0=X+ac,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    Nk=k-hE-R,
    Nt=(K0+omega)Cw+q-F-z(q-1),
    I=ic^2, D=1+Delta I^2, Q=(Delta I)^2, d=Q-1,
    v=cT, b=c+RD, e=Q(Dv^2+b^2)-1, Baux=2Qvb.

The three sharp weights are

    Cmid=E+3(X+Y),
    Ctight=E+2(X+Y)+sq^2,
    Cshift=E+2(X+Y)+sq,
    M=I(2T+RC ic).

Use Cshift only with omega=w+q. The new half carrier is

    L=1+HM, W=L b0+Ht.

The old full-carrier comparison has L=1+2HM and the same W. The source30
comparison instead has M=k(I^2+T^2), L=1+HM, W=b0+Ht.

Define an integer polynomial by the finite eight-factor conjugate product

    N = product over g^2=G, tau^2=A, f^2=D of
        [ d(W-Lg-HM tau)^2-H^2 e+H^2 Baux f ].

Each radical takes both signs. Sign invariance makes N an integer polynomial,
also when a radicand vanishes or is a square; the symbols add no unknowns.
The presentations are

    Nk=1, Nt=1, N=0;
    P=Nk Nt(1+N)-1=0;
    S=(Nk-1)^2+(Nt-1)^2+N^2=0.

## 2. A cheaper explicit scalar evaluator

The following is a complete division-free formula; the emitted JSON spells out
each charged binary gate and shares all stated registers:

    n=(HM)^2 A, dn=d*n,
    HQ=H^2 Q, HP=HQ(Dv^2), HU=HQ b^2,
    He=HP+HU-H^2, j=4HP HU,
    Trace=2d(W^2+L^2G), Knorm=d^2(W^2-L^2G)^2,
    AA=2(dn+He), constant=(dn-He)^2-j,
    at=Trace-AA, bt=constant-Knorm, coef=16dn j,
    vbar=coef-at(at Trace+2bt),
    ur=bt^2-at^2 Knorm,
    term1=ur(Trace vbar-ur), term2=Knorm vbar^2,
    N=term2-term1.

Juxtaposition denotes multiplication.

To verify, eliminating tau and f first gives a polynomial in x=d z^2:

    (x^2-AA x+constant)^2-coef x.

For z=W+/-L sqrt(G), the two x values have sum Trace and product Knorm.
Modulo x^2-Trace x+Knorm, the polynomial becomes ur-vbar x. Its norm is
ur^2-Trace ur vbar+Knorm vbar^2, exactly term2-term1. This is an identity
over the integer polynomial ring, so no nonzero-discriminant hypothesis or
division has been inserted.

Relative to source30, sharing HQ saves one multiplication. Evaluating the last
norm in Horner form saves another multiplication. Reversing the subtraction
that defined source30's vr costs no extra gate and permits the system's last
equation to be term1=term2, saving the final subtraction as well.

## 3. Product units and the inherited weak bounds

Put x0=d(W^2+L^2G). Then Trace=2x0 and

    Knorm=x0^2-4d^2 W^2 L^2 G.

Thus N=(ur-x0 vbar)^2 modulo 4. At a product root, Nk,Nt,1+N are integer
units; 1+N cannot equal -1 because -2 is not a square modulo 4. Hence N=0
and Nk=Nt=epsilon in {1,-1}. The system has epsilon=1 immediately.

The selected source30 authentic weak compiler interface now gives

    Cw>=0, q>=16, X>=16, Y>=4096,
    0<R<q^4-2, R>3q, E>=q^4>R+2,
    k=R+epsilon+hE>E, c>kY, c<k(Y+1).

These are available before any eliminated root is recovered. They include
the boundary Cw=0 and either unit sign. For shifted w, the old positive
coordinate omega=w+q is used in exactly this unchanged interface.

## 4. Uniform bound for all complex auxiliary roots

Consider coherent branches

    tau^2=A, f^2=D,
    d y^2=Q(vf-b)^2-1=e-Baux f.

Every conjugate f is +/-sqrt(D). Put Z=v sqrt(D)+b>1. The absolute-value
bound d|y|^2<=QZ^2+1 applies even if y is imaginary. We have b<=d and
sqrt(D)<Delta I<d: indeed Delta>R+2 and
Q-b=Delta I^2(Delta-R)-c-R>0. Also

    [Z(1+1/d)]^2-(QZ^2+1)/d=(QZ^2-d)/d^2>0.

Consequently

    |y|<Z+v+1<cT((a+2)I+1)+c+RD+1.                 (1)

Let rho=(1+1/Y)/E. Since sqrt(A)>ell and c/ell<rho, the contribution of
the first term in (1), divided by sqrt(A), is less than 2TI because
(a+3)rho<2. The residual harmless terms contribute less than 2. It follows
that each weight C with

    (a+2)^2 rho<C-2

satisfies

    |y|/sqrt(A)<2TI+R(C-2)i^2c^3+2<=M.             (2)

For Cmid the source24 estimate gives (a+2)^2rho<E+3Y+X+9<Cmid-2.
For Ctight and Cshift use the exact identity

    (a+2)^2rho=E+2Y+X+6+Y/X+5/X+4/Y+8/E+4/(EY).

The final four terms are less than 1. For Ctight, Y/X=sq^2/w<=sq^2.
For Cshift, Y/X=sq^2/(w+q)<sq. In each case X>=16 makes the right side
strictly less than E+2(X+Y)+B-2, with B=sq^2 or sq. This proves (2) in
all three families without assuming any square roots are rational.

## 5. Why the half carrier is sufficient

The inner degree-eight polynomial F(x) is the product of
d(x-M tau)^2-e+Baux f over both signs of tau and f. Every complex root
has the form x=M tau+y, so (2) gives |x|<2M sqrt(A).

The weak bounds also give G>A. For example
Delta c^2>k^2Y^2(E+Y)^2>k^2(E^2Y^2+EY)=A-1.
Moreover

    b0=ell+E eta+Yc+X>ell+k>sqrt(A).

At N=0 choose g=+/-sqrt(G) such that x=(W-Lg)/H is an inner root. If
g=-sqrt(G), the new carrier yields

    x=t+(M+1/H)(b0+sqrt(G))>2M sqrt(A),

a contradiction. If G is not a square, its two irrational quadratic roots
are conjugate, and the inner polynomial has rational coefficients; the
negative choice must then also give a root, again impossible. Thus the
chosen g is a positive integer and x is rational.

Work in a normal splitting field containing a coherent tau,f,y. If tau is
irrational, an automorphism negates it while fixing rational x. Subtracting
x=M tau+y from its image forces 2M sqrt(A)<=|y|+|y'|<2M sqrt(A), a
contradiction. Hence tau is rational and integral, and y=x-M tau is rational.
Because Baux>0, f=(e-dy^2)/Baux is rational and integral as well.

The rational Pell saturation lemma in the next section makes y integral.
Then x is integral, and W=L b0+Ht=L g+Hx with L=1 modulo H gives
g=b0 modulo H. Thus gamma=(g-b0)/H is an integer. In fact gamma>0:
g>(a+1)c, and c>k>E>X, so g-b0>c-X>0.

This proof does not divide by x or y, does not silently choose incompatible
signs, and does not assume all algebraic conjugates are real.

## 6. Rational auxiliary Pell saturation

If m>=2 and V are integers and rational y satisfies
m^2V^2-(m^2-1)y^2=1, write y=p/q reduced, q>0. Then q^2 divides m^2-1.
Set D0=(m^2-1)/q^2, a positive nonsquare integer. The two positive integral
Pell solutions (m,q) and (m|V|,|p|) are powers with indices j,l of the
fundamental integer-coordinate Pell unit. Their abscissas chi_j,chi_l obey
chi_j|chi_l. The addition identities give chi_(n+2j)=-chi_n modulo chi_j
and chi_(2j-n)=-chi_n modulo chi_j. Reduction and reflection of l into
0<=r<=j, together with 0<chi_r<chi_j for r<j, force l to be an odd
multiple of j. Pell addition then gives ordinate divisibility q|p.
Reducedness implies q=1. Neither ordinate is zero. This argument uses the
integer-coordinate Pell group, not half-integral units.

Apply it with m=Delta I and V=vf-b. Its equation is exactly the recovered
auxiliary equation, so all its hypotheses have now been established.

## 7. Compiler reconstruction, completeness, and coordinate shifts

The recovered integers satisfy

    tau^2-ell(ell+k)=1,
    (X+ac+H gamma)^2-Delta c^2=1,
    f^2-Delta i^2c^4=1,
    Q[c(Tf-1)-Rf^2]^2-(Q-1)y^2=1,
    Nk=Nt=epsilon.

The identity vf-b=c(Tf-1)-Rf^2 uses f^2=D. Take absolute values of tau,y.
If f<0, replace f,T simultaneously by -f,-T. The inherited normalized
signed-quotient interface permits that signed T, restores epsilon=1 and
extracts a blank K215 accepting tableau. No new signed-main-root theorem
is required because gamma is already positive.

Conversely keep a canonical positive normalized compiler witness and set

    t=y+M tau+L gamma>0.

Then W=L g+H(M tau+y), so a coherent factor of N vanishes. This proves
the half-carrier completeness directly, without an extra Pell congruence.

For the shifted-w construction, the authentic compiler gives X=omega q=2^R
and R>3q (source26 Section 8). Since q>=16 and 2^R>q^2, omega>q.
Equivalently, the explicitly documented canonical q=2^(dN) and
omega=2^(R-dN) satisfy R>2dN. Hence w=omega-q is strictly positive.
Conversely any new positive w gives a positive old omega=w+q. This is a
coordinate restriction whose completeness is proved after the compiler
interface; it is not an asserted pre-recovery fact about arbitrary w.

The shifted-system transport equation is

    (K0+omega)Cw=F+z(q-1).

Substituting z_old=z+1 makes it exactly Nt=1. Soundness is immediate.
Authentic solutions have Cw>0, omega>q>F, so
(K0+omega)Cw-F=(z_old-1)(q-1)>0. Therefore z_old>=2 and z is strictly
positive. The shift deletes one arithmetic gate. Neither shift changes
the number of supplied unknowns.

The source30 short/plain row uses source30's separate root-gap estimate
for M=k(I^2+T^2), quoted in full in `upstream/30-POSITIVE12_PROOF.md`.
Our three evaluator changes are polynomial identities and hence require
no new semantic argument for that row.

## 8. Exact degrees, including the new cancellations

Scale all twelve supplied variables by a parameter lambda and write a subscript
0 for the highest homogeneous part. Set q0=beta J and k0=eta+zeta. Let
X0=omega0 q0, Y0=sq0^3, E0=X0Y0, c0=k0Y0, R0=q0^3(q0-F), where
omega0=w except in the shifted family, where omega0=w+q0. Put

    d0=E0^4 i^2c0^4, H0=4E0,
    B=R0 E0^2 i^2c0^4                 (degree 38),
    D1=R0 E0 Y0 i^2c0^4              (degree 36).

The degrees remain H=6,d=46,D=34,b=38,M=27,A=G=22 in the three sharp
families. In a Laurent-series extension take sqrt(A)=ell+O(lambda), and
sqrt(G)=ac+2c+O(lambda^-1). The two gamma roots (g-b0)/H have orders -1
and 5. Also y=epsilon(b-vf)+O(lambda^-8), while vf has order 23.

The exact factorization is

    N=d^8 H^16 product_(16 coherent branches)
        [t-y-M tau-L gamma].

The difference M sqrt(A)-b has leading form delta, given by

    middle: delta=D1, degree 36;
    tight: delta=R0 E0(sq0^2)i^2c0^4, degree 35;
    shifted: delta=R0 i^2c0^3
      [ (2E0X0+E0 sq0-Y0^2)c0-E0^2 eta ], degree 34.

For the last formula it is essential to keep -E0^2 eta: this term now
ties at degree 13 in C ell-Delta c and cannot be discarded. Its bracket is

    X0^2 Y0^2(eta+2zeta)+k0 s^3 q0^8 w,

a nonzero positive-coefficient polynomial. These formulas follow from the
exact identities

    Cmid ell-Delta c
      =(EY+3EX-Y^2-4E-4Y-3)c-E Cmid eta,
    C ell-Delta c
      =(2EX+E Bextra-Y^2-4E-4Y-3)c-E C eta,

where Bextra=sq^2 or sq, and
M sqrt(A)-b=Ri^2c^3(C ell-Delta c)+O(lambda^28).

For the small gamma branch, four factors have leading +/-delta and four
have leading +/-2B. For the large gamma branch use
sqrt(G)+b0-2sqrt(A)=2Y0c0+lower terms. Six factors have leading magnitudes
2B,2B,4B, each twice. The remaining two have leader 3D1 for the middle
weight, and 2D1 for the tight and shifted weights. All signed pairs give
a positive product. Therefore

    middle half: N_top=9*2^12 d0^8 H0^16 B^10 D1^6, degree1060;
    tight half:  N_top=2^14 d0^8 H0^16 B^10 D1^2 delta^4, degree1056;
    shifted half:N_top=2^14 d0^8 H0^16 B^10 D1^2 delta^4, degree1052.

For example, the tight half leading form simplifies to

    2^46 i^48 k0^96 w^74 s^176 q0^646(q0-F)^16.

It is nonzero for every fixed beta>0. Multiplication by the nonzero leading
forms Nk0=-hE0 and Nt0=omega0(q0-F-alpha)-zq0 adds 7+2 degrees.
This proves exact product degrees 1069,1065,1061 uniformly, rather than
only for generic numerical coefficient choices. SOS has unique leading
summand N^2. The old full-carrier exact forms are source24's, and are
also verified by the same full polynomial ray checker. The short/plain
degree is source30's noncanceling leading form He0^8.

## 9. Reproduction, provenance, and negative scope

Run `python build_positive.py`, then `python check_positive.py` (NumPy is
used only by the independent finite-field polynomial checker). The emitter
requires only Python's standard library. It rejects dead gates and unused
ports. The checker independently multiplies eight factors in a rank-eight
quadratic algebra at 20 signed exact fixtures for each of six families,
checks the mod-4 unit guard, verifies both transport-coordinate descriptions,
and checks every analytic leading form using two complete univariate
specializations over finite fields. Fifty modular comparisons additionally
check the source30 literal-polynomial evaluator identity. These diagnostics
do not replace the unbounded arguments above or the inherited compiler.

All exact fetched sources are at ProveIt commit
8c6eec9d19ef80538c8e61ff6e0180040583446a, under
SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms.
`SOURCE_PROVENANCE.json` records Git blob IDs, URLs, and local SHA-256 values.
Main dependencies: source24 positive section and tight-weight emitter;
source25 hybrid weight proof; source26 ratio proof, especially Section 8;
source28 compact bound proof; source30 positive proof, generator and literal
product JSON. Received programs were inspected, not executed or imported.
The newly authored generator is self-contained. Source24's roots and source30's
trace/remainder evaluator are credited, not rebranded as new discoveries.

No eleven-positive-variable construction or equation below 67 operations was
established. The existence of nine-variable Jones presentations is unaffected.
These claims are finite explicit reductions, not a new representation theorem
or any proof deciding Con(ZFC).


