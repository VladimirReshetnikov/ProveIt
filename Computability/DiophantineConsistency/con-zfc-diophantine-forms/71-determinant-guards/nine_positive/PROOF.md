# A checked composition in nine positive variables

This construction combines three previously separate mechanisms in the pinned
ProveIt snapshot `9cca523d9f27ad39d52993f4065cbd7e58f8bdd4`:

1. Package 65's exact shared-coefficient source, convolution height 1873.
2. Package 63's unconditional deflated seventh-order root majorant.
3. Package 62's exact shared-power-chain rewrite.

The result is a single polynomial in nine strictly positive integers, exact
total degree **1,379,730**, evaluated by **478** live binary arithmetic
operations. Its nonnegative-coordinate translation has the same degree and
485 operations. This is a composition theorem with a new explicit polynomial,
not a new variable-count bound or a new native compiler.

## 1. Definition and fixed coefficients

The unknowns, in authoritative order, are

    b, g, h, s, w, C, i, j, n > 0.

The source weights, target positions and three coefficient polynomials D0,D1,D2
are specified by the complete integer tables `data/layout.json` and
`data/kernels.json`. Each coefficient is a fixed polynomial in the whole
original31 tuple `(beta,K0,MC,MF)`. The four fixed positive integers are the
little-endian values of `coefficients/payloads/*.bin.gz`; the binding gives
their exact byte hashes. `MF` is already shifted. The finite generator
`coefficients/build_coefficients.py`, with its literal transition/tile input,
reconstructs all four values. Thus no free program index, consistency oracle,
or unresolved coefficient parameter occurs in the equation.

Put a=2^2134939 and c=2^17079501. These letters are fixed constants.
For the weights w_l and target positions q_l in the tables set

    B=a b^2, ell=sum_l B^w_l, Targets=sum_l B^q_l,
    Us=ell+g, Gs=(D2(B)Us+D1(B))Us+D0(B), N0=B^117,
    Mask=N0-1-(b-1)ell,
    Sc=g+N0(2Gs+Targets), Tc=Mask+N0(B-2)Targets,
    L=b B^1991, R=L(Sc+Tc+1)-Sc-1,
    N=c b B^1057, t=b B^116.

Now define the polynomial abbreviations

    U=N^2 w, Y=N^2 s, M=RY, P=2M^2 U,
    K=R+1+h(P-1), A=M(U+1), B1=2R+1, W1=bw,
    J=4A-5, Q=3W1 C-2(W1^2-1),
    D=(A^2-1)C^2+1, e=iJC, E=eDC,
    F=(A^2-1)E^2+1, Lm=CD+1-A,
    G=A+F Lm, H=C+F(B1+(j-1)C), I=(G^2-1)H^2+1,
    a0=(P^2-1)K^2+1, a1=4096^2 DFI,
    m=K^2(4t-g)-16t(C-KY)^2,
    V0=PK, Omega=Jm, E0=J(n+W1^2)+Q.

Finally define

    Ns=2G+Lm,
    N1=2e^2 D(D-1)Lm+3C,
    N2=2e^2(D-1)Lm,
    N3=2e^2(Lm-C), N4=2e^2 C,
    T=e[(2048D^2-1024D-256)Ns-128N1-80N2-56N3-42N4
          +i^2(1568-448A+288C)]+640i+4096,
    V1=TH, Theta=E0-Omega(V0+V1).

The equation is

    F9=(Theta^2-Omega^2(a0+a1))^2-4Omega^4 a0a1=0.

Every power is a fixed nonnegative integer, every register is an abbreviation,
and all operations are polynomial. The complete division-free DAG is
`generated/composed9_positive.json`; all its fixed leaves have exact recipes.
The natural version replaces each positive variable by its natural successor,
except that natural j directly supplies the existing j-1 register.

## 2. Source compatibility

The source is the literal 31-coordinate, 22-equation positive system in
`data/source_system65.json` (SHA256
`3338193dfab9b409a198df086316a41a0dc987b4ba462d25e44c7de6fca62094`).
Its two invertible row operations are rho14=r14+r2 and rho15=r15+r3.
The source tables encode exactly

    [Z^q_l](D2(Z)Up(Z)^2+D1(Z)Up(Z)+D0(Z))=2 rho_l(p),
    Up(Z)=sum p_l Z^w_l.

Equal complete coefficient requirements may share a kernel position. They
are stored once, not added. The independent source audit checks all 11,616
coefficients of the 22 target identities, including absent monomials.
There are 89 weighted records and 84 distinct stored positions.

The largest coordinate weight is 116. The three kernel degrees are
1384,1739,1641, giving convolution height 1873. Package 65's proof applies
literally to these unchanged tables and coherent original31 coefficients.
It proves unconditional positivity of Gs, the weak-cap soundness bound,
signed-digit extraction, and the exact binary calibration

    N^2 divides binomial(2R,R)
       iff the encoded positive source coordinates satisfy all 22 equations.

Here the source witnesses are cofinal in sufficiently large binary b. The
stronger completeness bound is g<t; the recovered soundness range is g<4t.
The complete retained proof is `upstream65_PROOF.md`, Sections 1--4.
No claim about arbitrary integer b is inferred merely from digit notation.

## 3. Why the majorant can be substituted

Package 63 proves for every A>=3,C>=1,i>=1, independently of a source zero,

    T > 4096 sqrt(DF) G > 0.

The proof depends only on the displayed Pell registers, which are identical
here. Its source-dependent values R,N,t do not enter the majorant theorem.
For example its exact algebraic certificate uses

    tn=2048D^7-1024D^6-256D^5-128D^4-80D^3-56D^2-42D-33,
    dn=109824D^6+36608D^5+18304D^4+9984D^3
         +5460D^2+2772D+1089,
    tn^2-2048^2 D^13(D-1)=dn,
    Rn=D^5 T-e tn Ns.

The polynomial Rn-4096D^5 has exactly 264 positive coefficients after
substituting A=x+3,C=y+1. Those coefficients are supplied explicitly and
independently re-expanded by `check_majorant.py`. Thus the majorant is a
uniform algebraic theorem, not a large-input estimate. Its full elementary
inequality argument is retained in `upstream63_PROOF.md`, Sections 2--4.

Consequently V1>sqrt(a1), while V0^2-a0=K^2-1>0. At a zero m cannot vanish,
because m=0 gives F9=E0^4 and

    E0=Jn+(J-2)W1^2+3W1C+2>0.

Factoring the quartic over the reals gives

    E0/J=m(V0+V1+u0+u1), u0^2=a0, u1^2=a1,

with signed real roots. Both majorants make the parenthesis positive; hence
m>0 before any use of square-root integrality. The inherited free-carrier
margin proof recovers C>K and C>B1+W1. It then gives a1>a0, so the rational
sum u0+u1=Theta/Omega is nonzero. From

    2(u0+u1)u0=(u0+u1)^2+a0-a1

both roots are rational, hence integral. Also u1/4096 is a rational root of
the integer DFI, hence integral. The same factorization yields J|Q.

These are exactly the inherited ratio conditions. They recover a binary
base and the binomial divisibility, and hence a source zero. Conversely a
source zero supplies cofinal ratio witnesses and integral roots. The same
integer choice

    n=m(V0+V1+sqrt(a0)+sqrt(a1))-W1^2-Q/J

is strictly positive by the majorant bound, and makes F9 vanish. These steps
are stated with the required proof ordering in `upstream59_PROOF.md` and
`upstream63_PROOF.md`; the outer bounds are supplied by the unchanged source 65.
Composition therefore proves the zero-existence equivalence with the pinned
native source. The inherited native compiler and K215/refutation calibration
give, by ordinary arguments formalizable in ZFC,

    ZFC |- ((no positive integral zero of F9) <-> Con(ZFC)).

This statement is not a newly supplied Lean/Rocq or object-language ZFC proof.
It retains the same explicitly identified compiler/calibration dependencies.

## 4. Exact degree

Let r=deg R=7963, q=deg N=2115, and W=116. Then

    deg A=r+4q+2=16425,
    deg H=8 deg A+10+r=139373,
    deg Omega=5r+20q+2W+13=82360.

The exact T7 remainder has leading monomial 2880 A^10 C^12 i^3, giving
degree 164265. The cancellation-resolved identity implies

    deg(T^2-4096^2 DFG^2)=15 deg A+24=246399,
    deg(V1^2-a1)=31 deg A+2r+44=525145.

Set delta0=V0^2-a0,delta1=V1^2-a1 and

    Bsmall=E0^2-2E0 Omega(V0+V1)+Omega^2(delta0+delta1).

Then exactly

    F9=Bsmall^2+4Omega^2 V0V1 Bsmall
                  +4Omega^4(delta0 V1^2+a0 delta1).

The leading term is the square of Omega^2 delta1, and hence

    deg F9=86r+328q+8W+264=1,379,730.

Its diagonal leading coefficient, with fixed positive a,c as above, is

    2025 * 2^188 * a^689526 * c^328 > 0.

Thus the degree upper bound is attained on the actual fixed-coefficient
instance. The separate resolved-degree DAG computes D^20 F9, degree 2,036,770;
it is a verification artifact, not the primary equation or its operation count.

## 5. Circuit rewrite and scope

The direct composed evaluator has 489 operations. The shared-power algorithm
replaces pure powers of B by a common addition chain, reducing this to 478.
The exact certificate lists each e=a+b addition; the verifier compares the
remaining expression DAGs structurally after canonicalizing powers of B.
This establishes a polynomial identity, not just equality at test points.

The source identities, 264-term majorant certificate, defect identities,
resolved degree and exponent rewrite are checked exactly. Forty modular
assignments independently check transcription of the full primary and
certificate formulas. These checks do not test consistency or replace the
unbounded mathematical proof. Normal and optimized Python runs pass.

Compared with package 67's prior lowest-degree nine-positive entry
(1,494,006; 487 operations), this polynomial saves 114,276 degrees (7.64897%)
and 9 operations. Lower-operation higher-degree entries, such as package 62's
453-operation equation, retain their advantage. No global optimum or new
literature priority is claimed for the ingredients.
