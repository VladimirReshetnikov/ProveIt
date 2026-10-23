# Fifty-integer quartic and cheaper twenty-four-integer ratio norm

## 0. Fixed instance, dependencies, and statements

Every new artifact in this directory selects **one complete compact Wang943
tuple** from `../coefficients/COMPACT_COEFFICIENT_BINDING.json`:
`beta=beta`, `K0=K`, `MC=MC`, `MF=MF_source`. Here
`B=2^(5^10)` and `beta=B-1`; `MF_source` is the already shifted mask.
The four ports are fixed integer coefficients, never quantified unknowns.
No port is taken from the mixed-radix tuple in the historical source27 files.

The source30 whole-tuple transfer proof, copied as
`upstream/integers/COEFFICIENT_TRANSFER.md`, establishes the signed arithmetic
interface for this compact tuple. Its odd-scale extension is in
`upstream/integers/SIGNED_ODD_SCALE_FAMILY_PROOF.md`, Section 5. In particular
canonical witnesses simultaneously have odd normalized multiplier, square w,
and odd positive s. These facts depend on the full compiler, five-power padding,
and exact mask-population identity, not merely on coefficient residues.
The shared coefficient directory contains the finite recipe and payloads.

The new results, under the binary +,-,* convention including constant
multiplications, are:

| Domain | Equations | Exact degree | Operations | Artifact |
|---|---:|---:|---:|---|
| 50 unrestricted integers | 29 | 2 | 111 | integer50_quartic_system.json |
| 50 unrestricted integers | 1 | 4 | 197 | integer50_quartic.json |
| 24 unrestricted integers | 3 | 1920 | 156 | integer24_ratio_system.json |
| 24 unrestricted integers | 1 | 1936 | 161 | integer24_ratio_product.json |
| 24 unrestricted integers | 1 | 3840 | 164 | integer24_ratio_sos.json |

Comparisons are free. The three-equation system's third comparison does not
compute a residual subtraction. Its SOS is the sum of the squares of the
three mathematical residuals, not the square of their product.

For each artifact the inherited compiler and literal K215 calibration give,
by ordinary mathematics formalizable in ZFC,

    ZFC proves: no solution in its stated domain iff Con(ZFC).

This is neither a proof of consistency nor an end-to-end proof-assistant
certificate. No global minimality is asserted. The new arguments are complete
algebraic/domain reductions of the explicit inherited Pell/compiler interface.
The unbounded compiler, Pell-rank and K215 endpoint theorems remain named
dependencies. `SOURCE_PROVENANCE.json` identifies all 22 exact upstream text
files, fetched at commit `8c6eec9d19ef80538c8e61ff6e0180040583446a`, with both
SHA-256 and Git-blob SHA-1. Upstream code is inert reference material.

## 1. The fifty-integer quadratic system

Start with the 31 core coordinates of source30's quartic, replacing its i and
s coordinates by r and s_odd. Add a coordinate u and three disjoint coordinates
for each of J,F,alpha,z,eta,zeta. Thus there are 31+1+18=50 unrestricted
integer coordinates. Set the affine abbreviations

    i=2r+1, s=2s_odd+1, q=beta J+1,
    k=eta+zeta, H=4a+3, C=q-F-alpha.

The 22 core equations are

    L=q²-1,                 N=q(L+1),
    X=wq,                   a=E+sN,
    E=X(a-E),               c=k(a-E)+eta,
    P=E(c-eta)+k,           tau²=P(P-k)+1,
    D=X+ac+gamma H,         Delta=a²+H,
    C2=c²,                  D²=Delta C2+1,
    k=jc-V+1+hE,
    jc-V=(q-F)(N-q)-CL+(MC+q MF)J,
    (K0+w)C=F+z(q-1),
    F2=f²,                  V=of-c,
    g=y²-V²,                I=i C2,
    Baux=I²,                Baux=Delta(F2-1),
    y²-Baux g=1.

The remaining seven equations are w=u² and, for each guarded port x,

    x=Pos(x1,x2,x3)=1+x1²+x2²+x3(x3+1).

Pos is always a positive integer and is onto the positive integers. Indeed
Legendre's three-square theorem represents 4n-3 by three squares. Exactly one
square is odd modulo 4; take its root to be 2x3+1, and divide the other two
even roots by 2. This gives n=1+x1²+x2²+x3(x3+1).

All displayed residuals are quadratic. The single polynomial is their sum of
29 squares. It has degree exactly four because tau occurs only through tau²
in its first-root residual, so the coefficient of tau⁴ is exactly one.

Important convention: z in this construction is the **shifted** positive
transport coordinate. It is not source30's old z coordinate. The transport
equation is the displayed shifted equation, matching source27's integer51.
No offset is silently dropped.

### Exact restoration, including negative s

The eliminated source27 register is G. Define

    G=q(q-F)-C=(q-1)(q-F)+alpha.

The polynomial identity

    LG-[(q-F)(N-q)-CL]=(q-F)[q(L+1)-N]

shows that the new packing formula equals LG whenever the N equation holds.
The new index and packing equations therefore restore the old two residuals

    k-1-hE-LG-(MC+q MF)J=0,
    k-1-hE-jc+V=0.

Conversely, subtracting these old residuals gives the new packing equation.
Every other equation is literally unchanged after the affine i,s substitution
and shifted transport normalization. This is an invertible row operation plus
elimination of the uniquely determined register G. It is valid over arbitrary
integers, before the sign of s is known.

In fact G is positive as well: q>1, K0+w>0, and shifted transport gives
C=(F+z(q-1))/(K0+w)>0; hence G=(q-1)C+q alpha>0. This uses none of s,h,
gamma,f,o,j having positive sign.

The exact old signed-quartic soundness theorem is supplied in
`upstream/source27/LOW_DEGREE_PROOF.md`, including its exposed-quotient argument.
Its crucial order is preserved: main norm excludes w=0 modulo H; the signed
first/main Pell ranks and ordinary strong-rank theorem give f²=1 modulo c,
including the initially negative-s case; then

    T=(o+Rf)/c is integral,
    c(Tf-1)-Rf²=of-c=V,

where R=LG+(MC+q MF)J. The signed odd-scale theorem now excludes s<0 and
decodes the native blank computation. We do not apply a positive-s theorem
before establishing this conclusion. Restoring G introduces no new sign or
divisibility obligation.

Conversely a canonical blank accepting computation supplies the old lift with
odd s, square w, and odd ordinary multiplier i. The latter follows from the
canonical odd normalized multiplier and odd Delta (canonical a is even).
Forget G and retain all other coordinates. The same positive-surjection
preimages give the new fifty-integer witness. Thus this reduction preserves
existence, and indeed gives a bijection between the two retained signed zero
sets with the same fixed tuple. It improves the 51-integer quartic by one
variable; it does not claim a 30-positive-variable quartic.

## 2. The twenty-four-integer ratio-weight construction

For each guarded port J,F,alpha,z,eta,zeta use a separate Pos triple, and set

    i=2i_integer+1, s=2s_integer+1, w=w_integer².

Retain arbitrary integer h,T,t. This is 18+3+3=24 unrestricted integers.
All following symbols are computed polynomials, not supplied coordinates:

    q=beta J+1, C=q-F-alpha, X=wq, Y=sq³, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
    Delta=a²+H, ell=EkY,
    A=1+ell(ell+k), G=1+Delta c², b0=X+ac,
    R=((q-1)(q-F)+alpha)(q²-1)+(MC+q MF)J,
    Nk=k-hE-R, Nt=(K0+w)C+q-F-z(q-1),
    I=ic², D=1+Delta I², Q=Delta(D-1)=(Delta I)², d=Q-1,
    v=cT, b=c+RD, e=Q(Dv²+b²)-1, Baux=2Qvb.

Here z is the **old** source transport coordinate, unlike Section 1.
Each artifact explicitly uses the correct formula. Define the new weight

    M=2(5Rac iI+v²), L=1+HM, S=b0+Ht.

For formal roots u²=G, tau²=A, f²=D define the integer polynomial

    N= product over the eight signs of (u,tau,f) of
       {d(S-Lu-2HM tau)²-H²e+H²Baux f}.

Its division-free evaluator is given in Section 4. The three equivalent
existence formulations are

    Nk=1, Nt=1, N=0;
    P24=Nk Nt(1+N)-1=0;
    (Nk-1)²+(Nt-1)²+N²=0.

## 3. Complete sign-safe proof for the smaller weight

The norm is a square modulo four, as proved in Section 4. Consequently a
product zero gives N=0 and Nk=Nt=epsilon in {1,-1}. The comparison and SOS
forms already assert the positive unit signs.

Weak transport excludes C<=-1 since then Nt<=-(K0+w)<=-2. The complete
authentic mask interface therefore gives

    q>=16, q(q²-1)<R<q⁴-2.

These deductions do not assume s>0,w>0 or h>=0. Put Z=|Y|>=q³. Then
X>=0, a and c have the same sign, |a|=(X+1)Z>=4096, |c|>k(Z-1)>1,
|H|>6, Delta>q⁴>R, G>4. Odd i is nonzero. As in source27,

    D>Delta+|c|, Q>1, d>0, 1<b<Q.

For example Q-b=(Delta-R)D-Delta-c>0 and b=c+RD>D-|c|>1.

A zero of the product supplies algebraic roots with

    d y²=e-Baux f=Q(vf-b)²-1,
    S=Lu+2HM tau+Hy,
    u²=G, tau²=A, f²=D.

This factorization covers repeated or square radicands and Baux=0. Every
actual conjugate y', including complex ones, satisfies

    |y'|<2(|v|sqrt(D)+b).

If the squared equation's real right side is negative, its absolute value is
at most one; otherwise its absolute value is bounded by
Q(|v|sqrt(D)+b)²-1. Either case gives the displayed strict estimate.

Here is the full ratio bound with the new simplification. Since i²c²>1,

    D/G < i²c²,
    2|v|sqrt(D)/sqrt(G) <= 2|iT|c² <= iI+v².

Writing a0=|a|>=4096 gives sqrt(Delta)>a0-3,
D<(a0+2)²i²c⁴, and (a0+2)²/(a0-3)<2a0. Thus

    b/sqrt(G)<1+2Rac iI.

Combining these inequalities,

    |y'|/sqrt(G)<iI+v²+2+4Rac iI
                    <5Rac iI+v²=M/2.

The last step is valid because (Rac-1)iI>2: ac=|a||c|>8192, R>4080,
and iI=i²c²>=1. It holds with T=0 and with either sign of i,s,H.
The old ratio weight included a redundant +iI inside its parentheses;
the new strict inequality removes it without weakening any boundary case.

Put B=|H|M>8. Since L=1+HM,

    |L|>B/2, |L|<(9/8)B,
    |L|sqrt(G)>|H||y'|.                         (I)

If X=0 then A=1 and tau is integral. An automorphism changing an irrational
u to -u in the linear relation contradicts (I); therefore u and y are rational.
If Baux!=0, f=(e-dy²)/Baux is rational and f²=D makes it integral. If Baux=0,
then v=T=0 and the auxiliary equation is directly Qb²-(Q-1)y²=1.
In both cases the saturation lemma below makes y integral. Reduction modulo H,
using L=1 mod H, makes gamma=(u-b0)/H integral. The main equation at X=0 now
gives 1=H(2ac gamma+H gamma²-c²), impossible since |H|>1. Hence X>=q>=16.

For either sign of Y, with Z>=4096 (even Z>=32 suffices),

    |a+2|/(XZ)<=273/256, |c|/(kZ)<33/32,
    sqrt(G)<(9/8)sqrt(A).

Consequently

    |L|sqrt(G)+|H||y'|
       <(9/8+1/2)B sqrt(G)
       <(117/64)B sqrt(A)<2B sqrt(A).            (II)

An actual field automorphism flipping irrational tau contradicts (II).
Thus tau is integral; a subsequent u flip contradicts (I), so u is integral.
Again y is rational, saturation makes it integral, and gamma is integral
modulo H. This argument uses only existing automorphisms of the actual field;
it does not assume generic independence of the radicals.

T=0 would now imply (Q-1)(y²-b²)=b²-1>0. Integral y has |y|>=b+1, whereas
Q-1>=b, yielding b²-1>=b(2b+1)>b²-1, a contradiction. Therefore T and
Baux are nonzero, and the recovered f is integral. We have restored precisely

    tau²=1+ell(ell+k),
    (X+ac+gamma H)²-Delta c²=1,
    f²-Delta i²c⁴=1,
    Q[c(Tf-1)-Rf²]²-(Q-1)y²=1,
    Nk=Nt=epsilon.

The signed odd-scale theorem in the bundled
`upstream/source27/sources/23-separating12/proofs/ODD_SCALE_27_PROOF.md`
applies now, not earlier. It proves s>0 and epsilon=1 by the first/main Pell
rank congruences, signed auxiliary step-down, p=R, and exclusion of both main
root signs modulo H in the negative-s branch. Its complete proof is included.
The authenticated signed compiler then gives the accepting blank computation.

Conversely take canonical compiler witnesses with the simultaneous odd i,
positive odd s and square w. Put

    t=gamma+M u+2M tau+y.

Then S=Lu+2HM tau+Hy, so one coherent norm factor vanishes. Nk=Nt=1.
Choose Pos preimages and the two odd-parameter preimages. This constructs a
zero of every displayed 24-integer formulation. No extra Pell period, root
positivity or sign restriction on the new coordinate t is imposed.

### Rational auxiliary saturation used above

For integer m>=2 and V, a rational y satisfying
m²V²-(m²-1)y²=1 is an integer. Write m²-1=d0 b0² with d0 squarefree.
The rational number z=b0 y has d0 z² integer, so it is an integer (a reduced
denominator squared cannot divide squarefree d0). The two nontrivial Pell
solutions (m,b0) and (|mV|,|z|) have indices j,l in powers of the fundamental
integer-coordinate unit. The addition identities modulo chi_j give
chi_(n+2j)=-chi_n and chi_(2j-n)=-chi_n. Reduction and reflection to 0<=n<=j,
where 1<=chi_n<chi_j for n<j, show chi_j|chi_l only if l is an odd multiple
of j. Then psi_j|psi_l, so b0 divides z and y is integral. This is a special
Pell saturation statement, not a false assertion about arbitrary rational
Pell points.

## 4. Division-free scalar evaluator and comparison saving

Put

    n=(2HM)² A, dn=d n, H2=H², HQ=H2 Q,
    HP=HQ Dv², HU=HQ b², He=HP+HU-H2,
    j=4HP HU,
    Trace=2d(S²+L²G), Knorm=d²(S²-L²G)²,
    AA=2(dn+He), constant=(dn-He)²-j,
    at=Trace-AA, bt=constant-Knorm, coef=16dn j,
    vbar=coef-at(at Trace+2bt), ur=bt²-at² Knorm.

Then

    N=ur(ur-Trace vbar)+Knorm vbar².

To prove the identity, first eliminate f and tau in the eight-factor product.
For x=d(S+/-L sqrt(G))², its factor is

    (x²-AA x+constant)²-coef x.

The two x roots have sum Trace and product Knorm. Modulo
x²-Trace x+Knorm the displayed quartic reduces to ur-vbar x. Multiplying
these two remainders gives N. This is a universal integer-polynomial identity
in any commutative ring, including repeated-root specializations.

The shared HQ avoids separately computing QDv² and Qb² before multiplying
both by H². Horner evaluation of the final quadratic norm saves another gate.
For a system, the last equality can be written directly

    ur(Trace vbar-ur)=Knorm vbar²,

saving the final addition as well. Its left-minus-right residual is -N.
No division, branching, constant-size oracle, or free arithmetic is concealed.

Finally Trace=2x0 for x0=d(S²+L²G), while Knorm=x0² modulo 4. Hence
N=(ur-x0 vbar)² modulo 4, proving the unit argument for the product finalizer.

## 5. Uniform exact degrees

Before substitution, assign weight two to J,F,alpha,z,eta,zeta,w and weight
one to i,s,h,T,t. The actual Pos, odd and square substitutions realize these
weights with nonzero leading forms. The relevant degrees are

    q=2, X=4, Y=7, E=a=H=11, c=9, Delta=22,
    ell=20, A=G=40, R=8, I=19, D=60, Q=d=82,
    v=10, b=68, M=48, L=59, S=20.

Use a star for highest homogeneous part. Then

    A*=G*=ell*², e*=d* b*², M* ell*=10b*.

The four (u,tau)-branches of S-Lu-2HM tau have top parts with multiples
-3,-1,1,3 of 10H*b*. Thus, after subtracting H²e, the leading coefficients
of d times their squares are 899,99,99,899 times d* H*² b*². The remaining
f-dependent term H²Baux f has degree 212, below 240. Multiplying all eight
factors proves

    N*=(99*899)^4 d*^8 H*^16 b*^16, degree 1920.

This is nonzero for every fixed beta>0. The index leader is -h E*, degree12;
the transport leader is w*(beta J*-F*-alpha*)-z* beta J*, degree4. The latter
is nonzero, for instance after setting w_integer=0. The polynomial ring has
no zero divisors, so P24 has exact degree1936. The SOS has exact degree3840,
since N² is its unique highest-degree summand. The system has exact maximum
residual degree1920. These are uniform proofs, not merely sampled degrees.

## 6. Reproduction, independent evidence, and boundaries

Run `python build.py` and `python check.py`. The former reads only inert JSON
and writes the five literal circuits. The checker uses SymPy and NumPy; it
does not import or execute any received program. It verifies the quartic
packing syzygy and every retained residual symbolically, expands the 414-term
quartic, and independently certifies its tau⁴ coefficient. For the large norm
it multiplies all eight factors in a rank-eight quadratic algebra rather than
using the scalar evaluator as its reference. It checks 208 fixtures, including
eight exact-integer cases, and also checks the comparison and SOS finalizers.

Two exact finite-field univariate polynomial calculations use the actual
shared tuple's residues, attain degrees1920/1936, and match the proved leading
formula. Separate fixed-tuple finite differences prove every supplied variable
is algebraically live, in addition to graph liveness and literal gate counts.
These finite audits supplement, not replace, the universal sign/Pell/compiler
arguments. They do not search for or produce an accepting K215 computation.

The positive quartic remains 31 variables; the sextic42 and octic36 variants
already eliminate the G register, so the same trick gives no additional saving
there. No smaller positive quartic or smaller-than-24 moderate-degree integer
domain is claimed by this package.
