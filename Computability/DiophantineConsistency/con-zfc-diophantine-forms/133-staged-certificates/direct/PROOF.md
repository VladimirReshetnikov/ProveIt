# Staged shared-index certificates for the direct C222 equation

## Statement and attribution

The modified finite graph in `build_combined.py --staged` has a natural zero
if and only if the retained shared-binomial direct C222 source has a zero.
Composed with that source's identified ordinary C222/ZF/ZFC refutation
calibration, its quartic sum of squares has no natural zero if and only if
Con(ZFC), provably by ordinary mathematics formalizable in ZFC.
This statement does not prove either side, assert global minimality, or
supply a newly completed Lean/Rocq/object-language ZFC certificate.

Three inspected inputs are used, not claimed as new: the shared-binomial
construction in `ConZFC_Shared_Binomial_Certificates_2026-10-24` (six exact
powers, one factorial/product binomial, eleven modular digit requests),
and the one-cap bounded Pell-index lemma in
`ConZFC_Shared_Pell_Bound_261_2026-10-24/portable/CAP_THEOREM.md`,
and the dominant-denominator proof in
`ConZFC_Residue_Compiler_2026-10-24/proofs/MODULAR_NUMERATORS_PROOF.md`.
The new feature is **staging** the bounded-error congruences, here combined
with the credited reuse of the dominant denominator. The exact
powers and factorial are interpreted before the ranges. The giant derived
label index is never added to the early frame. It is bounded later by the
now-certified radix. This avoids a circular attempt to use an unproved
range-digit bound in the first Pell decoding step.

## Fixed arithmetic source

All coordinates below range over nonnegative integers. Arithmetic names
are abbreviations for the literal quadratic gates in the artifacts.
Use

    t=t0+16, R=2+t+x+y+F, K=2R, B=b0+2,
    V=(F^2+1)^t, N=B^K, q=N^K,
    Dt=q^t, Dy=q^(y+1), Dx=q^(x+1).

These are the **six** exact-power requests; their equalities are conclusions
of the power graph, not assumptions used before its interpretation. Their
four distinct exponent atoms are t, K, y+1, x+1. The extra denominator
D(t+1)=q*Dt is an ordinary multiplication.

Let A1,...,A8,C be the nine independent positive CRT representatives, with
sum at most 9N^2. Let J(A1,...,A4) be the actual positive label polynomial.
The ten range-digit upper indices are A1,...,A8,C,J. The exact binomial has
upper index n0=F^2+t, lower index t, and output B. Its ceiling rows are

    V+B=BF+r+1,       B=r+s+1.

Their intended consequence is F=t!, after the binomial is interpreted.
The original C222 constructors, Horn-flow rows, endpoint equations,
reciprocal index congruence, ten range requests, and source majorant are
unchanged. In particular E=2^23 and ell=2^22 are the inherited local and
label majorant exponents; their exact generating certificates are retained.

## One cap for fifteen principal pairs

For a>=2 define the standard natural Pell sequence by

    X0(a)=1, Y0(a)=0,
    X(j+1)=a Xj+(a^2-1)Yj,  Y(j+1)=Xj+aYj.

Its elementary properties used here are: all natural norm-one pairs have
this form; Yj is strictly increasing; Yj(a)=j mod(a-1); and
Y(j+1)>(2a-1)Yj for j>=1. These follow by Pell descent and the recurrence.

Let S be the set of distinct atoms among all bases, exponents, and outputs
of the six exact-power requests. Retain the original definition

    W=2+sum(S).

It contains twelve atoms in this literal graph. No CRT representative,
J-value, Pell witness, or cap witness is inserted. Define L,A,Z by the
retained lower-frame equations

    L^2-((W+1)^2-1)(WZ)^2=1, Z=z0+1, A=L+sigma.

Pell classification modulo W gives L=X_e(W+1) with positive W|e. Hence
L>=X_W(W+1)>=(W+1)^W, and A-1>W^3. Also W>=K+2>=38, so the fifteen
seed count is at most W-2. Every exact-power base, exponent, and output is
strictly less than W, directly from the sum row.

Retain one complete inherited indexed-Pell certificate at index W. It
forces a pair (Xcap,Ycap)=(X_W(A),Y_W(A)). Its needed lower bound W<=Ycap
follows from the new aggregate row below; it requires no separate slack.
The certificate consists of the three usual Pell norms and congruence
rows as specified literally in `CAP_THEOREM.md` and the new equation.
It is used with A>=2. Its completeness is valid for every such fixed A
and positive W.

For each of the fifteen seed indices retain just its principal norm

    Xi^2-(A^2-1)Yi^2=1.

All fifteen ordinates occur in the one row

    Ycap=W+1+u+sum_i Yi.

Therefore Pell classification gives a unique actual index ji satisfying
0<=ji<W for every seed. At this point no assertion about ji equalling the
requested index is made.

## Two error congruences

Partition the requested seed indices into

    I0={t,K,y+1,x+1,F^2+t},
    I1={A1,...,A8,C,J}.

The actual code uses identity of expression atoms, and the emitted
`cap_certificate.json` records the exact partition. Its sizes are five
and ten. All requested indices are positive by their raw definitions.
Use two independent natural quotients Q0,Q1 and rows

    sum_(k in I0) (Yk-k)^2 = (A-1)Q0,
    sum_(k in I1) (Yk-k)^2 = (A-1)Q1.

Only fixed-degree polynomial arithmetic occurs in these equations.

For any one group, if its requested indices are already proved below W,
reduce its row modulo A-1. The Pell congruence gives divisibility of
E=sum(jk-k)^2 by A-1. Since there are at most fifteen terms,

    0<=E<=15(W-1)^2 < W^3 < A-1.

Thus E=0, so each actual index equals its requested index. This argument
is applied twice, with different prerequisites. It does not assume the
large Pell ordinates themselves are below A-1.

### Stage 1: exact powers and the factorial binomial

The four power indices in I0 are atoms of S, so are below W. The remaining
index n0=F^2+t is also below W **without interpreting any power**: the two
distinct atoms F^2+1 and t are in S, giving W>=F^2+t+3.
The first error row therefore identifies all five principal pairs.

For each exact request m=n^k the unchanged modulus rows are

    Tn=2An-n^2-1,
    Xk+(n-A)Yk=m+Tn*h.

Their natural Tn excludes n=0. Since n,k,m<W and A>=(W+1)^W, both m and
n^k are strictly smaller than the positive Tn. The standard Pell identity
modulo Tn yields m=n^k. Thus all six exact powers are now known, in
particular N=B^K, q=N^K and B>=2.

Before any binomial semantics, one more raw consequence is needed for the
smaller common-root modulus. The ceiling equations give V+s=BF, and the now
certified V=(F^2+1)^t is positive. Hence F>=1. The endpoint equations give

    y=F+1+r0>=2,  x=F+1+(y+1)u0>=2,
    x=1+(1+(t+1)y)ut.

The last equality forces ut>=1, so x>=2+(t+1)y and therefore
x>t+1 and x>y+1. This uses neither B's binomial value nor F=t!.
Consequently the smaller common modulus

    M=N*Dx=N*q^(x+1)

is divisible by q*Dt=q^(t+1) and by every N*q^k used in a range request,
where k is one of t,t+1,y+1,x+1. Its multiplication is already present in
the range rows for the two quotient columns. Three earlier product gates
are removed, with no new power or indexed Pell certificate.

The independent radix estimate from the inspected shared-binomial proof
now applies, before any factorial semantics:

    q >= 2^(4R^2),
    binom(F^2+t,j) <= (F^2+t)^t <= (R^2+R)^t
                     <= 2^(2Rt) < q, 0<=j<=t.

The common-root congruence below supplies a correct modular numerator for
this exact binomial, since its index F^2+t is already certified. Its digit
rows therefore give B=binom(F^2+t,t). They and the exact power V imply
F>=1. The previously proved squared-radius fixed-point lemma, valid for
t>=6, then gives

    F=ceil((F^2+1)^t/binom(F^2+t,t))=t!.

### Stage 2: all ten range indices

The exact radix and the aggregate representative row give
A1,...,A8,C<=9N^2<q. The strict last inequality follows from N>=2^(2R),
K=2R, R>=18. It does not use a range-divisibility interpretation.

The retained positive-DAG bound gives

    J <= (9N^2+1)^ell <= N^(3ell).

The factorial value now justifies the inherited budget
3ell(t+1)<=2F<K. Hence J<N^K=q. Every index in I1 is therefore below
q<W. The second error row is now eligible and certifies their exact
Pell indices. No second-group Pell interpretation was used to derive
these bounds. This is the crucial dependency separation.

## Modular numerators and common-root compatibility

Write b=q+1 and

    M=N*Dx.

The endpoint argument in Stage 1, already proved before interpreting the
exact binomial, ensures that all required digit moduli divide M.

The original single root-congruence row is retained:

    2A(q+1)=(q+1)^2+1+M*h0.

The corresponding substitution into Pell's quadratic algebra gives, for
every now-certified index n,

    Xn(A)+(q+1-A)Yn(A) = (q+1)^n mod M.

Its left side is positive: for n>0, Xn>(A-1)Yn, so it exceeds qYn; at n=0
it is one. Every needed q*d or N*d divides M, so the retained remainder
rows correctly extract the exact binomial or the range divisibility.
The low-digit carry bounds are the original shared-binomial bounds. After
Stage 2 these imply all ten N|binom(n,k) constraints. The unchanged
prime-power CRT, derived-label range and Horn-flow arguments recover a
finite C222 refutation, hence a finite ZFC refutation through the retained
logical calibration.

For completeness the common-root congruence has cofinally many A. Since
N divides q and M=N*q^(x+1), gcd(q+1,M)=1. Thus gcd(2(q+1),M) is 1 or 2; in the
second case (q+1)^2+1 is even. The linear congruence is soluble and its
positive solution class is unbounded. One may choose A>=L and large
enough for h0>=0. Unlike some earlier constructions, A itself need not be
the abscissa in the lower-frame Pell equation; L is that abscissa and
sigma=A-L is free natural slack.

## Full witness order and constructive completeness

Start with an arbitrary finite C222 refutation. Use the retained padding,
pending-product and beta/CRT completeness construction to fix t>=16,
F=t!, x,y,B,R,K,N and all nine representatives in (0,N^2]. Fix q=N^K,
the six true powers, the exact binomial B and the ten true modular range
digits. The majorant argument just given shows all fifteen requested
indices are below the resulting W. Only now choose the lower Pell frame
L,Z, and then a sufficiently large compatible A in the root-congruence
class. No semantic datum chosen before A depends on A.

Set every principal pair to its actual canonical Pell pair at the
requested index. Supply the one inherited indexed certificate at W.
For m=15<=W-2,

    Y_W(A)-sum_i Y_ki(A)
       >= Y_W(A)-mY_(W-1)(A)
        > (2A-1-m)Y_(W-1)(A) > W.

Thus the aggregate slack u=Y_W(A)-W-1-sum Yi is nonnegative. In each
group Yki(A)=ki mod(A-1), so its squared-error sum divided by A-1 is a
nonnegative integer, supplying Q0 and Q1. The unchanged positive power
and modular-residue identities give nonnegative quotients, and ordinary
Euclidean digits give the remaining slacks. All arithmetic gates have
natural values. This constructs a zero of the new raw graph.

Every projected equation in this packet is obtained from that graph by
literal monic elimination. Each eliminated coordinate is restored by an
integer polynomial proved nonnegative through an exact rational
sum-of-squares plus nonnegative-monomial certificate. Reverse restoration
recovers all original rows; forward projection preserves them. Independent
finite verification checks every substitution and every collected quartic
coefficient. These syntax checks supplement the preceding unbounded
proof, rather than replace it.

## What changed and what did not

The initial 319-variable inspected source gave each of fifteen Pell
indices its own comparison pair under shared auxiliary infrastructure.
The new source keeps fifteen principal norms, adds one complete cap
certificate, and replaces all private comparisons by one aggregate
ordinate bound and two staged bounded-error congruences. All original
arithmetic/source semantics and all fixed C222 coefficients are retained.
There are no unspecified coefficient ports or calls to a universal
polynomial in the final equation. Each final object is literally a sum of
squares of the supplied quadratic integer polynomials.

## Measured effect of the dominant denominator

The new raw graph has343 coordinates and291 quadratic residuals, three
fewer of each than the retained staged product-modulus checkpoint. The
principal projection has239 variables and187 rows. The old242-variable
equation remains a valid separate checkpoint; this packet makes the
credited dominant-modulus composition concrete and reviewable.
