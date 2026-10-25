# Shift-free descending factorials with cofinal Pell anchors

## Scope and literal equation

All coordinates range independently over N={0,1,2,...}. The released equation
is P=sum_j R_j^2=0, with every R_j given literally in equation.json and
residuals.tex; expanded_polynomial.json records every collected integer
coefficient. No factorial, binomial, exponentiation, floor, Pell sequence, or
bounded quantifier is a primitive of P. The statements below explain the
finite arithmetic graph which is exported and exactly contracted into P.

Relative to the explicitly retained ordinary C222 numerical-calculus
calibration, P has a natural zero exactly when there is a finite syntactic ZFC
refutation. Thus ZFC proves that the no-natural-zero sentence is equivalent to
Con(ZFC). This does not prove consistency, give a new kernel-checked endpoint,
or assert global optimality. The new contribution combines the incoming
descending certificate with the Round17 cofinal anchor and strict x-budget,
and removes both artificially shifted factorial and carrier coordinates.
The removal uses semantic positivity rather than an invalid unrestricted
substitution F^2-1>=0.

## 1. The shift-free certificate and its sound bootstrap

Keep t=t0+12, and introduce *unshifted* natural coordinates F, n, B, r, s.
The literal rows are

    n+1=F^2,       V=BF+r,       B=r+s+1.                 (D)

The graph requests V=n^t. Its exact-power modulus T_n has a natural coordinate
and row T_n+n^2+1=2An. At n=0 this is impossible. This exclusion is purely
polynomial, before interpreting powers, factorials, or binomials. Since
n+1=F^2, it follows that F>=2 and n=F^2-1>=3.

The retained shared Pell frame and one-row semantic anchor first authenticate
all indices, and then prove every exact power. Their hypotheses do not require
knowing F=t!: all intended exponents are positive directly from t>=12 and
x>=F+1>=3, every frame atom is natural, the power-modulus rows exclude zero
bases, and the lower Pell scale gives A>=(W+1)^W. The standard chronology is
spelled out in the retained ONE_ROW_SEMANTIC_ANCHOR_PROOF.md. Here the exact
power list is

    V=n^t, N=B^x, q=(N S)^x, D_t=q^t, D_y=q^(y+1), D_x=q^x,
    S=1+C+Aa+Ab+Ac+Ad+AS+ASp+Au+Av.                       (P)

There are thirteen nonanchor seeds, eleven modular requests, and W is their
frame sum plus fifteen. The anchor J is the same derived syntax-label sum;
its complete three-norm certificate is not replaced by a free Pell norm.

Before the first binomial decoding, the raw endpoints already give y>=F+1>=3 and x>=F+1>=3. Thus u_t>=1 in x=1+(1+(t+1)y)u_t, and x>=2+(t+1)y>max(t+1,y+1). Therefore M=N*q^x has the required denominator divisibility before factorial semantics.

After (P), (D) gives B>=1 and V<B(F+1). For F>=2,

    n=F^2-1>=(F+1),
    V=n^t>=n^2>F(F+1),

so B>F. In particular B>=3 and x>=F+1>=3. Therefore

    V<B(F+1)<=B^2<=N<=q.                                 (B)

There is no circular use of the factorial or of the binomial output here.
For every 0<=j<=t, binom(n,j)<=n^j<=n^t=V, taking binom(n,j)=0 if j>n.
Thus (B) establishes the carry bound for the first exact binomial before it
is decoded. The retained modular digit graph now yields B=binom(n,t).
Because B>=1, n>=t. The floor rows in (D) are precisely

    F=floor(n^t/binom(n,t)).

## 2. Descending factorial identity

For integers t>=3, F>=2, n=F^2-1>=t, write T=t! and U=t(t-1)/2. Then

    H=n^t/binom(n,t)=T*product_{j=0}^{t-1}(1-j/n)^(-1)>=T.

If F=floor(H), then F>=T. The inequality T-1>U holds at t=3 and persists
by induction: (t+1)!-1 >= (t+1)(U+2)-1 > U+t. Consequently
n>=T^2-1=(T+1)(T-1)>(T+1)U. The product inequality
product(1-a_j)>=1-sum a_j for 0<=a_j<=1 gives

    T<=H<=T*n/(n-U)=T+T*U/(n-U)<T+1.

Therefore F=T. Conversely, at F=T these same estimates prove floor(H)=T.
All steps apply to the positive binomial already recovered, rather than
assuming its positivity as a hidden side condition.

## 3. Descending reciprocal CRT and quotient orientation

Now F=t!, and define d_i=F^2/i-1 for 1<=i<=t. Each i divides F, so d_i is
an integer congruent to -1 modulo F. Thus every prime divisor of d_i is >t.
If a prime p divided d_i and d_j with i!=j, it would divide
id_i-jd_j=j-i, impossible because p>t. These moduli are pairwise coprime,
and their product is B=binom(F^2-1,t).

The index row is C+1=F^2+Bq_C, equivalently C=n+Bq_C. Modulo d_i it gives
C=i-1. This differs in sign from the rising-factorial predecessor and is
explicitly implemented in build_strict_budget.py. It is not silently inherited.
For completeness B>n: since F>=6 and 3<=t<=n-2, binom(n,t)>=binom(n,2)>n.
Every positive representative congruent to n modulo B is therefore >=n,
so the index quotient q_C is natural.

## 4. Bounds, modular decoding, and local soundness

All endpoint rows, source arithmetic, range indices and label polynomials are
identical to Round17. In particular y>=F+1 and
x=1+(1+(t+1)y)u_t>=2+(t+1)y. Hence R=2+t+x+y+F<2x and x>2^32 for t>=12.
The retained literal majorant has E=2^23; its checked induction gives
R^E<(2x)^E<2^x. The label majorant has ell=2^22 and ell(t+1)<F<x.
The strict beta quotient ranges are u,v<x, justified canonically by their
positive denominators >=2; no upper-bound assumption on x is needed.

Every independent positive representative is <S, so binom(a,j)<S^x<q
for j<=x. The derived label obeys J<=S^ell, and therefore every needed
coefficient binom(J,j), j<=t+1, is <S^x<q. Together with Section 1 this
justifies all eleven modular requests. The root modulus is M=N*D_x.
Since x>t+1 and x>y+1, it is divisible by qD_t for the exact binomial and
by N times every range denominator. The common-root row

    2A(q+1)=(q+1)^2+1+M h

therefore supplies the unchanged Pell congruences for all digit requests.

For a row i-1 choose p|d_i and m=v_p(d_i). The one-direction prime-power
range lemma p^e|binom(a,k) => a mod p^e in [0,k-1], together with the index
congruence, recovers C=i-1 modulo p^(xm). All local coordinates are decoded
in their prescribed ranges. The nonnegative local source polynomial is
strictly <2^x<=p^(xm); its zero residue forces its actual value to be zero.
The derived-label range yields the local label bound. The unchanged beta
consistency and Horn-flow argument gives a finite C222 refutation.
No converse of the prime-power range lemma is assumed.

## 5. Constructive completeness and padding

Start with a finite syntactic refutation. Use the retained C222 calibration,
expand its witness to a proof tree, and pad the horizon to t>=12 beyond every
required local parameter and label. The inherited beta construction supplies
x,y. Put F=t!, n=F^2-1, B=product_i d_i, N=B^x. Section 2 supplies nonnegative
r,s in (D); these are the ordinary Euclidean remainder and complementary slack.

Choose the nine positive independent CRT representatives modulo d_i^(2x),
initially in (0,N^2]. Replace only Aa by Aa+N^2. All local polynomial
congruences to precision d_i^(2x) are preserved. In each range, the falling
factorial numerator has a term of valuation at least 2xm, while division by
k! loses at most k-1<=x-1. Thus the required binomial remains divisible by
p^(xm). This supplies all range divisibilities, including the polynomial J.
Section 3 supplies the correctly oriented natural index quotient.

The remaining nominal indices t,y+1,x,n are <=x^2+x<2^x<=N; all independent
representatives are <=2N^2. Thus the maximum nonanchor index k is <=2N^2.
The unchanged Cantor label gives

    J>=2(Aa+N^2)^2>2N^4>4N^2>=2k.

This is exactly the completeness hypothesis of the one-row anchor; no extra
inequality or witness is required. Now choose S and q, followed by denominators,
W and its lower Pell witness. Since N|q and gcd(q+1,M)=1,
gcd(2(q+1),M) is 1 or 2, and in the latter case the root row has even right
side. Choose A arbitrarily large in its soluble congruence class. The scale
slack and root quotient can be natural. Canonical Pell pairs, fresh private
anchor witnesses, the one-row square-error quotient and Euclidean modular
digit witnesses then complete the graph. The order of choices is acyclic.

## 6. Polynomial export, contraction, and inherited boundary

Every defining gate is a nonnegative addition/product/square or squared
difference. The new row n+1=F^2 is deliberately *not* marked as a definitional
gate with globally nonnegative restoration F^2-1. It is a retained polynomial
equality. Independent check_affine_export.py verifies the exact dependency
closure, every permitted nonnegative affine restoration, every exported row,
and all collected raw coefficients. check_natural.py independently replays
each monic contraction, with exact rational sums of affine squares plus
nonnegative monomials certifying restorations; it then independently expands
the full SOS. Hence both directions of natural existence are preserved.

The portable source keeps the exact numerical source JSON and arithmetic
compiler. proofs/ retains the ordinary cofinal anchor, Pell, CRT, factorial
carrier, source-range and calculus dependencies. proofs/inherited/calibration/ retains the
named C222/ZF/ZFC endpoint inputs. Their calibration is used, not re-proved
by finite coefficient checks. SOURCE_MAP.json binds retained inputs and
modifications. The ordinary argument here supplies the new unbounded steps;
finite tests are controls and cannot certify consistency.


## 7. Reversible row basis for the final balanced endpoint

The 229-variable precursor has 179 residuals, 6,596 terms and height
83,879,378. The final balanced endpoint applies the 42 listed elementary
integer row shears R_i <- R_i+k R_j with i!=j. Their inverses, in reverse
order with -k, recover every precursor row exactly. Hence the two residual
vectors have identical zero sets; sums of their squares have the same zeros
over N^229 even though the polynomial values differ. No coordinate is changed,
eliminated, or made signed. The resulting polynomial has 5,607 monomials and
height 65,892,965. The exact shear checker validates the expanded polynomial
and all refreshed embedded metrics, rejecting six deliberate corruptions.
