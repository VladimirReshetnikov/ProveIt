# Removing the horizon square guard: a separate coefficient tradeoff

This extension starts from the source in PROOF.md. It changes two further
raw rows and retains all eighteen power requests, five base moduli,
fourteen-pair orientation pool, common remainders and C222 calculus.

## Literal change and coordinate offset

The raw coordinate named t0 represents the actual horizon t=t0+16.
Delete t0-h0^2=0, where h0 is the private cofinal.horizon_root coordinate.
It occurs nowhere else. Replace the growth-base row d=2(t+1) by

    d=2^26(2t+1).

In RAW coordinates the exact residual is d-2^27*t0-33*2^26. After the
inherited translation old t0=new t0-16, it is d-2^27*t-2^26. Using the
latter expression in the raw source would incorrectly omit the offset.
The existing index-t power request still produces F; no power slot is added.
Retain q=4z+1 and y=F(2v+1). The exact changes are recorded in
horizon_free/source_changes.json and horizon_free/raw_source.json.
The removed horizon row is temporarily zero in the raw data to preserve
lineage indices; it and its unused root are absent from the final equations.

## Recovering the positive horizon

For every integer t, 2t+1 is nonzero and |d|>=2^26. Because d is an
actual square-frame atom, W>=2+d^2>=2+2^52>258. This restores the
numerical frame bound without presuming t>=16. The unchanged signed
anchor and orientation argument consequently gives canonical Pell
polynomials at the actual signed t. It does not require a positive
nominal index or monotonicity of a signed semantic label.

Apply the signed-base power lemma at |d|>=2: it gives t>=0 and F=d^t.
If t=0 then F=1 and y=2v+1 is odd. The two endpoints read

    x=2+(y+1)u0,        x=1+(y+1)ut.

They imply (y+1)(ut-u0)=1, impossible since y+1 is even. This also
covers y=-1. Hence t>=1, and

    F=[2^26(2t+1)]^t >=3*2^26>7,
    F>(t+1)^t,        F>t!,        v2(F)=26t>v2(t!).

The q=1 exclusion and subsequent signed-radix bootstrap in PROOF.md
now apply unchanged with t>=1: |y|>=F excludes x=0 in the last endpoint;
|q|>=3 follows; all upper representatives are nonnegative; x>=t+1;
y+1>=0 implies y>=F; and the endpoints then imply

    x>=2+(t+1)y>=2+(t+1)F>=2+6*2^26>2^28.

The signed binomial proof remains valid for t>=1. Its coefficient bound
max_(j<=t) binom(F^2+t,j)<=2^[t(F-1)] has ratio to |q| at most
2^(-F-t-2), much less than 1/32. Thus centered uniqueness gives
B=binom(F^2+t,t)>0 and then q>0, with all denominators nonzero.
At t=1, B=F^2+1 and the encoded index C may be zero; this is harmless
because the changed H is 2+sum of nine actual representatives. The proof
uses H>=2 and H>=n+2 for every representative n, without C>=1.

## The two required large-budget repairs

For the derived-label exponent ell=2^22, F>=3*2^26>ell gives
x>ell(t+1), exactly the required coefficient margin. The complete
local polynomial uses the inherited majorant exponent E=2^23 and
R=2+t+x+y+F. Its suitable bound is R<3x for all t>=1. At t=1 one
may only assert R<=2x+1, so the old convenient R<2x estimate must
not be reused without a boundary argument.

For x>=2^28, choose k>=28 with 2^k<=x<2^(k+1). Then

    log2(3x)<k+3<=2^(k-23).

The last inequality holds at k=28 because 31<=32 and persists by
induction. Hence E log2(3x)<2^k<=x, proving R^E<(3x)^E<2^x.
This gives the required exact-zero conclusion for each CRT-selected row.

The generalized binomial CRT theorem needs only t>=1 and
F^2>=lcm(1,...,t)^2, which follows from F>t!. The label multiplicity
argument needs only t>=1 and F>(t+1)^t. The y=F boundary is excluded
by the same zero-accumulator propagation argument, also valid for t=1.
The single-conclusion flow and C222/ZFC refutation calibration are unchanged.

## Constructive completeness

Given a finite refutation, choose a sufficiently large integer t; one may
still choose t=16+h^2 when constructing a witness. Put
F=[2^26(2t+1)]^t. A sufficiently large positive odd multiple w of
the odd part of t! gives y=Fw, an even multiple of t! larger than all
pending accumulators. This works because v2(F)=26t>v2(t!).
The beta moduli are odd and pairwise coprime, so x can be chosen even
and arbitrarily large. The binomial B is odd, since
v2(F^2)>floor(log2t). The inherited CRT parity choices make H odd
and the semantic anchor even and dominant. Then q=(BH)^x is an odd
square, hence 1 modulo 4. All canonical Pell and remainder witnesses
exist as before, and the common norm gap has its ternary representation.
No witness is needed for the deleted horizon square.

## Exact lineage and numerical cost

The builder build_horizon_free.py changes the raw source and replays the
same Horn factorization. It keeps the same 202 monic pivot locations but
rederives EVERY restoration from the changed current row. Every pivot
remains integral, and all rows remain quadratic. The coordinate
translations, six shears and fixed row operations are replayed; the 3/4
affine restorations are likewise rederived. Finally the q and multiplier
affine pivots, zero horizon row and private root are removed with explicit
coordinate maps. Old growth-base restoration formulas are not reused.

Before the independent D contraction the exact endpoints are:

|Profile|Integer variables|Quadratic rows|Collected terms|Coefficient height|
|---|---:|---:|---:|---:|
|Balanced|239|175|5059|1298074204962300530359575779475468|
|Dense|238|174|12804|1298074204962300530359575779475468|

Their degree is4 and maximum residual coefficient 18014398509481987.
The separate D contraction saves one variable and one row, producing
238/237 variables respectively, with its own inverse-map certificate.
The conservative low-height 239/238-variable equations are unchanged.
This is a coefficient-versus-dimension tradeoff, not domination in all metrics.

The horizon builder reuses verify_affine.py as an algebra engine, so its
own replay is not independent verification of this extension. A separate
checker, sources/direct_agent/verify_horizon_lineage.py, uses a different
sparse ring engine and has independently checked all four raw changes,
Horn changes, 202 restorations, translations, shears, row operations,
projections, zero-row/root deletion and every collected coefficient in
normal and optimized Python. Its HORIZON_LINEAGE_VERIFICATION receipts
record the exact scope. The source source_changes.json is a mutation
record, not an external signature.

The unbounded proof composes with the same named inherited Pell, CRT,
C222/ZF and ZF/ZFC interfaces. This is neither a new end-to-end Lean/Rocq
formalization nor a proof of consistency or a global simplicity minimum.
