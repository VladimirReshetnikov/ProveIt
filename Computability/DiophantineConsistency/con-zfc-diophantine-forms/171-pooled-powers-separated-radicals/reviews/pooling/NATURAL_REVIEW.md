# Independent final natural-source review

**PASS, with the orientation recovery below explicitly included in the proof.**
Reviewed 25 October 2026 against `round21/natural/final`. Internal AI-assisted
ordinary mathematical/artifact review; not external peer review or a fresh
kernel-checked end-to-end derivation.

The independent `audit_natural.py` imports neither the producer nor its checker.
Both normal and optimized Python runs passed, with byte-identical JSON receipts
`NATURAL_NORMAL.json` and `NATURAL_OPTIMIZED.json`. They bind all six endpoint
objects by canonical SHA-256 and independently collect every quartic coefficient.

## 1. Exact stages and achieved base metrics

| Endpoint | Natural variables | Quadratic rows | Quartic monomials | Height |
|---|---:|---:|---:|---:|
| dimension203 | 203 | 155 | 9,126 | 9,592,304,964 |
| projected204 | 204 | 156 | 6,250 | 9,600,187,996 |
| projected205 | 205 | 157 | 6,263 | 9,592,984,476 |
| pooled202 | 202 | 154 | 10,104 | 9,592,414,944 |
| pooled203 | 203 | 155 | 7,242 | 9,600,187,996 |
| pooled204 | 204 | 156 | 7,255 | 9,592,981,476 |

These are the checked base objects before any later invertible row shears.
Every coordinate independently ranges over the nonnegative integers. All
residuals have degree at most two and each complete SOS has exact degree four.
The result is not a global optimality claim or a proof of Con(ZFC).

## 2. The three syntax-coordinate deletions preserve natural zero sets

Write `L=2*b+mul.36`, so L is natural, and use a new coordinate

    g=4L^2+26L+42=(2L+6)(2L+7).

This is a nonnegative quadratic wire; no unsupported perfect-square assertion
about g is made. The exact old-wire restorations are

    old mul.43  = g+8L+30,
    old mul.143 = g+4L+14,
    old mul.166 = 4g-4L-12,
    old mul.370 = old mul.366+2F.

In the projected branches the third restoration instead reads

    old add.171 = 8g+4b+2 mul.60+13.

The only negative coefficients occur in the mul.166 formula. On the defining
g row it is `16L^2+100L+156`, hence natural. Every other restored value is
manifestly natural. Conversely any old zero supplies the same g from its old
quadratic definition, so g is natural. Literal substitution makes the three
old quadratic definitions proportional to one retained g row; the two F
multiple rows become identical. Dropping exactly these three duplicate rows
and three redundant coordinates therefore preserves the natural zero set.

Every retained row, including the nonnegative local-source evaluation row,
its syntax-label expression, seed indices, bounds, and all endpoints is exactly
replayed. In particular none of the earlier cofinal sign choices for local
source factors has been altered by this common-wire recircuiting.

## 3. Lower frame strengthening is coefficient-only and valid

The old lower ordinate is `W*(z+1)`, with z natural. Replacing its old z by
`2*z_new+1` makes that ordinate `2W*(z_new+1)`, strictly positive. The retained
second product and norm give a lower canonical Pell pair at base W+1.
The recurrence modulo 2W gives

    Y_j(W+1) = j mod 2W.

Thus its positive index is a multiple of 2W and at least 2W. Since the actual
principal A is the lower abscissa plus a natural slack,

    A >= X_(2W)(W+1) >= (W+1)^(2W) > 4W^(2W),

for W>=2. The strict inequality follows from `(1+1/W)^W>2` for integer W>1.
The literal frame has far more than the required constant margin.

For completeness choose any canonical lower index divisible by 2W, for example
2W itself. Its positive ordinate is divisible by 2W, supplying natural z_new.
Only afterward choose A in the unchanged common-root congruence class above
this lower bound. The free natural A slack still permits arbitrary enlargement.
No semantic indices, CRT representatives, denominators, or earlier choices change.

## 4. The new three-coordinate pool and an essential orientation distinction

The three denominator requests have the common positive radix q and requested
indices `t`, `c=y+1`, `x`. Their proposed outputs m_i are the already contracted
natural affine remainder sums plus one, hence at least one. Let the stored
consecutive Pell coordinates be `(Y_i,Z_i)`. Introduce natural U,M,K with

    U = sum Y_i^2,
    K = 2 sum Y_i(m_i+Z_i) + (2A-q)M - qU,
    sum (m_i+Z_i)^2 + M - qK = 0.

The complete formal identity, without any Pell hypothesis, is

    sum (m_i+Z_i-qY_i)^2 = (2Aq-q^2-1)M.             (1)

**The removed c-request was the only direct output incidence orienting its
consecutive Pell pair. Therefore it is not legitimate to assume in advance
that Z_c is Y_(c-1).** This potential gap is repaired below; no equation or
extra coordinate is needed.

The t pair still has its first exact-power incidence, and the x pair retains
the N and radix incidences. The audit authenticates their literal rows. Their
nonnegative right sides, natural modulus/quotient coordinates, and base below
A give `Z_i<=base*Y_i<AY_i`, and exclude Y_i=0. Thus their principal abscissae
`X_i=AY_i-Z_i` are positive.

For the c pair, define the same integral X=AY-Z but initially allow either
sign. Its consecutive norm yields `X^2-(A^2-1)Y^2=1`. Classification using
`|X|` gives `Y=Y_j(A)` for some j>=0. The unchanged merged semantic-anchor
proof uses only these ordinates, not the abscissa signs: its error-square bound
first gives j<J<W and then reduces modulo A-1 to force every j to its requested
positive index. This also excludes the exceptional Y=0 pair. Consequently

    X_c = epsilon X_c(A), Y_c=Y_c(A), epsilon in {+1,-1}.

All other seed orientation incidences are unchanged, and the anchor itself
still has its ordinary natural principal and private coordinates.

## 5. Recover the positive radix without using the removed requests

The first retained power modulus rules out its base `n=F^2-1` being zero,
so F>=2 and n>=3. Natural endpoints give x>=F+1>=3. The frame and semantic
anchor now recover the first retained exact power `V=n^t` without any pooled
denominator meaning. The cofinal row gives y+1=V. The retained floor rows
`V=BF+r`, `B=r+s+1` imply `V<B(F+1)` and `V>F(F+1)`, hence B>F>=2.
The remaining singleton requests then give `N=B^x` and `q=(N*S_base)^x`.
The natural representative scale is positive, so q>=2. Every step precedes
interpretation of (1). This is a valid reordering of the retained bootstrap,
not an appeal to a removed quotient.

## 6. Inverse clearing with the actual additive frame

Put `T=2Aq-q^2-1`. The frame gives q<W, and its strengthened lower bound
implies T>A>0. Modulo T the Pell substitution has norm one and sends the
positive principal expression to q^k. Its conjugate is the inverse. More
explicitly,

    X_k+(q-A)Y_k = q^k mod T,
    X_k+(A-q)Y_k = q^(-k) mod T,

because their product is one modulo T and gcd(q,T)=1. Therefore

    qY_k-Z_k = q^k        if X=+X_k,
    qY_k-Z_k = -q^(-k)    if X=-X_k.

Multiply the residuals in (1) by q^c, with c=y+1. Their ordinary representatives
are

    d_t = m_t q^c - q^(c+t),
    d_x = m_x q^c - q^(c+x),
    d_c = m_c q^c - q^(2c)        when epsilon=+1,
          m_c q^c + 1            when epsilon=-1.

Thus T divides the nonnegative integer `E=d_t^2+d_x^2+d_c^2`.

The independent checker authenticates the stronger *combined-index* frame
bounds, not merely each individual atom bound:

    W >= c+t+1,   W >= c+x+1,   W >= 2c+1,   W >= c+2.

In the dense branch they are coefficientwise consequences of the literal
positive affine W. In the projected branches W contains a positive partial
sum and the first output via its floor expression; substituting the checked
partial-sum row and adding the retained cofinal floor row recovers the same
bounds. The receipts record every polynomial difference and row multiplier.

Since m_i,q<W, each displayed d_i has absolute value at most `2W^(W-1)`.
All exponents are nonnegative and at most W-1; also m_i q^c<=W^(c+1)<=W^(W-1).
Hence

    0 <= E <= 12W^(2W-2) <= 3W^(2W) < A < T,

where W>=2. Thus E=0. The negative c branch is impossible because
`m_c q^c+1>0`. The positive branch and the other two zero errors give exactly
`m_t=q^t`, `m_c=q^c`, `m_x=q^x`, and the missing predecessor orientation.

This sum-of-indices estimate is why the existing 2W strengthening suffices;
a rough maximum-index estimate would unnecessarily suggest a stronger frame.

## 7. Restore the deleted natural moduli and quotients

Restore T by its positive formula. For every now canonical predecessor pair
put `f_k=qY_k-Y_(k-1)`. Recurrence gives

    f_1=q,  f_k-q f_(k-1)=T Y_(k-1),
    f_k-q^k = T sum_(j=1)^(k-1) q^(k-1-j)Y_j.

Thus every old exact-power quotient `(f_k-m_k)/T` is a natural integer, not
merely an unrestricted integer. Restore the old lower parameter by
`z_old=2z_new+1`, also natural. All the deleted parent rows now hold and all
unmodified rows already held. Composing the syntax restorations from Section 2
therefore gives a natural zero of the full round20 parent.

Conversely start with the inherited canonical finite-refutation witnesses,
choose the strengthened frame as above, and retain all genuine powers. Their
errors e_i=m_i+Z_i-qY_i are divisible by T. Set

    U=sum Y_i^2,
    M=sum e_i^2/T = T sum(e_i/T)^2,
    K=2sum Y_i(m_i+Z_i)+(2A-q)M-qU.

U,M,K are integral by construction. U,M are natural and the identity
`qK=sum(m_i+Z_i)^2+M` proves K is natural. All three new rows hold. The previous
cofinal choices of CRT representatives, local-factor signs, semantic anchor,
carry margins, and private Pell witnesses remain in their original acyclic
order. The new U,M,K occur in no semantic frame or earlier choice.

## 8. Finite verification coverage and limits

The independent checker verifies, on all three branches:

- canonical source/output hash bindings;
- every syntax restoration, its natural sign, and all shared/duplicate rows;
- all old exact-power and modulus rows and exact deletion coverage;
- every retained and new polynomial row, label, and coordinate identity;
- the formal aggregate squared-error identity;
- the literal lower product, lower norm and parameter substitution;
- all base/output/index and combined-index frame bounds;
- all three consecutive norm/product pairs and retained t/x orientation rows;
- independent full SOS collection, exact metrics, degree and coordinate liveness;
- rejection of a deliberately changed aggregate coefficient even after its
  target hash is refreshed.

These finite receipts verify algebra, not the unbounded Pell classification or
C222/ZF/ZFC calibration. Those are explicit inherited ordinary proof contracts.
Within this boundary, the orientation issue is resolved, not silently assumed.
Later row-basis shears have their own exact replay and cannot change these
natural zero sets when they are invertible residual-row operations.
