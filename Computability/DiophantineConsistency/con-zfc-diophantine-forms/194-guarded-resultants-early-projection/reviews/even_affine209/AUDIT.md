# Independent audit of the even-affine 209-integer candidate

## Current conclusion

**The new ordinary mathematical delta and the exact emitted polynomial pass.**
The conclusion is relative to the explicitly inherited source210/source173
signed-Pell, factorial-free CRT, shell-C222, and ZF/ZFC calibration. It is not
a new end-to-end proof-assistant compilation or an assertion of consistency.

The independent exact audit, importing no producer code, gives:

| Quantity | Verified value |
|---|---:|
| Unrestricted integer variables | 209 |
| Quadratic residuals | 149 |
| Collected degree | 4 |
| Collected nonzero monomials | 5,486 |
| Coefficient height | 17,592,186,044,416 = 2^44 |
| Residual coefficient height | 4,194,304 = 2^22 |
| Residual terms | 1,004 |

Equation SHA-256:
`216bbdb35cf8b8fcc1f64acd45cf9b57cc1c2d2004a561e6ec8822de960b8cd5`.
Expansion SHA-256:
`71d88b558af92c97906a6149b002c85630b841fbe7f1abb1cb933a60c8327ee6`.

Normal and optimized Python both pass the independent full-coefficient
checker and the advertised `verify.py --parent` release command. The latter
checks all 149 plain and 149 TeX rows, all 149 retained affine inverse
identities, twelve actual-data corruption controls, and six byte-identical
JSON outputs rebuilt from a newly relocated package. Its complete original
source210 replay verifies 352 manifest entries and freshly rebuilds 37
coefficient files byte-identically; the nested source173 replay verifies
196 manifest entries and 26 reconstruction stages. Separately, all six
independent auditor mutations are rejected normally and under `-O`.
The receipts are stored beside this note.

## 1. Exactly what changed, including the inherited projection boundary

The authenticated immediate source is the incoming principal210 equation,
SHA-256 `20a2108353a3756ed7d1ddfdc71695131dcf0b6d94039988d9565ac48e6e1f0a`.
Its complete original ZIP is retained byte-for-byte, SHA-256
`33fecaaa728d5f38608b8b0930c09b08dbe9a01e03f6269f092ec6142d72a0ee`.
The source file in the new package agrees exactly with that archive member.

In its actual optimized chart, coordinate 0 is physical t. Coordinate 178
is the old private root and occurs only in row 125,

    t − 16 − 4 h_old² = 0.

The new construction substitutes t=4h+2 in every other row and deletes
only that row and root. The independent auditor reconstructs every final
row directly from the authenticated incoming equation. Exactly five
retained old rows change: 0, 124, 136, 147, and 149. Every coefficient of
every other row is retained, apart from mandatory index renumbering.
All rows remain quadratic; all 209 coordinates occur in the polynomial.

Privacy at the final stage alone would not suffice if an earlier projection
had used the old horizon to derive some retained relation. I checked that
additional boundary explicitly. At every stage the root remains private to
its original unchanged horizon row:

| Incoming stage | Root coordinate | Horizon row |
|---|---:|---:|
| anchor219 | 190 | 136 |
| growth217 | 185 | 132 |
| source216 | 184 | 131 |
| projection211 | 179 | 126 |
| projection210 | 178 | 125 |
| principal210 | 178 | 125 |

All five common-Hessian directions and their restoration formulas avoid
both t and the root. None deletes the horizon row. The subsequent affine
consequence uses only rows 5 and 18 and does not use the horizon or root.
All 79 final operations avoid the horizon row/root, and none changes
coordinate 0. Therefore the semantic horizon relaxation commutes with the
inherited arithmetic charts; their inverse identities have not silently
lost a required hypothesis.

The change is **not** a bijection between old and new zeros: old t is 0
modulo 4 and new t is 2 modulo 4. The affine inverse (t−2)/4 applies to
retained physical tuples in the new congruence class, not to arbitrary old
parent zeros. Soundness and completeness require the following new proof.

## 2. The frame is still strong before any arithmetic signs

Write delta=2^19. The retained standalone rows are

    Z=tF,
    X²−16Z²−8ZF=1,
    F=delta t(2u+1).

The new t=4h+2 is neither 0 nor −1, and |t|≥2. Thus the divisibility row
alone, without classifying a Pell equation at a possibly negative center,
implies F is nonzero and even and |F|≥delta|t|≥2^20.

I independently reconstructed the entire actual square frame in the
optimized incoming chart. It is W=2+sum of 34 actual atom squares,
including F itself, t, t+1, F+t, the radix 2(C+F+1), and all 45 ports of
the fifteen retained exact-power requests. Substituting 4h+2 preserves
this literal identity. Hence W≥2+F²>258 before recovering the signs of
t, F, y, x, C, or the radix.

The unchanged inherited signed C-anchor theorem therefore applies with
all its numerical hypotheses. It excludes C=0 and identifies the absolute
anchor index without assuming C positive. The cap bounds every other
classified index, and the small nonnegative orientation residue identifies
every principal pair canonically at its signed nominal index. This covers
negative shared Pell center A and negative requested indices, exactly as
in the inherited theorem. No use of standalone positive growth is needed.

## 3. Signed bootstrap, including all previously dangerous branches

The retained beta row is y=F(2v+1), so |y|≥|F|≥2^20. The representative
C is explicitly even. Therefore C+F+1 is odd and the affine radix base
D=2(C+F+1) is nonzero and nonunit for every initial signed tuple.
Its now-oriented power request gives x≥0 and q=D^x.

If x=0, the terminal endpoint

    x=1+[1+(t+1)y]u_t

makes 1+(t+1)y divide −1. But t+1≠0 and

    |1+(t+1)y| ≥ |t+1||y|−1 ≥ |y|−1 > 1.

This contradiction does not assume t positive. In particular it excludes
the negative-horizon branch that invalidated the earlier odd-affine
proposal. Thus x≥1 and |q|≥2. Only now interpret the q pool. Its actual
t index gives t≥0; t≡2 modulo 4 then gives t≥2. Its y+1 index gives
y≥−1, and the nonzero multiple condition strengthens this to y≥|F|>0.

The standalone Pell center 4t+1 is now positive and odd, so the growth
argument in Section 4 is legitimate. If x=1, the initial endpoint gives
−F=(y+1)u_0, impossible since 0<|F|≤y<y+1. Thus x≥2. The terminal
endpoint now has a positive multiplier, gives u_t≥1, and yields
x≥2+(t+1)y. In particular |q+1|≥3. The q+1 pool is therefore nonunit;
its F+t index gives F+t≥0. The bound |F|>t excludes F<0, so F>0.
The same pool gives C≥0, and prior anchor nondegeneracy gives C>0.
Thus D,q are positive, y≥F, and the initial endpoint yields u_0≥0 and
x≥F+1. Every sign is obtained before it is used.

Zero t, t=−1, x=0, x=1, negative F, negative y, C=0, and unit/zero radix
escapes have all been handled explicitly. The smallest surviving t is 2.

## 4. Growth, syntax, selector radius and local precision at t=2

For a positive odd center a, Pell classification and elementary recurrences
give Y_n(a)≡n modulo a−1, v2(Y_n(a))=v2(n), and
Y_n(a)≥(2a−1)^(n−1) for positive n. Here F≠0, so write
|F|=Y_n(4t+1). Since delta is divisible by four, 4t divides F; hence
4t divides n. The odd multiplier gives v2(n)=19+v2(t), so
n/(4t) has exact valuation 17 and n≥delta t.

At natural arguments ≤M, every actual shell constructor is bounded by
E(M,M), and E(M,M)+1=8M²+14M+8≤8(M+1)². For t≥2 every parameter leaf
and each constant 0 or 1 has value-plus-one at most t. The unchanged,
authenticated maximum depth 19 therefore gives every label strictly below

    L=8^(delta−1)t^delta.

Consequently

    |F|≥(8t+1)^(delta t−1)≥(8t)^(delta t−1)≥L^t,

the last ratio being exactly 8^(t−1)/t≥1. After sign recovery this is the
required positive label-product separation bound F≥L^t. The inherited sharp
separation theorem permits equality, uses positive coefficient differences
strictly smaller than F, and treats zero labels as units. No old t≥16
constructor threshold is being reused.

The selector estimate is separately repaired: t≥2, 8t+1≥17 and
delta t−1≥t imply

    F≥17^t>16^(t−1)≥lcm(1,...,t)².

This avoids the false assertion t^t≥16^t at small t. Moreover at the
minimum t=2 one has F≥17^(2^20−1)>17^8>2^32. With y≥F>t and
x≥2+(t+1)y, one has R0=2+t+x+y+F<2x: the needed strict inequality
follows from (t−1)F>t. The inherited local-degree bound 2^23 is then
dominated by x via the usual dyadic estimate, starting at exponent 32.
Thus every local congruence still becomes an exact local row.

## 5. Remaining arithmetic extraction

The unchanged cap now bounds every positive binomial upper argument by C,
and every lower digit cutoff is at most x. Since D=2(C+F+1)>2C,
q=D^x>(2C)^x. Therefore every relevant coefficient is at most C^x<q/2^x,
and each true low tail is less than its denominator divided by 32.
The retained centered remainder norm and congruence force exact agreement.

The selector row B eta=C+F+1 has nonzero right side, so eta≠0 and
|B|≤D/2<q/2. Combined with the first digit congruence and the true
coefficient bound q/32, it gives B=binom(F+t,t)>0. Its retained power
gives N=B^x, and B|D gives N|q. These are precisely the size/divisibility
interfaces used by the nine local ranges and ten normalized digits.

The repaired selector radius covers every row and every prime of B.
The y=F boundary is excluded only after local recovery by positive-weight
state propagation. Positive accumulators can then be cancelled. Sharp
label separation and the inherited finite Horn-closure argument handle
cycles and yield a finite shell-C222 refutation. The unchanged shell-to-
original-C222 recoding and the identified C222/ZF/ZFC endpoints complete
soundness. This audit does not replace that credited logical calibration
with a numerical experiment or claim a newly compiled kernel proof.

## 6. Cofinal completeness and the changed dyadic parity target

Choose a≥11 sufficiently large for the proof and its local parameters, and
set t=2^(2a)+2 and h=2^(2a−2). These horizons are cofinal in the allowed
class. They have v2(t)=1 and bit 20 equal to zero; their only nonzero bits
are 1 and 2a≥22.

Put n0=delta t, y0=Y_n0(4t+1), a0=X_n0(4t+1). The Pell congruence gives
t|y0, and its valuation is exactly 20. Thus b0=y0/(delta t) is an odd
integer. Since n0 is even and the base is odd, a0≡1 modulo 4.

For any a0≡1 modulo 4 the inherited normalized ordinate map s↦Y_s(a0)
permutes classes modulo each 2^r. Its elementary proof is valid here:
v2(Y_(2^r))=r; the norm and X_(2^r)≡1 modulo 4 imply
X_(2^r)≡1 modulo 2^(2r+2); addition then gives
Y_(s+2^r)−Y_s≡2^r modulo 2^(r+1). Each index class therefore supplies
both next-bit lifts, and the same recurrence gives periodicity. This gives
arbitrarily large positive odd indices for any selected odd output class.

Choose b>22 with 2^b>t. The odd coefficient (t/2)b0 is invertible modulo
2^(b−20). Select positive odd s with

    (t/2)b0Y_s(a0)≡1 modulo 2^(b−20).

Set F=y0Y_s(a0)=Y_(n0s)(4t+1), X=X_(n0s)(4t+1), Z=tF, and
u=(F/(delta t)−1)/2. All witnesses are integers, F>0 can be arbitrarily
large, and all three standalone rows hold. Crucially

    F≡2^20 modulo 2^b.

Below bit b, F has only bit 20, absent from t; at or above b, t has no
bits. Their binary supports are disjoint, so addition is carry-free and
v2 binom(F+t,t)=s2(F)+s2(t)−s2(F+t)=0. Therefore B is odd. The old
bit-23 argument was not silently reused at the changed horizon.

Choose odd w arbitrarily large and divisible by every odd prime ≤t,
then y=Fw. Every prime ≤t divides y, so a common prime of 1+iy and
1+jy would divide j−i≤t and also y, a contradiction. The beta moduli
are pairwise coprime; full factorial divisibility is neither needed nor
claimed with fixed v2(F)=20. Choose w to dominate the finite pending states
and then choose a sufficiently large positive beta code x by CRT.

Only after x is fixed set N=B^x. Choose eight positive CRT representatives,
then choose C even and cofinally large in its prescribed class modulo odd
N², beyond all other nominal indices and representatives. The required
B|C+F+1 is preserved. Define D,q and true power outputs after C. Choose
the main square frame and all private Pell/cap witnesses last. Its even-C
completion, nonnegative cap slack, orientation quotient, and small genuine
remainders use exactly the source210 hypotheses now proved. This order is
acyclic and constructs a new zero from every finite refutation.

## 7. Exact verification and comparison boundary

`independent_audit.py` verifies the original archive and source byte pins,
the six-stage horizon privacy, all five retained-row edits, all 149 final
residuals, all 5,486 collected coefficients, the literal 34-atom square
frame and all 45 actual power ports, and every dimension/height/liveness
claim. It imports no producer helper and works with or without Python -O.

This endpoint is not a numerical domination claim. Against incoming210 it
saves one variable and one row but adds 204 terms and multiplies height by
16. Against sealed212 it saves three variables and two rows but adds 129
terms; its height is only four smaller. The much lower-height 215-variable
construction remains another tradeoff. No global minimum follows.

The earlier sealed212 files and all old/upstream sources are untouched.
All independent audit work is under `round23/review/even_affine209`.
