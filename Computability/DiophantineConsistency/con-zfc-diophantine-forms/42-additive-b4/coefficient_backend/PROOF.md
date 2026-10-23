# Nonzero label codes and a shorter synchronization layout

## Result and dependency boundary

This is a new, complete four-port instance of the inherited blank-K215
native-window/Pell compiler. Its exact parameters are

    b = 107, L = 6385, d = bL = 683195,
    rho = 2^107, B = rho^6385 = 2^683195.

The four materialized coefficients occupy 342,269 raw bytes in total;
the largest coefficient has 688,546 bits. The previous smallest base at
the reviewed commit was B=2^1012115 (package 36), with 506,664 raw bytes
and a largest coefficient of 1,016,946 bits. These are reductions of
32.50% in the base exponent, 32.45% in total raw bytes, and 32.29% in the
largest coefficient's bit length. Arithmetic skeletons need all four new
ports together. Their numbers of variables, equations, degrees and gates
are unchanged by this coefficient substitution.

The two new ideas are: (1) occupancy is encoded by nonzeroness of a whole
edge word, so a dedicated occupancy bit on each port is unnecessary; (2)
the lower tested synchronization anchor can be placed inside the existing
copy/dummy span, with exact support isolation replacing interval spacing.
The first saves four payload bits, and the second lowers the cell length
from 8801 to 6385.

This is an ordinary mathematical compiler-adapter proof, formalizable in
ZFC, relative to the repository's inherited arithmetic, marked Wang
language, helical padding and K215 finite-refutation theorems. Finite
certificates do not replace these universal results. We assert no new
end-to-end proof-assistant certificate and no proof of consistency.
Source pin: `22e75dd6b87b1b199bb08c778d7cf075ae5aae08`.

## 1. A general nonzero-code occupancy lemma

Let a finite tile alphabet have horizontal edge set H and vertical edge
set V. Encode horizontal labels by an injective map into the nonzero
binary words of length l_H, and vertical labels by an injective map into
the nonzero binary words of length l_V. At every native cell a local
selector/copy clause permits exactly two cases:

* empty: every edge-copy word is zero;
* occupied: exactly one tile is selected and its four copy words are its
  encoded labels.

Suppose corresponding copy words match at spatial and temporal neighbors,
and a Start selector is present. Then every spatial neighbor of an
occupied cell is occupied: its matching word is the same nonzero word,
whereas an empty cell's word would be zero. Spatial step one visits the
entire cyclic word, so every cell is occupied. Injectivity now decodes
exactly the original matching equations. Conversely an original tile
word gives all four nonzero copy words and satisfies every bit comparison.

Thus a shared distinguished high bit is sufficient but not necessary.
No numerical ordering, special label zero, or prefix property is needed.
In particular the lemma remains valid when label zero is used by most
tiles: zero is mapped to the nonzero word 1.

## 2. Fixed language and complete coefficient recipe

Retain the inherited ordered 943 Wang tiles. The literal K215 transition
table, directed-signal tiles, reset/seam tiles, Start tile at selector 0,
and forbidden tile at selector 1 are unchanged. The tile-list SHA-256 is

    66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f.

For each slot encode its label x by x+1. Horizontal labels are at most 249,
and vertical labels at most 438. Consequently widths 8 and 9 suffice:

| Slot | Copy offset o_s | Width l_s | Payload field p_s |
|---|---:|---:|---:|
| West | 1023 | 8 | 0 |
| North | 1013 | 9 | 8 |
| East | 1003 | 8 | 17 |
| South | 983 | 9 | 25 |

Define E as the disjoint union of selectors 0,...,942, the 34 positions
o_s+j, dummy positions 1063,1064, and anchors 1022,1042,2107. Thus |E|=982.
For 0<=j<37 put w_j=2^(10+2j). For tile i with slot labels x_(i,s), set

    c_i = 1 + sum_(s,j) bit_j(x_(i,s)+1) w_(p_s+j)
            + w_34+w_35+w_36.

At a copy position o_s+j set c_(o_s+j)=w_(p_s+j). The three anchor
coefficients, in order 1022,1042,2107, are w_34,w_35,w_36. Set both dummy
coefficients to zero. Finally put

    mu = 1022 + sum_(j=0..36) w_j,
    Z = (2^105-1) sum_(e=6376..6383) rho^e
        + (2^30-1) rho^6384,
    DC = rho^30+rho^70+rho^20+rho^1085
         + sum_(e in E) c_e(rho^(3202-e)+rho^(4268-e)),
    DR = rho^50,
    MC = B-1-sum_(e in E, e != 1) rho^e-2rho^1063,
    MF_native = 4+mu(rho^3202+rho^4268)
                + sum_(j=0..8) rho^(1013+j)
                + sum_(j=0..7) rho^(1073+j)
                + rho^1042+rho^2107+Z.

The actual four integer coefficient ports are

    beta=B-1, K=DC+B DR, MC, MF_source=MF_native+B-1.

The final high-mask port is already shifted. Replacing it by MF_native,
or mixing this tuple with any previous tuple, changes the mathematical
instance. Every sum and exponent above is fixed finite integer arithmetic.

## 3. Exact clauses, comparisons and synchronization

### 3.1 Selector extraction precedes payload extraction

The low native mask permits Boolean digits on selectors, copies and
anchors, and the same inherited dummy digits. All dummy clause coefficients
are zero. Let n be the number of selected tiles. Initially 0<=n<=943, and
all nonconstant clause terms are divisible by 1024. Hence the lowest ten
bits of a clause sum are exactly n. Mask 1022 allows only n=0 or n=1.

Only after obtaining this fact do we inspect the radix-four payload
fields. Each is a selected tile bit plus its Boolean copy, or n plus an
anchor bit; the possible sums are 0,1,2. Testing its lowest bit allows
precisely 0 and 2. Empty cells therefore have all copies and all anchors
zero, and occupied cells have the tile's encoded words and all anchors one.
There is no unjustified assumption of carry-free payloads before extraction
of the selector count.

### 3.2 Full native-basis isolation

Every tested target has exactly these contributions:

| Target | DC current source | DR spatial source | Temporal source |
|---|---|---|---|
| 1013+j, 0<=j<9 | 983+j via shift 30 | none | 1013+j |
| 1073+j, 0<=j<8 | 1003+j via shift 70 | 1023+j via shift 50 | none |
| 1042 | 1022 via shift 20 | none | 1042 |
| 2107 | 1022 via shift 1085 | none | 2107 |

At each clause band T=3202,4268 the coefficient of rho^(T-e) in DC is
exactly c_e for every e in E, and e+50 != T. There are no hidden terms
from another bare shift or another reflected clause band. These are full
scalar coefficient identities, including dummy coordinates, and linearity
extends them to every allowed native assignment. The generator checks
19*982*3+2*982*2=59,902 exact equalities.

For clarity, the short source-to-anchor shift 20 is safe because the
relevant gaps in E isolate both target 1042 and all bit-comparison targets.
Its safety is an exact support fact, not an interval-separation assertion.

### 3.3 Clean bands and unique alignment

Let S=E\{2107}. Its largest element is 1064. The difference 1066 does not
occur in E-E: pairs inside S have smaller span, and 2107-1066=1041 is
absent. Because 4268-3202=1066 and L=6385>2*2107, this proves

    ((3202-E) mod L) intersection ((4268-E) mod L) is empty.

Consequently at least one clause band is clean for every binary rotation,
exactly as in the inherited synchronization proof. Apply its local clause
decoding first in the distinguished Start cell. Its selector 0 is already
forced to be one. Therefore its source anchor at 1022 equals one, and
both temporal tested anchors must be one. No global occupancy assumption
is needed for this step.

For a binary remainder 1,...,b-2 every rotated native digit is even.
For remainder b-1, only the single upper-dummy spill can be odd. Two
distinct tested anchors demand two odd digits, ruling out these cases.
For the remaining whole-radix rotation use 2107-1042=1065. This difference
occurs exactly once in E-E: again S has span only 1064, and the only pair
is (1042,2107). Since L>2*max(E), there is no extra circular alignment.
Thus

    ((1042-E) mod L) intersection ((2107-E) mod L) = {0}.

The temporal rotation is therefore a whole-cell rotation. All overlap
tests now compare two Boolean bits, so their parity tests imply equality.
The nonzero-code lemma propagates occupancy from Start and recovers the
unchanged marked Wang tiling.

Conversely any intended aligned tiling has exactly these copied bits and
anchors, so it satisfies every clause and overlap condition. Neither the
compressed label encoding nor the shorter geometry removes a tableau.

## 4. Carries, padding and the arithmetic interface

Retain the source's conservative pre-decoding mass bound

    M = (982+2)(2 sum_(e in E) c_e + 6).

Exact arithmetic gives bitlength(M)=104 and bitlength(4M+8)=106. Therefore
4M+8<rho=2^107 and 2mu+4<rho. The largest padded digit is 2^105-1, so
2(2^105-1)+4=2^106+2<rho. The source uniform no-carry estimate, including
nonaligned rotations, applies without alteration. The canonical strict
positive raw-slack estimate also applies.

All unshifted products remain inside a cell. In particular

    max(DC support)+max(E)=4268+2107=6375;
    max(DR support)+max(E)=50+2107=2157.

Every padding digit 6376,...,6384 is therefore zero on an aligned intended
field, including all safe dummy variations. Adding its tests cannot lose
completeness; these extra tests may be ignored in soundness. They all lie
below L=6385.

The unpadded high mask has population 2*46+9+8+2+1=112. Padding contributes
8*105+30=870 bits. Hence

    pc(MF_native)=982, pc(MC)=d-982,
    pc(MF_native)+pc(MC)=d.

The low congruences remain MC=2 mod4 and MF_native=4 mod8, and
0<MC,MF_native<B-1. They follow directly from the supports and are also
checked on the actual integers. As in the source, no assertion that these
two masks are mutually disjoint is needed: they constrain different objects.

The canonical origin test is unchanged. DC and DR have strictly positive
degree, so the unit native digit of the field comes only from the temporal
neighbor's selector 0. A canonical tableau has one Start and nonzero
temporal shift. It therefore satisfies the inherited low-origin mask tests.

## 5. Exact actual-rank controller

The new exponent is d=5*107*1277. Both 107 and 1277 are prime. Choose
lambda=135257, which is prime, and k=lambda-1=135256. Exact certificates
are:

| Modulus | 5 | 107 | 1277 | 135257 |
|---|---:|---:|---:|---:|
| Order of B | 4 | 106 | 1276 | 67628 |

Thus ord_d(B)=67628 divides k, and

    B^k mod lambda^2 = 13998558473 != 1,
    v_lambda(B^k-1)=1.

For H0=1+B DC+B^2(DR+1), the unit certificate is:

| Prime p | B mod p | (B^2-1) mod p | H0 mod p |
|---|---:|---:|---:|
| 5 | 3 | 3 | 2 |
| 107 | 88 | 39 | 58 |
| 1277 | 942 | 1125 | 956 |
| 135257 | 55321 | 88158 | 66933 |

Choose the independently padded spatial width w and temporal height h
to be sufficiently large powers of lambda. Put N=wh=lambda^n, q=B^N,
with N>d lambda^2 and h>lambda. Because all listed orders divide lambda-1,
q=B^w=B modulo d lambda.

Switching the low dummy bit at position 1063 of cell j changes the actual
packed rank by

    delta R=-Gamma B^j,
    Gamma=rho^1063(q^2-1)[1+q(DC+B DR+B^w)].

The identity is unchanged because neither the dummy location nor the
arithmetic transport equation changed. The unit table gives
gcd(Gamma,dN)=1.

Here is the full Boolean coverage argument. Put T=N/lambda and C0=d lambda.
Every residue modulo dN=C0 T is a Boolean sum of the weights

    {B^(2+kj): 0<=j<T} union {B^3}.

Indeed B^k=1 modulo d and has lambda-adic valuation one after subtracting
one. Its first T powers are precisely the residues 1+C0 z modulo C0 T.
After multiplying a target by B^(-2), subtract epsilon B, epsilon in {0,1},
so that the result is nonzero modulo lambda. Its least residue a modulo
C0 then satisfies 1<=a<C0<T and gcd(a,T)=1. Write the target as a+C0 u and
solve

    a z0 + a(a-1)/2 = u modulo T.

The a distinct orbit residues with additive coordinates
z0,z0+1,...,z0+a-1 modulo T have exactly the desired sum. Include B^3 if
epsilon=1. This selects each dummy cell at most once.

The largest selected position is at most
N-N/lambda-lambda+3. Since h>lambda, w<N/lambda. These positions, their
spatial translate by one and their temporal translate by w all remain
below N and avoid the origin. Position 3 is separate because k>1. Therefore
the inherited no-wrap dummy argument is valid.

From a canonical tiling with rank R0 choose the Boolean sum
(R0-dw)Gamma^(-1) modulo dN. The changed actual rank then satisfies
R=dw modulo dN, exactly the required temporal rotation of X=2^R. This
controls the actual index, not a free surrogate. Every local constraint,
carry bound and strict positive slack is preserved. The inherited Pell
converse supplies the remaining positive witnesses.

Soundness imposes no prime-power restriction on solutions. Prime powers
are used only to construct a canonical witness from a finite halting run.

## 6. Signed-domain completeness promises and composition

Both d and N are odd. Let t=dN and q=2^t. The canonical word C is 1 modulo
4 because Start is selector 0, selector 1 is forbidden, and every other
position is higher. The balanced populations and low congruences above
are exactly the source hypotheses for the identities pc(R)=3t+2 and
R=3 modulo4. Safe dummy changes preserve them. Thus X/q=2^(R-t) is a
positive square; the canonical Pell parameter is even and its relevant
Pell value is odd. The inherited rank choice m=cR again provides the
positive odd normalized multiplier. The half-binomial scale is odd as
well. No signed-domain adapter loses its canonical completeness witness.

Accordingly this coherent tuple can be used in any of the compatible
positive, ordinary, quartic or signed arithmetic skeletons. Composing its
soundness/completeness with the unchanged marked Wang-language theorem
and K215/refutation calibration proves in ZFC:

    the bound system has a solution in its stated domain
        iff ZFC has a finite refutation.

Negating both sides yields the requested equivalence with Con(ZFC).
Jones/Sun low-variable compressions require their own fixed indices to
be recomputed after rebinding a parent polynomial. This note does not
silently change an index from a different coefficient tuple.

## 7. Reproduction and provenance

`build_coefficients.py` reconstructs the exact Wang language from the
literal 430 actions, checks every scalar interface identity, the two
support-intersection conditions, mask populations, carries, primality,
multiplicative orders, lifting and units, and materializes all four ports.
`audit_coefficients.py` uses the separately pinned tile list and an
independent formulation, without importing the builder. It checks the
actual payloads and repeats the finite interface audit.

Inherited proof sources and their attribution are retained under
`source_proofs/` and `licenses/`. The direct baseline is package 36,
whose complete proof is `source_proofs/package36_PROOF.md`.
The source language and arithmetic proofs are mathematical dependencies,
not conclusions of the finite Python checks. No coefficient optimality,
new variable-count record, or decision of Con(ZFC) is asserted.
