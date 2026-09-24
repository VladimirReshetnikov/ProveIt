# Life with one auxiliary and one affine mask field

This note gives an exact local improvement to
[the five-auxiliary Life relation](EXPLORATION_LIFE_LOCAL_ARITHMETIC.md).
Given the inclusive nine-cell sum, the arithmetic takes **8=4M+4A**,
uses **one Boolean auxiliary**, and produces one radix-256 field with
two forbidden bits. The old inclusive-sum relation takes 11 operations
and five Boolean auxiliaries. Neither number pays for its digit tests.

A separately counted mask/index wrapper below takes **26=14M+12A**
using a nine-operation shifted version of that local expression. It is
conditional on an already established radix power, aligned Boolean input/output words, and the
inclusive sum. It is not a complete history system, a universal equation
system, or a claimed improvement to the retained universal bound.
Numerals are free; multiplication by a numeral is charged.

## 1. Exact scalar relation

Let n be the number of live neighbors, 0<=n<=8; let b,y,u be Boolean;
and put s=n+b. Define

    v = 14s+b+8y+59u+20.

Then

    y = Life(n,b)  iff  there exists u in {0,1} with (v & 72)=0.       (1)

The forbidden mask is 72=2^3+2^6. For every n,b there is exactly one
accepted pair (y,u). The following exhaustive table is a finite proof;
the four digit columns are ordered (y,u)=(0,0),(0,1),(1,0),(1,1).
In each row exactly the indicated digit has both forbidden bits zero.

| n | b | Four affine digits | Accepted (y,u) | Accepted digit |
|---:|---:|---|---|---:|
| 0 | 0 | 20,79,28,87 | (0,0) | 20 |
| 0 | 1 | 35,94,43,102 | (0,0) | 35 |
| 1 | 0 | 34,93,42,101 | (0,0) | 34 |
| 1 | 1 | 49,108,57,116 | (0,0) | 49 |
| 2 | 0 | 48,107,56,115 | (0,0) | 48 |
| 2 | 1 | 63,122,71,130 | (1,1) | 130 |
| 3 | 0 | 62,121,70,129 | (1,1) | 129 |
| 3 | 1 | 77,136,85,144 | (1,1) | 144 |
| 4 | 0 | 76,135,84,143 | (0,1) | 135 |
| 4 | 1 | 91,150,99,158 | (0,1) | 150 |
| 5 | 0 | 90,149,98,157 | (0,1) | 149 |
| 5 | 1 | 105,164,113,172 | (0,1) | 164 |
| 6 | 0 | 104,163,112,171 | (0,1) | 163 |
| 6 | 1 | 119,178,127,186 | (0,1) | 178 |
| 7 | 0 | 118,177,126,185 | (0,1) | 177 |
| 7 | 1 | 133,192,141,200 | (0,0) | 133 |
| 8 | 0 | 132,191,140,199 | (0,0) | 132 |
| 8 | 1 | 147,206,155,214 | (0,0) | 147 |

All 72 affine digits lie in [20,214], strictly within radix 256.
In particular (1) does not rely on accepting a carry into the next cell.
The helper u is not simply a monotone threshold: its values at large
counts return to zero. The finite table, not an asserted threshold
interpretation, establishes the rule.

## 2. Packed relation and its eight-operation source

For m>=1 cells set q=256^m and J=(q-1)/255. Suppose B,Y,U are
radix-256 Boolean words of length m, and S is the coordinatewise sum
of a cell and its eight Boolean neighbors. Then

    V = 14S+B+8Y+59U+20J.                                      (2)

Every raw digit is the v above. Hence 0<V<q, with no carry between
cells, and

    V & (72J)=0

is exactly the simultaneous Life rule. The count is four numeral
multiplications (14S,8Y,59U,20J) and four additions. The numeral 20
is free, but the all-one word J and its multiplication are not silently
free: the multiplication is included here, and J's defining relation
is counted separately below. If only the exclusive neighbor count N
is supplied, computing S=N+B adds one operation.

This relation has one separately typed Boolean helper U and one mixed
field V. It also needs B and Y to be Boolean, either through independent
masks or through an established history/shift argument. In particular,
an unproved claim that Y is a shifted copy of B cannot replace typing.

## 3. A shifted field gives a conditional 26-operation wrapper

For this wrapper use radix512, set q=512^m and J=(q-1)/511, and
assume the aligned Boolean-word and inclusive-sum domains from section2.
Instead of first computing V and then doubling it, compute directly

    Vprime = 28S+2B+16Y+118U+41J = 2V+J.                     (3)

This takes9=5M+4A. Every digit is odd and lies in[41,429], below512;
forbidden mask144=2*72 tests exactly the same local condition as(1).
Put the mixed field first and the Boolean fields after it:

    P = Vprime+q(B+qU),
    M = J[144+510(q+q^2)],
    Lambda = q^4,
    D0 = q^6,
    r = (Lambda-P)(Lambda-1)+M.                              (4)

The three occupied base-q blocks of P are Vprime,B,U; its fourth block
is zero. Since Vprime,B,U<q, these blocks do not overlap. Mask510=511-1
allows exactly digits0 or1 in each Boolean block; mask144 applies the
local rule to the first block. Thus P&M=0 types B,U and tests the local
relation, provided the displayed field decomposition has been justified.
Independently of pre-existing Boolean typing, extraction remains valid
under the separate bounds0<=Vprime,B,U<q. Y typing and the meaning of S
are still separate obligations.

The mask's two Boolean blocks contribute8m set bits each; its first
block contributes2m. Consequently

    popcount(M)=18m,
    log2(Lambda)+popcount(M)=36m+18m=54m,
    D0=2^(54m).                                               (5)

The zero fourth block is useful: it makes the threshold exactly q^6,
so the existing square-scale kernel can use n0=q^3. The powers
q^2,q^4,q^6 need just three multiplications. Using Lambda=q^3 would
instead give q^5 and would require a separate audit of the kernel
scale; that alternative is not used here.

For arbitrary 0<=P,M<Lambda=2^k, the proved arbitrary-mask lemma is

    popcount((Lambda-P)(Lambda-1)+M) <= k+popcount(M),

with equality exactly when P&M=0. This includes P+M>=Lambda, where
the inequality is strict. The lemma and the complete square-scale
kernel are proved in the
[one-field Rule110 component](EXPLORATION_RULE110_THREE_BIT_FIELD.md)
and [finite-history successor](EXPLORATION_ONE_FIELD_RULE110_HISTORY.md).
Together with v2(binomial(2r,r))=popcount(r), (5) makes the divisibility
test D0 | binomial(2r,r) equivalent to the desired simultaneous mask.

Under the assumed typed domains, 0<P,M<q^3<Lambda. Therefore
n0<=r<q^8<2n0^3 and n0>=64, the numerical range needed by the retained
kernel. For the lower bound, Lambda-P>q^4-q^3 and Lambda-1>=1, so
r>q^4-q^3>=q^3. For the upper bound, P>=1 and M<Lambda give
r<Lambda^2. Also P is odd and M is even, so r is odd. The fixed-minus
43-operation base-two kernel from
[the odd-index Pell note](EXPLORATION_ODD_INDEX_PELL_SIGNS.md) therefore
has its audited positive converse at the actual index. This is a
conditional compatibility statement: no new Pell source is being
introduced or counted as part of the26 operations.

| Source part | M | A | Total |
|---|---:|---:|---:|
| q^2,q^4,q^6 | 3 | 0 | 3 |
| 511J=q-1 | 1 | 1 | 2 |
| Vprime in (3) | 5 | 4 | 9 |
| P: qU, B+qU, times q, addition | 2 | 2 | 4 |
| M: q+q^2, times510, plus144, times J | 2 | 2 | 4 |
| r in (4) | 1 | 3 | 4 |
| **Conditional local/mask/index wrapper** | **14** | **12** | **26** |

All comparisons and literals are free. These26 operations already
include the shifted local relation; the standalone8 must not be added
again. Supplying positive variables to represent potentially zero
B,U,Y, proving q's radix power and the untyped bounds before invoking
the kernel, constructing S and temporal shifts, spatial seams, target
detection, and a universal input interface remain unpaid. Thus adding
43 to26 is not a complete69-operation Life or universal certificate.

For comparison, retaining radix256 and the unshifted V permits an
odd-index layout P=2(B+qU)+q^2V and M=J[253(1+q)+72q^2]. Its three
powers, ones relation, local expression, packing, mask and index take
3+2+8+5+5+4=27 operations. The direct shifted expression(3), changed
field order and factored mask save one operation overall in(4).

## 4. Discovery boundary and reproducibility

The separate bounded search
`tmp/search_life_more_aux_masks.cpp` searches a single affine form
`a0+an*n+ab*b+ay*y+au*u(+av*v)` and a fixed zero-bit mask, requiring
every value on the full scalar domain to fit the chosen radix. It found
no one-helper form at radix128 (228,998,784 coefficient/offset cases),
no two-helper form at radix64 (27,096,832), and none at radix128
(2,332,433,920). These are bounded negative searches, not lower bounds
for arbitrary encodings. Complementing and permuting Boolean helpers
allows their coefficients to be positive and ordered in that search.

An unrestricted radix256 run first found
`103+7n-b+63y+27u`, mask68, range102..249, after5,382,961,612 cases.
It stopped at that candidate. A second search requiring ab-an=+/-1
found (1), whose inclusive-sum form saves one multiplication relative
to that initial candidate. The final checker verifies both variants,
and the independently derived radix512 inclusive form
`17s-b+84+120u+8y`, mask136, range84..364. Only the radix256 form (2)
is used in the local schedule, and its direct shifted form(3) is used
in the wrapper schedule. No minimum is
claimed for the radix or the arithmetic count.

The reproducible checker is
[explore_life_one_field_mask.py](../verification/explore_life_one_field_mask.py);
its saved exact receipt is
[explore_life_one_field_mask.json](../verification/explore_life_one_field_mask.json).
It exhausts the scalar truth table, all nine-cell neighborhoods and
output/helper choices, every pair of scalar assignments, and every
one-cell value in each field and their Boolean/mixed combinations.
It also checks the arbitrary-mask
lemma on small widths including overflowing P+M, the operation schedules
and their symbolic identities,
and deterministic multi-cell wrapper instances and corrupted outputs.
These tests support the finite proofs and explicit scope above.

Review status: author and two independent complete scoped proof/source
reviews and fresh receipt checks PASS. A further independent calculation
also verifies the selected scalar relation and the26-operation schedule.
