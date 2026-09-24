# Life with one Boolean helper and eight affine operations

The inclusive Life predicate has a constructive **8=3M+5A** arithmetic
component using **one auxiliary Boolean plane**, followed by two fixed
binary-digit tests. The existing homogeneous subset-sum component uses
11 operations and five auxiliary Boolean planes. The new eight operations
do not themselves pay for the digit tests. Sections 4-6 give separately
counted mixed-mask sources that perform both tests together with the
center and helper Boolean checks.

This is a local component, not a complete torus, raw-input, or universal
certificate. The exact source checker is
`../verification/explore_life_threshold_masks.py`, with an adjacent receipt.
The Life rule and periodic-preimage source are recorded in
`EXPLORATION_LIFE_LOCAL_ARITHMETIC.md` and
`EXPLORATION_LIFE_PERIODIC_PREIMAGE.md`; all new identities below are proved
here. Numerals are free inputs; every multiplication by one is charged.

## 1. A unique one-bit witness

Let n in {0,...,8} count the live neighbors, b in {0,1} be the center,
y in {0,1} the proposed output, and s=n+b the inclusive nine-cell count.
Define the two thresholds

    v=[s>=3],  w=[n>=4].

Then w<=v and Life is exactly

    y=v-w.                                                        (1)

Indeed n<=1 gives v=w=0; n=2 gives v=b,w=0; n=3 gives v=1,w=0;
and n>=4 gives v=w=1.

For an auxiliary bit u, form

    f=s+5+8u,
    g=f-b-1+8y=n+4+8u+8y.                                        (2)

Write bit3(z) for the binary digit of weight8. The complete local relation is

    bit3(f)=0,  bit3(g)=0.                                        (3)

Because 5<=s+5<=14, its bit3 is v. Adding8u toggles that bit, so the
first test uniquely forces u=v. Similarly 4<=n+4<=12 has bit3 equal
to w, and the second test says w+u+y is even. With w<=u and both
Boolean, this forces y=u-w, proving (1). Conversely, the correct Life
output with u=v passes both tests.

For all input and auxiliary bit assignments, including rejected ones,

    5<=f<=22,  4<=g<=28.                                         (4)

Thus radix32 accommodates both forms without intercell carries.

## 2. Exactly eight operations in the inclusive interface

For t>=1 cells put q=32^t and J=(q-1)/31. Let B,Y,U be their Boolean
words, and let S be the actual inclusive neighbor sum, with digits0..9.
Define F,G by the packed forms corresponding to (2):

    F=S+5J+8U,
    G=F-B-J+8Y.                                                   (5)

The schedule is

| Step | Primitive | Type |
|---:|---|---|
| 1 | u8=8U | multiplication |
| 2 | j5=5J | multiplication |
| 3 | f0=S+j5 | addition |
| 4 | F=f0+u8 | addition |
| 5 | y8=8Y | multiplication |
| 6 | g0=F-B | subtraction |
| 7 | g1=g0-J | subtraction |
| 8 | G=g1+y8 | addition |

The prescribed tests are F AND(8J)=0 and G AND(8J)=0. Bounds (4)
show that these are exactly the scalar tests at every cell. Subtractions
are permitted signed registers; the final G has the digit expansion
in (2), with no borrowing issue in its interpretation.

The cost is 3M+5A. This assumes S and J are already supplied. If only
the excluded-center count N is supplied, forming S=N+B adds one addition.
Producing J, producing S through actual torus geometry, and implementing
the two fixed-bit tests are separate costs. In particular, a convolution
interface that previously computed a scaled linear form cannot reuse
that cost verbatim when S becomes a supplied coordinate.

Once actual alignment derives the neighbors from B and Y is known Boolean,
the only Boolean plane obligations here are B and U. If Y is not already
typed, it is a third obligation. F,G are computed multibit words; they
must satisfy their one-bit tests, not Booleanity.

## 3. A carry lemma for an arbitrary mask

Let L=2^ell, 0<=P<L and 0<=M<L. Put

    r=(L-P)(L-1)+M,
    c=popcount(P)+popcount(M)-popcount(P+M).

The integer c counts binary carry events. The exact identity is

    popcount(r)=ell+popcount(M)-c,                 if P+M<L,
    popcount(r)=ell+popcount(M)-c-v2(P),           if P+M>=L.       (6)

For the first case use r=(L-P-1)L+(P+M); the first coefficient is
the ell-bit complement of P. For the second use
r=(L-P)L+(P+M-L), together with
popcount(L-P)=ell-popcount(P-1) and
popcount(P-1)=popcount(P)-1+v2(P). Overflow implies P>0.

The number c is nonnegative and vanishes precisely when P AND M=0.
If it vanishes, P+M=P OR M<L, so overflow is impossible. Therefore

    popcount(r)<=ell+popcount(M),
    equality iff P AND M=0.                                      (7)

Finally v2(binom(2r,r))=popcount(r), by the standard binary digit-sum
formula for factorial valuations. Thus one divisibility test at the
maximal threshold enforces an arbitrary combination of forbidden bits.
This extends the mask calculation of
`EXPLORATION_GENERAL_RADIX_BOOLEAN_MASK.md`; it does not assume a
carry-free addition before deriving (6).

## 4. Four mixed fields in radix32: a 28-operation source

Conditionally assume q=32^t and 0<=B,U,F,G<q. Pack

    P=B+qU+q^2 F+q^3 G,  L=q^4.                                  (8)

Each field occupies t cells. Set

    lambda=(q^2-1)/31=J(1+q),
    M=lambda(30+8q^2).                                            (9)

The first two field masks have digit30, forbidding every bit except
the Boolean weight1. The last two have digit8, testing (3).
Consequently

    P AND M=0 iff B,U are Boolean and both tests in (3) hold.

The mask has popcount (4+4+1+1)t=10t, while log2(L)=20t. With
r as in (6), condition (7) becomes exactly

    q^6 divides binom(2r,r).                                      (10)

With Y typed and S its actual inclusive count after B is decoded,
(10) therefore gives precisely the local Life relation at every cell.

The full source subtotal, excluding the implementation of (10), is

| Part | M | A | Total |
|---|---:|---:|---:|
| F,G from S,B,Y,U,J | 3 | 5 | 8 |
| Four-field Horner packing | 3 | 3 | 6 |
| q2=q*q, L=q2*q2, D0=L*q2 | 3 | 0 | 3 |
| 31J+1=q and31lambda+1=q2 | 2 | 2 | 4 |
| M=lambda(30+8q2) | 2 | 1 | 3 |
| r=(L-P)(L-1)+M | 1 | 3 | 4 |
| Total | 14 | 14 | 28 |

The last line explicitly constructs both subtractions, the product and
the addition. Equation tests are free; binomial divisibility is not.
Here the parity of r is the parity of P and is not fixed. A particular
signed Pell necessity construction cannot be invoked for both parities
without checking its interface. The next variant supplies fixed odd parity.

## 5. Radix64 and one global doubling: a 29-operation odd-index source

Use q=64^t and J=(q-1)/63. The same eight operations (5) define
undoubled F,G, with the same digit bounds. Pack the same P0 as in (8),
and add the one multiplication

    P=2P0.

Use

    L=q^4,  D0=q^6,
    lambda=(q^2-1)/63=J(1+q),
    M=lambda(61+16q^2),  r=(L-P)(L-1)+M.                          (11)

The first two masks have digit61, permitting only weight2. The final
two have digit16, which tests the doubled version of bit3. Assume the
individual pre-decoding bounds

    0<=2B,2U,2F,2G<q.                                            (12)

Then P<L and the four doubled field boundaries are exact. Conversely,
all intended words satisfy (12): even the largest raw digit after
doubling is 56<64. Booleanity of the first two doubled fields means
exactly that the original B,U are Boolean. Once those are decoded,
the established F,G digit bounds make the remaining bit tests precisely
(3). The mask popcount is (5+5+1+1)t=12t and log2(L)=24t, so the
required threshold is 36t, again D0=q^6.

The cost is the previous table with63 in place of31 and mask coefficients
61,16 in place of30,8, plus the global doubling: **29=15M+14A**.
No four separate doublings are hidden. Accepted P is even and M is odd;
hence r is odd. The same-cost fixed-minus43 kernel is the relevant sign
choice in `EXPLORATION_ODD_INDEX_PELL_SIGNS.md`.

### Preliminary range facts, without assuming powers

These sources do not establish (12) or its radix32 counterpart. Given
those bounds, however, their index estimates can be checked before
power decoding. Both geometry equations give q>=32, positive lambda,
and M>0. Also M<L follows directly from

    31M=8q^4+22q^2-30 <31q^4                 (radix32),
    63M=16q^4+45q^2-61 <63q^4               (radix64).

For 0<=P<L this gives

    q^3 < L-1 < r < L^2=q^8 < 2(q^3)^3.                         (13)

Thus n0=q^3>=64 and D0=n0^2 supply the usual kernel scale/range
interface. In particular D0^2=q^12>2r+1 and >r+1. If the retained
kernel then proves its exponential coordinate is a power of two,
D0 dividing that coordinate implies q is a power of two. The already
paid equation (R-1)J+1=q then makes q a power of R: the order of2
modulo31 is5, and modulo63 is6. Field boundaries are consequently
aligned before applying the mask argument.

For a full positive necessity construction, the radix64 variant supplies
odd r, the exact q^6 divisibility, and (13). The published fixed-minus43
converse supplies the remaining auxiliary coordinates under its stated
hypotheses. This note does not reproduce or recount those43 operations,
nor derive the input field bounds from a complete surrounding system.

## 6. Comparison and remaining obligations

The primary improvement is the local representation: one Boolean helper
instead of five, and eight affine operations instead of eleven in the
inclusive interface. The two tests are paid together by the mixed-mask
construction; they are not treated as free arithmetic comparisons.

For component comparison, the previous six-field radix64 arrangement
has local predicate11, six-field packing10, and mask source11, totaling32
operations before its kernel. The new odd-index arrangement totals29,
including its own J equation. Their surrounding geometry, bounds and
positive-domain interfaces still differ. These numbers alone do not
establish that replacing the predicate in the existing torus source
saves three operations overall.

In particular, a complete torus compiler still owes actual neighbor
alignment and both seams, target repetition over unbounded witness
periods, a uniform raw-input interface, the bounds before decoding,
and positive representations of any vanishing fields. U can vanish:
an all-zero local configuration has u=0 at every cell. B can vanish
as well. The two computed words F,G are positive for a nonempty list
of cells, but this does not make their source planes positive.
Supplying a signed convolution quotient and the inclusive coordinate S
also needs an honest counted source. No full torus operation total is
claimed here.

## 7. Fresh checks

The checker verifies all source primitives and 19 independently written
polynomial identities across the28/29 variants. It tests all72 scalar
count/center/output/helper assignments and all2,048 complete nine-bit
neighborhood/output/helper assignments, finding the unique helper (1).

It exhausts every mask M and word P for binary widths1 through8:
87,380 pairs, including43,435 overflows, checking both exact formulas
in (6) and the equality criterion. It exercises720 packed mixed-mask
instances with lengths1 through12, including corrupted outputs and
helpers, and238 instances with a zero center, output or helper field.
It also checks42 preliminary bound instances,33 with non-power q.
These are finite corroborations of the general proofs, not tests of
unprovided torus geometry or all enormous Pell witnesses.

Review status: author and two independent complete scoped proof/source
reviews and fresh receipt checks PASS.
