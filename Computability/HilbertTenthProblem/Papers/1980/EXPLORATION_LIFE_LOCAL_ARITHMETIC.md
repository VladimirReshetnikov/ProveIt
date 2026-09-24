# An 18-operation local arithmetic verifier for Life

This is a counted local component for the periodic-preimage direction.
It is not a full torus verifier or a universal certificate. With eight
already aligned neighbor planes, the achieved schedule has **18
operations: 5 multiplications by fixed numerals and 13 additions or
subtractions**. It requires five auxiliary Boolean planes. No ordinary
product of two packed words is used.

The complete schedule and reproducible finite verification are
`../verification/explore_life_local_arithmetic.py` and its JSON receipt.
No optimality claim is made for the local operation count or field count.

## 1. The source problem and its exact local rule

Salo and Torma's [2025 paper, Theorem 9, p.16](https://www.utupub.fi/bitstream/handle/10024/188843/1-s2.0-S0304397525001756-main.pdf?sequence=1)
proves Sigma^0_1-completeness of existence of a totally periodic Life
preimage of a supplied totally periodic configuration. Its local Life
rule is given on p.1: with center bit b and eight-neighbor count n,

    life(n,b)=1 iff n=3 or (n=2 and b=1).           (1)

The quantifier and unbounded-period distinctions are audited in
`EXPLORATION_LIFE_PERIODIC_PREIMAGE.md`. In particular, a finite witness
may have periods larger than the supplied target periods. The present
note addresses only the local constraint in that finite torus witness.

All further constructions in this note are our deductions, not claims
about an arithmetic certificate supplied by that paper.

## 2. One homogeneous linear relation with five Boolean auxiliaries

For n in {0,...,8}, b,y in {0,1}, the following are equivalent:

* y=life(n,b);
* there exist u1,...,u5 in {0,1} such that

    n+22y+6(u1+u2-b)+7u3=11u4+14u5.              (2)

Here is a complete finite proof. First use the nonhomogeneous subset-sum
form

    n-6b+22y+19=6a1+6a2+7a3+11a4+14a5,           (3)

where all a_i are Boolean. The complete set of its 32 subset sums is

    S={0,6,7,11,12,13,14,17,18,19,20,21,
       23,24,25,26,27,30,31,32,33,37,38,44}.

For the four possible pairs (b,y), membership of the left side in S
gives exactly these neighbor counts:

| b | y | Left side | Accepted n in 0,...,8 |
|---|---|---|---|
| 0 | 0 | n+19 | 0,1,2,4,5,6,7,8 |
| 0 | 1 | n+41 | 3 |
| 1 | 0 | n+13 | 0,1,4,5,6,7,8 |
| 1 | 1 | n+35 | 2,3 |

This is precisely (1). Now set

    a1=1-u1, a2=1-u2, a3=1-u3,
    a4=u4, a5=u5.

Since 6+6+7=19, the constants cancel and (3) becomes (2). Thus no
all-ones plane is needed to express the final local relation. The
complement is part of the mathematical witness map, rather than an
instruction computing complements in the final schedule.

## 3. Packed soundness in radix 64

Fix an arbitrary finite list of cells and encode each Boolean field
as a base-64 word. Let B be the center field, Y the supplied target
field, and N the sum of the eight aligned neighbor fields. Its digits
are in {0,...,8}, because summing eight bits has no radix-64 carry.
Choose Boolean auxiliary fields U1,...,U5 and impose

    N+22Y+6(U1+U2-B)+7U3=11U4+14U5.               (4)

To prove digitwise equivalence, rewrite it as an equality between
nonnegative sums:

    N+22Y+6(U1+U2)+7U3=6B+11U4+14U5.             (5)

Every raw digit on the left is at most

    8+22+6+6+7=49<64,

and every raw digit on the right is at most

    6+11+14=31<64.

Thus neither side has a carry. Uniqueness of the base-64 expansion
proves that (4) holds if and only if (2) holds at every cell. By
Section 2, the packed equation is exactly the local Life predicate.
Conversely, when every target digit is correct, choose one of the
finite scalar witnesses at each cell and pack its five coordinates.
That gives nonnegative Boolean words satisfying (4).

The optimized schedule below computes the signed intermediate
U1+U2-B. Signed registers are allowed in the certificate model. The
soundness proof uses the equivalent nonnegative sides (5), so it does
not assume that this intermediate word has independent signed digits.
The argument is linear throughout; no convolution is being mistaken
for a coordinatewise product.

### Radix 32 fails for this unchanged relation

The larger radix is a real requirement of this particular packing
argument, not an arbitrary presentation choice. For the low cell take

    n=2,b=0,y=1,(u1,u2,u3,u4,u5)=(1,1,1,1,0).

Its residual in (2) is 32 and its target is wrong. For the next cell take

    n=0,b=0,y=0,(u1,u2,u3,u4,u5)=(0,1,1,0,1).

Its residual is -1. Packing these two independently specified cells
in radix 32 gives total residual 32+32*(-1)=0, despite the false low
target. This is a counterexample to the local packed equation in that
radix. It is not asserted to be an aligned torus counterexample.

## 4. Exact 18-operation schedule

Write A0,...,A7 for the eight already aligned neighbor words. First
sum them with seven additions to obtain N. Then compute

| Step | Primitive instruction | Type |
|---|---|---|
| 1-7 | N=A0+...+A7, one addition at a time | 7 additions |
| 8 | u12=U1+U2 | addition |
| 9 | u12b=u12-B | subtraction |
| 10 | m6=6*u12b | multiplication |
| 11 | m7=7*U3 | multiplication |
| 12 | m11=11*U4 | multiplication |
| 13 | m14=14*U5 | multiplication |
| 14 | m22=22*Y | multiplication |
| 15 | lhs1=N+m6 | addition |
| 16 | lhs2=lhs1+m7 | addition |
| 17 | lhs=lhs2+m22 | addition |
| 18 | rhs=m11+m14 | addition |

Test lhs=rhs for free. Fixed numerals are free inputs, but their five
multiplications are all counted. The cost is 5M+13A=18. The local
predicate after the neighbor sum has been supplied costs 11 operations,
5M+6A.

Five auxiliary planes are used by (4). If torus alignment derives all
eight neighbors from one Boolean preimage plane B, and Y is already
known to be the Boolean target, the local Boolean obligations are
exactly six planes: B,U1,...,U5. If Y's Booleanity has not yet been
established, it is a seventh obligation. Merely supplying nine
independent neighbor/center fields would instead require Booleanity
of all nine plus the five auxiliaries; the lower field count assumes
actual proved alignment, not nine unchecked supplied fields.

## 5. A shared neighbor aggregation, conditional on its shifts

There is a second useful interface when torus shifts themselves will
be implemented. Let Vminus and Vplus be the correctly vertically
shifted copies of B, and form

    V=Vminus+B+Vplus                              (2 additions).

If L(V),R(V) are the correctly horizontally shifted versions of this
three-row sum, then the inclusive nine-cell sum is

    S=L(V)+V+R(V)                                 (2 additions). (6)

It satisfies S=N+B, with the correct multiplicities even for small
torus periods. Replacing N by S-B in (4) and regrouping gives

    S+22Y+6(U1+U2)+7(U3-B)=11U4+14U5.             (7)

This still costs eleven operations after S is supplied: two additions
or subtractions form U1+U2 and U3-B, five multiplications form the
same coefficient groups, and four additions assemble the two sides.
Its nonnegative sides have digit bounds 50 and 32, both below 64.
The checker independently evaluates this eleven-step schedule on
every complete local test as well.

Thus four aggregation additions and the eleven-operation predicate
give a conditional **15-operation arithmetic component**, 5M+10A.
The four shift relations are not included: they must implement
the two-dimensional torus and its corner cases exactly. In particular,
an ordinary cyclic shift of the entire row-major word is not the
horizontal shift of each row. Consequently 15 is not a count for a
complete aligned local verifier.

## 6. Comparison with a radix-16 Boolean gate implementation

A straightforward independent implementation first decomposes the
neighbor count into four Boolean bit planes:

    N=N0+2N1+4N2+8N3.

This uses three multiplications and three additions after the seven
neighbor additions. Since n<=8, the rule is

    y=n1 AND (NOT n2) AND (n0 OR b).

For an available all-ones word J, use Boolean U,V and xor witnesses
Z1,Z2,Z3 with

    N0+B+Z1=2U,
    N1+J=N2+Z2+2V,
    U+V=Z3+2Y.

These equations cost 3,4,3 operations respectively. Each is a
carry-free half-adder identity in radix 16. The total is therefore
23 operations, 6M+17A, with nine auxiliary Boolean planes: the four
count bits and U,V,Z1,Z2,Z3. This assumes J is already available;
constructing an all-ones field through 15J+1=Q costs two further
operations unless a proved shared register supplies it.

For comparison, the existing Rule 110 local relation costs seven
operations and, after its spatial alignment and causal argument,
uses five explicitly masked planes. These are comparisons of
specified components, not comparable complete universal-system
bounds. The subset-sum Life relation reduces its own gate baseline
by five operations and four auxiliary planes, at the expense of
using radix 64 instead of radix 16.

## 7. Mask and positive-domain obligations remain explicit

For the general radix 2^k periodic mask, one conservative scale interface
is L=q^(2k), D0=q^(4k-2), N0=q^(2k-1). The mask word has digit
2^k-2, and the associated popcount threshold is (2k-1) times the
number of radix digits. Applying the separately proved general-mask
lemma, radix 64 would use

    L=q^12, D0=q^22, N0=q^11.

The powers can be computed in six multiplications:

    q2=q*q, q4=q2*q2, q8=q4*q4,
    q10=q8*q2, L=q8*q4, D0=L*q10.

No N0 register is needed by the retained kernel. If radix-64 field
boundaries are obtained through row geometry, W=v^6 takes three
multiplications, and q=v*quot together with W-1 dividing q-1 gives
q=W^t after q becomes a power of two. These power costs exceed the
corresponding radix-four component costs and cannot be omitted from
a whole-system comparison. This paragraph specifies an interface;
it does not supply the still-missing global bounds, alignment, or
parity needed for a complete new kernel composition.

The subsequent proof in `EXPLORATION_GENERAL_RADIX_BOOLEAN_MASK.md`
also supplies a six-field radix-64 interface with L=q^6 and D0=q^11,
whose five power products save one multiplication in this local mask
component. The kernel needs a sufficiently large common divisibility
scale, not a square scale. That note further proves a native doubled-
digit radix-128 option using the same-cost odd-index kernel. These
alternatives still require the surrounding bounds and geometry; neither
is a complete Life certificate.

The witnesses supplied by Section 3 are nonnegative words. Some can
be zero on a perfectly valid periodic preimage. In fact all-zero
neighborhoods admit the all-zero five-tuple in (2). No argument here
turns all six mask fields into positive unknowns at zero cost.
A complete positive-integer system must account for a representation
of zero fields, or prove that its encoded target gadgets force each
required field to be nonzero. Similarly, it must encode the raw
input target, its unbounded repetitions, both seams, and all ranges.

## 8. Reproducible evidence and scope

The verifier checks all 36 count/center/output choices against all
32 auxiliary assignments, and all 512 nine-bit neighborhoods with
both outputs and all 32 auxiliary assignments: 32,768 complete local
cases. It evaluates the actual 18-step schedule, checks the digit
bounds, and exercises 72 deterministic packed cases with deliberately
corrupted outputs. It also reproduces the radix-32 carry collision.

The complete finite table establishes the local Boolean equivalence;
the digit bounds establish its general packed version. The sampled
packed cases are supplementary regression evidence, not a substitute
for that proof. No universal operation bound or local optimum is
claimed.
