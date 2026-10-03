# Exact paired Boolean ternary queues from a positive split of ordinary input

Three operations extend the independently reviewed
[Boolean ternary FIFO60](input_bridge_boolean_ternary60.md) to two
independently preserved Boolean queue lanes. The complete component costs
**63=32M+31A**, with18 equations and29 strictly positive witnesses besides
the ordinary positive input x. A general fixed affine carry controller
costs **72=37M+35A**, with19 equations and the same witnesses.

These are exact component projections. They do not include a universal
compiler or an acceptance theorem. Their queue alphabet is the four pairs
of Boolean digits, genuinely restricting the nine-symbol paired ternary
alphabet. The unfiltered paired-queue Presburger reductions therefore do
not apply directly. The established complete universal bound remains76.

## 1. Literal source and count

Retain the complete60-operation source. Its supplied positive fields are
F0,F1,F2,F3, with append sum A=F0+F1, read sum D=F2+F3, and equations

    I=2x, D=I+WA, I+width_beta=W, q=WL,
    F0+F1+F2+F3+alpha=q.                               (1)

The retained Boolean55 kernel and packing certify q=3^t, t>=2, and
positive native Boolean ternary fields Fi<q. Every ternary digit of every
Fi is0 or1, and sum Fi is even. All positive kernel coordinates and the
paid bound X>r are retained unchanged.

Supply two additional strictly positive witnesses init0,init1 and compute

    initial_sum=init0+init1,
    lane_tail=W*F0,
    lane_transport=init0+lane_tail.                    (2)

Make the free comparisons initial_sum=I and F2=lane_transport. These are
one multiplication and two additions. Subtracting their equations from
the existing scalar transport proves the second lane transport:

    init0+init1=2x,
    F2=init0+W*F0, F3=init1+W*F1.                      (3)

The source has63=32M+31A,18 equations and29 positive witnesses besides x.
The literal checker imports the frozen60 source, appends exactly(2), and
expands every source polynomial independently. It audits the inherited
auxiliary-norm correction and the complete combined register dependency
graph. In particular the second equation of(3) is a consequence of paid
equations, not a free arithmetic expression.

## 2. Exact paired-queue projection

Write Ii=init_i. The source projects exactly to the following finite runs:

- q=3^t and W=3^m, with integers m>=1 and t>=m+1;
- positive Boolean ternary initial words I0,I1 with I0+I1=2x<W;
- a synchronized t-step pair of width-m Boolean queues, starting at
  (I0,I1) and ending at(0,0);
- positive append and read streams F0,F1 and F2,F3, respectively, and
  F0+F1+F2+F3<q.

No initial radix conversion is assumed. The two initial words are actual
positive witnesses constrained by(3), and their Boolean digits follow
from the same transport equations as the stream semantics.

For soundness, q=WL and the inherited power theorem give W=3^m. Since
W>2x>=2, m>=1. Each Ii is smaller than W because its positive pair sums
to2x<W. Taking(3) modulo W shows that Ii consists of the low m digits of
its Boolean read stream, so it is Boolean. The higher digits are exactly
the corresponding append stream. Positivity of either append stream
gives F2>W or F3>W, whereas both are below q; hence q>W and t>=m+1.

With read bit d_i,j and append bit a_i,j, each lane obeys

    d_i,j=N_i,j modulo3,
    N_i,j+1=floor(N_i,j/3)+(W/3)*a_i,j.                (4)

The initial Boolean word and the bit appends keep all queue digits in
{0,1}. Expanding(3) in base3 proves that the read bits at times j<m are
the initial digits, and those at j>=m are a_i,j-m. Since Fi<q and(3)
holds, the last m append bits vanish. These observations prove(4) at every
step and its final zero endpoint. Equivalently, telescoping(4) yields
`3^t*N_i,t=Ii+W*Append_i-Read_i`, whose right side is zero by(3).

Conversely, take any run in the displayed predicate. Telescoping gives
(3) and then all equations(1),(2). Set

    width_beta=W-2x, L=q/W, alpha=q-sum Fi.

These are positive. The remaining parity needed by the Boolean55 theorem
is automatic:

    sum Fi=2x+(W+1)(F0+F1),                            (5)

which is even because W is odd. Apply that theorem's full positive Pell
converse at these exact fields and their packing r. This supplies every
retained coordinate, including X>r and Y=3s+1. Thus the converse applies
to arbitrary such runs; it neither pads their duration nor changes their
endpoints or field values.

## 3. Every ordinary positive input admits a positive split and a bare run

The ternary digit sum of2x is positive and even, since every power of3
is odd. It is therefore at least2. If2x has a digit2, split every such
digit as1+1 and distribute digits1 arbitrarily; both rails are positive.
If it has only digits0/1, at least two digits are1; put one on each rail
and distribute the rest arbitrarily. In either case this yields positive
Boolean ternary words I0,I1 with I0+I1=2x.

Choose a power W=3^m strictly larger than2x+2. Set

    q=3W, t=m+1,
    F0=F1=1, F2=I0+W, F3=I1+W.                       (6)

All four fields are positive Boolean words. Each lane appends1 at the
first step and then zeros, so after m+1 steps both queues are empty.
The joint bound is strict because

    sum Fi=2+2x+2W<3W=q.

All slacks are positive, and Section2 supplies the full Pell extension.
This proves bare-component completeness for every ordinary x. A future
controller still needs to process the existential split consistently and
implement an intended accepting computation. No such normalization or
universal acceptance theorem is asserted here.

The separate lane equation is a real restriction. For example the scalar
60 source admits x=1,W=9,q=81 and fields(1,3,28,10), with total42<81.
Its scalar read38 equals2+9*4 and the four fields are Boolean. But the
forced paired initial values are(19,-17), so this tuple has no extension
to the positive63 source.

## 4. Exact general affine carry interface

Fix arbitrary integers c0,c1,c2,c3,h,cs,cf, independent of x. At a time
step, in the append0,append1,read0,read1 order, use

    3*k_next=k+h+sum ci*label_i, k0=cs, kt=cf.         (7)

The exact global equality is

    2*sum ci*Fi+(h-2cf)q=h-2cs.                       (8)

Four products by the fixed numerals2ci and three summation additions,
then a product of q by h-2cf and one last addition, cost9=5M+4A. The
comparison with the fixed numeral h-2cs is free. This gives the complete
literal72-operation relation,19 equations and29 positive witnesses.
Signed computed registers and fixed numerals are allowed; the supplied
existential coordinates remain strictly positive.

Multiplying(7) by3^j and summing proves(8). Conversely divide(8) by2 in
the mathematical proof to obtain

    cs+h*(q-1)/2+sum ci*Fi=q*cf.

Successive reductions modulo3 show that cs+h+sum ci*label_i,0 is
divisible by3, then that the same is true at each following step after
updating k. The remaining quotient after t steps is cf. Thus every
intermediate carry is integral and(7) holds. The source certifies the
entire affine carry graph on the paired Boolean labels. No selected-edge
filter, state-range restriction, or serialized code is silently imposed.

## 5. Boundaries of related weighted and block interpretations

Replacing the scalar sums by A=F0+3F1 and D=F2+3F3 costs two extra
multiplications. At trit position j the first expression contains
F0_j+F1_(j-1), so this is overlap of adjacent time positions. It is not
a proof that two queue lanes are independently preserved. With initial
2x it also excludes x=1 at the units position, since D modulo3 is a
Boolean bit. Changing the multiplier to6 supplies a low zero but does
not prove separation of the lanes.

Making q and W squares would allow grouping successive trits of a scalar
queue into radix9 cells, at two extra multiplication operations. Its
initial cells would still be the consecutive trit pairs of the original
raw input. They cannot be identified with the earlier paired input
(x,0) without a proved conversion or loader.

An aggregate phase sum alone does not type even positions. At q=81,
the Boolean fields(1,1,4,4) sum to(q-1)/8=10 but have nonzero odd-position
digits. In contrast, a pair of Boolean fields summing to that even-position
repunit has no ternary carry and is forced to complementary even-position
support. Applied permanently to append rails, however, this forces a
nonzero append in every two-step block and conflicts with the last m
zero appends required by an empty queue whenever m>=2. The width-one
exception is real: x=1,W=3,q=81, initials(1,1) and fields(1,9,4,28)
satisfy the full63 predicate, with append sum10=(q-1)/8. Its last append
is the odd-position zero. But W=3 and2x<W force x=1, so permanent phase
complementation still excludes unbounded ordinary inputs. A general
cleanup exception needs its own proved and costed interface. None of
these interpretations is part of the63-operation theorem.

## 6. Evidence and scope

The [checker](native_boolean_pair_fifo63.py) audits all source equations,
the complete63/72 operation ledgers and the inherited norm correction.
It enumerates positive Boolean stream tuples through t=4, comparing the
unique transport initial values with direct paired-queue execution. Two
hundred positive ordinary inputs have explicit split and positive outer
maps. A separate exhaustive two-step check compares the global carry
identity with integral local paths for coefficients and offsets in
{-1,0,1}. The scalar/paired and aggregate-phase counterexamples are
checked directly.

The positive extension to the enormous auxiliary Pell coordinates is a
parametric theorem inherited from Boolean55, not a claim that the checker
materializes them. Finite checks supplement the proofs. Independent
review of the core proof, source and fresh default replay passed; the
reviewer's width-one boundary correction is now preserved explicitly.
No complete universal improvement below76 is claimed.
