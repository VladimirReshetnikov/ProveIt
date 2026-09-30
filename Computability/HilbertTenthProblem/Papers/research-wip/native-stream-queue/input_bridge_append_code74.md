# A paid append-code filter, with exact endpoint and loading obstructions

Two additional Boolean helper fields turn the
[direct Boolean FIFO60](input_bridge_boolean_ternary60.md) into an exact
append00/12 filter in68 operations. The existing zero-code affine controller
then fits73 operations at endpoint0, or74 at endpoint7. The former relation
is empty. The latter has positive witnesses, but no fixed positive affine
input map can make its controller process every ordinary input. These are
whole-language statements that allow arbitrary raw reads during loading;
neither assumes that the input was already block coded.

The fixed controller and a fixed affine prefix are therefore insufficient
as a universal ordinary-input compiler. This does not exclude other
controllers, a separately paid loader, a phased filter, or a different
acceptance condition. The complete universal bound remains76.

## 1. Exact paid filter and its positive projection

Retain all equations and positive coordinates of Boolean60. Add positive
B,C and extend its packing to

    r=F0+qF1+q^2F2+q^3F3+q^4B+q^5C.

Two extra Horner stages cost4 operations. Also compute

    E=B+C, eight_E=8E, q_calc=eight_E+1, code_append=7B,

and compare q=q_calc and A=code_append, reusing A=F0+F1. These four
operations give **68=35M+33A**, with18 equations and29 positive witnesses
besides ordinary x. The original input is I=2x, the read is D=F2+F3,
and the retained transport and bounds are

    D=I+WA, I<W, q=WL, A+D<q.                          (1)

No read-stream code filter is added.

The changed six-field packing remains within the proved kernel interface.
The old joint bound gives 0<Fi<q for the first four fields, while q=8(B+C)+1
gives 0<B,C<q. Its index is at least1+q+...+q^5 and below q^6. The paid
bound X>r and Y=3s+1 still give every bootstrap inequality in the Boolean60
proof. Consequently q=3^t, r is even, and all six supplied fields have
Boolean ternary digits. Its complete positive converse uses exactly the
same map at this larger actual r; neither q^4 nor an upper bound of q^4
was a rank or ratio hypothesis.

Since q=8E+1, t is even. Write t=2n. Then

    E=(q-1)/8=1+9+...+9^(n-1).

Two Boolean ternary fields B,C sum without carry, because their digit sums
are at most2. Their sum E therefore forces them to partition the even
ternary positions: both vanish at odd positions, and exactly one is1 at
each even position. It follows that A=7B has successive low-first trit
blocks00 or12, since7=1+2*3. Conversely every such append word has this B;
C is its complementary even-position selector.

Positivity means at least one block is12 and at least one is00. Transport
with I=2x gives A+D even. Since q is odd, packing parity is

    r = A+D+B+C = E modulo2.

Thus E is even, equivalently q=1 modulo16, and hence **t is divisible by4**.
Conversely, for a run with I=2x, append blocks00/12 containing both kinds,
t divisible by4, four nonzero Boolean rails and the joint bound, the
packing is even and every digit is Boolean. The retained positive map
supplies all kernel witnesses. This proves the exact68 projection.

Every positive x has a bare68 witness. Choose W=3^m>2x, use A=7 with
append rails4 and3, and put D=2x+7W. Choose t divisible by4 sufficiently
large that q=3^t is divisible by W and A+D<q. Split the ternary digits of
D into Boolean rails. Its top digit2 makes both read rails positive.
Take B=1 and C=(q-1)/8-1, which is positive and Boolean. These data give
a complete positive extension. No controller acceptance is asserted here.

## 2. Shared controller schedules and exact carry meaning

Use the existing zero-code controller on labels in order append0,append1,
read0,read1:

    3k_next=k-5a0+2a1-28d0+56d1, k0=0.                (2)

The helper relation F0+F1=7B gives

    -5F0+2F1-28F2+56F3
        =7*(2B-F0-4F2+8F3).                           (3)

For terminal carry0, compare

    2B+8F3 = F0+4F2.

Three products and two sums cost5, giving **73=38M+35A**. For terminal
carry7, add q to the right side:

    2B+8F3 = F0+4F2+q.                                (4)

This costs6, giving **74=38M+36A**. Both have19 equations and the same29
positive witnesses. Equation(3) shows that these are precisely the global
carry identities with endpoints0 and7. Reducing successive prefixes modulo3
recovers every integral intermediate carry; no preferred-state subgraph is
assumed.

A fixed affine input I=cx+d uses one product and one sum, adding one operation
to the74 source. The literal75 schedule is also audited. For a full ordinary
FIFO interpretation one may take c>=1,d>=0. The loading obstruction below
also applies to any fixed integer d on sufficiently large positive inputs.

## 3. Entire raw-read, coded-append carry graph

Group time into two-trit blocks. A raw read block is any integer R in0,...,8,
with Boolean rail words R0,R1 in{0,1,3,4} satisfying R0+R1=R. An append00
block has rail words(0,0); append12 has either(4,3) or(3,4). Their weighted
append contributions in(2) are respectively0,-14,-7.

At every block boundary the carry is7s with

    s in {-2,-1,0,1,2,3}.                              (5)

This is an invariant, not a selected subgraph. Initially s=0. An integral
two-step transition has

    s_next=(s-4R0+8R1-z)/9, z in{0,1,2},               (6)

where z encodes the three append-rail possibilities. Its numerator lies
between-20 and35. An integral quotient therefore lies in[-2,3]. Also an
integral next carry is divisible by7 because7 is coprime to9. This proves(5).

Exhausting these six states and the actual allowed rail words gives31
edges; all six states are reachable. This finite enumeration is the full
controller graph for arbitrary raw reads and coded appends. Forget outputs
and determinize with respect to the raw base-nine read digit. Apart from
the empty rejecting set, the reachable carry subsets are exactly:

| Carry subset | A read prefix reaching it | A forbidden next raw digit |
| --- | --- | --- |
| {0} | empty | 1 |
| {-14,14} | 4 | 3 |
| {-7,21} | 5 | 0 |
| {14} | 7 | 2 |
| {7} | 4,1 | 2 |
| {7,14} | 4,7 | 2 |

Prefixes are low first. The checker exhausts all48 rail choices at each
boundary state and all9 successor digits of each reachable subset, so the
table includes arbitrary output choices and every split of a scalar1.

## 4. The zero-carry endpoint is empty

A>0, and its last nonzero block is12. Let h be the position of its highest
nonzero trit; h is odd and that trit is2. Since I<W and D=I+WA, the highest
read trit is likewise2 at position h+m, where W=3^m. No carry between I
and WA can change it. Every append trit at that position or later is0.
The complete block containing that last nonzero read has append00.

If m is even, its read block is12, integer7. Its two possible read-rail
contributions to(2) are140 and56. To end that block at carry0, its initial
carry would have to be-140 or-56, both excluded by(5). If m is odd, the
last read block is20, integer2, with contribution28, requiring carry-28,
also excluded.

All later blocks, if any, read00 and append00. Such a block divides its
carry by9, so it can end at0 only if it began at0. The desired terminal
carry0 therefore produces the preceding contradiction. This proves that
the entire73 relation is empty for every positive ordinary input and every
width, including odd widths and arbitrary raw initial trits.

## 5. Terminal7 is possible, but requires even width

At terminal carry7, a trailing00/00 block would require preceding carry63,
contrary to(5). Thus the last nonzero read block is the final block. If m
were odd, that read20/append00 block would need initial carry63-28=35,
also impossible. Consequently every74 witness has **m even**.

For even m, read12/append00 can start and end at carry7, using read rails
(4,3). Thus this endpoint avoids Section4's contradiction. A concrete
full positive outer witness has x=2, W=9, t=12; its twelve rail labels,
all six field values, positive slacks and exact endpoint are recorded in
the receipt. The general positive kernel map supplies all remaining
coordinates. This is a nonempty exact relation.

It still has no proved universal halting interpretation. After an entire
initial sweep, the even width makes every subsequently read block coded.
At most one additional coded block is needed to enter the familiar
Rule110 scan states{0,7,14}: the extra coded edges are
-14/read7/append0->14, -7/read7/append7->14 and21/read7/append7->7.
If
an erasing tail occurs wholly after that sweep, its preceding queue is
all logical1 blocks and its carry is7. That condition has not been proved
equivalent to halting on ordinary input. The raw first sweep cannot be
silently replaced by a precompiled code word.

## 6. No fixed affine prefix repairs the raw-input domain

The subset table supplies a stronger uniform loading obstruction. Fix any
c>0 and integer d. There is a positive x, with I=cx+d>0, for which **no**
controller path with coded appends can read the initial queue, regardless
of its endpoint or available padding. In fact infinitely many such x exist.

Choose n so g=gcd(c,9^n) already contains the full3-primary part of c, hence
c/g is coprime to9. Choose any x0>0 with I0=cx0+d>0, and process its first
n raw base-nine digits in the subset automaton. If the resulting subset
is empty, all sufficiently large x preserving that prefix already fail.
Otherwise choose its forbidden next digit b from the table.

Changing x by multiples of9^n/g preserves I modulo9^n. The quotient
floor(I/9^n) changes modulo9 by multiples of c/g, a unit modulo9. Hence
one can choose an increment making the next digit exactly b. Further
increments by9^(n+1)/g preserve all these n+1 digits and make x and I
arbitrarily large. In particular choose I>=9^(n+1).

For any width W>I, those first2(n+1) trits are read directly from the
initial queue, before any appended trit can return. Their prefix has no
path in the complete graph from Section3. No choice of later labels,
width, endpoint or padding can fix this failure.

Therefore every fixed affine-input version of this particular controller
and append filter misses infinitely many positive inputs. This family
cannot even represent the set of all positive integers, and so cannot
be a universal representation family with program data supplied only by
those affine input numerals. The conclusion concerns this fixed controller;
it does not claim that no other small controller or paid loading phase can
use the filter.

## 7. Evidence and status

The [checker](input_bridge_append_code74.py) audits the full68/73/74/75
instruction schedules and every independent source residual. It verifies
the helper filter over21,343 positive Boolean pairs, computes all31 raw
block edges and the complete reachable subset automaton, and implements
the constructive forbidden-input argument for840 affine maps, including
negative offsets at sufficiently large positive inputs. It checks an
actual positive terminal7 outer witness and its complete Boolean packing.

The infinite assertions are the invariant, last-read argument, and modular
construction above. Finite tests do not substitute for those proofs. The
positive Pell extension remains parametric. Default execution compares the
saved [receipt](input_bridge_append_code74.json). Independent full proof,
source, and default-replay review passed, including the three transient
coded edges before the Rule110 state subgraph.
