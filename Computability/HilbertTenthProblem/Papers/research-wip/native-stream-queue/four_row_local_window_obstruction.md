# Row-local windows cannot certify the simulator's finite control

There is a fixed four-state source machine for which **no fixed window width
of physical row labels** can certify the
[four-row block simulator](four_row_queue_block_simulator.md), even on its
valid encoded input format. For every window width K, an explicitly rejecting
coded input has a genuine accepting-endpoint four-row FIFO trace whose every
K-window occurs at the identical time position in a truly accepting trace.
The accepting comparisons have the same width and duration. The prefix and
suffix windows also agree simultaneously with one accepting trace. Section6
gives the same obstruction for the binary three-row simulator.

This is a precise obstruction to replacing the finite controller by a fixed
collection of row-only local tests, including fixed block filters and
position-dependent tests. It is not an obstruction to regular-language
recognition with extra state, matrix products, nonlocal constraints, or tests
that themselves depend on the varying numerical input. Indeed two additions
and one positive witness separate this particular parity fixture. No lower
bound for all arithmetic controller encodings is claimed.

## 1. One fixed copying source distinguishes parity

Use source alphabet `{0,1,E}`, numbered0,1,2, and four states:

    even (initial), odd, accept, dead.

In even or odd state, reading0 copies0 and preserves the state; reading1
copies1 and toggles even/odd. Reading E copies E and enters accept from odd,
or dead from even. Accept and dead both copy every symbol forever, preserving
their respective states. Thus the source word

    0^N E                                                (1)

never accepts, while changing exactly one of those N zeros to1 produces
acceptance on the first visit to E. The source and its transition table are
fixed independently of N and K.

Use the simulator's fixed code `beta(a)=2a` in k=4 low-first binary digits.
The wrapper guard and delimiter are symbols3 and4. The initial physical
word consists of C(a)=2beta(a), each followed by four zero work cells,
including the final wrapper guard and delimiter. There are N+3 blocks, so

    m=2k(N+3), k=4.                                      (2)

All these words satisfy the same valid simulator input format.

## 2. A false cleanup trace and nearby accepting traces

For (1), fabricate a physical trace T* by using the same copying protocol
but pretending that the source accepts at E even in the even state. It
performs one complete COMPUTE/SKIP/PREPARE cycle, the ERASE sweep, and the
two final zero steps. This is not a valid path of the intended controller;
it is a completely valid path of the four physical rows00,01,12,20.
It ends with the queue zero and uses all four rows.

For `0<=i<N`, let Ti be the genuine accepting simulator trace obtained by
changing data cell i to1. All these traces, including T*, have exactly

    t=3m+k+2                                             (3)

steps. State changes do not otherwise affect physical output: the source
always copies its input, and all Ti halt at their E. Thus their physical
rows differ only where the changed data code is processed.

Use zero-based physical time. Since beta(1) has its sole1 at code offset1,
Ti differs from T* at exactly the four positions

    S_i={2ki+1, 2ki+k+1, m+k+2ki+1, 2m+k+2ki+1}.          (4)

These are respectively its COMPUTE read, COMPUTE write, PREPARE read and
ERASE read. The row at each of these positions is00 in T*, and respectively
20,01,12,20 in Ti. Formula(4) is independent of any inference about finite
windows; it follows directly from the literal simulator phases.

The sets S_i are pairwise disjoint. Their last two points lie in separate
sweep intervals. Within the COMPUTE interval, read positions are1 modulo2k
and write positions are k+1 modulo2k, so those positions cannot collide.
Every index also lies in the duration range specified by(2)--(3).

## 3. Every fixed window has an accepting comparison

Fix any integer K>=1, and choose `N=2K+1`. Any K consecutive time positions
intersect at most K of the pairwise disjoint nonempty sets S_i. Some index i
is therefore untouched, and its accepting trace Ti agrees with T* on that
entire window, at the **same** position. This applies to cyclic windows
crossing the end/start boundary as well as ordinary linear windows.

The union of the first K and last K positions intersects at most2K sets
S_i. Hence another choice of i makes Ti agree with **both** boundary windows
simultaneously. All compared traces have identical m,t and therefore
identical W=3^m and q=3^t.

Formally, consider a proposed controller certificate that is a conjunction
of predicates on length-at-most-K windows of the physical row word, plus
any predicate on its first/last K rows. A local predicate may depend on its
time position, the common q,W, and fixed program numerals. Assume the
certificate accepts every genuine accepting simulator trace in this format.
Each local predicate must then accept the corresponding window of T*, using
the matching Ti. The boundary predicate must accept too, using the single
Ti that agrees at both ends. Thus the conjunction accepts T* although its
coded source input rejects.

Fixed block alignment and fixed periodic masks do not avoid the result:
positions and geometry agree in every comparison. A varying-input predicate,
extra existential state/history tracks, a global relation among different
windows, or a product of transition matrices is outside this conjunction
model. Such additions need their own arithmetic accounting.

## 4. The false trace really extends to the positive FIFO66 component

This is not merely an abstract controller word with unpaid stream bounds.
Every trace just constructed starts at its actual encoded integer I, ends
at zero, and has even m,t. Its first row is00 and every row occurs. Write
F0,F1,F2,F3 for the four row indicators and put G=F1+F2 and H=sum Fi.
Then

    D=F2+2F3, A=F1+2F2,
    D=I+WA, 0<I<W, I even,
    H=(q-1)/2, G even, H even, Fi>0, G>0.                 (5)

The two final zero steps also give `D+A<q`. Consequently
`x=I/2`, width_beta=W-I, and L=q/W are strictly positive. Equation(5)
satisfies the exact projection of
[the established FIFO66 source](native_four_row_fifo66.md), including its
five-field parity condition. Its positive converse supplies all26 positive
witnesses; astronomical Pell coordinates are provided by that theorem,
not numerically materialized here.

The changed positive input for Ti is precisely

    x_i=x_*+3^(2ki+1).                                   (6)

Thus the ordinary parameter of FIFO66 is different in the comparisons,
whereas q,W and the local row patterns agree. This is why the obstruction
is explicitly row-only and does not claim that arbitrary input-dependent
arithmetic predicates agree. The initial coding of the source word is still
the actual supplied block code, not a new ordinary-input loader theorem.

## 5. A cheap nonlocal parity test separates this example

The source E, wrapper guard and delimiter have code populations1,2,1.
During the sole COMPUTE sweep they contribute four01 rows in total.
Each data1 contributes one more, and no other phase uses01. Therefore

    popcount_3(F1)=4+number_of_data_ones.                  (7)

Here popcount_3 counts1 trits of this Boolean ternary word. Since every
power of3 is odd, F1 has the same parity as(7). The false trace has F1
even; every comparison trace Ti has F1 odd and larger than1.

Supply a new positive witness v and compute

    twice_v=v+v; odd_v=twice_v+1; compare F1=odd_v.         (8)

This is exactly two additions, one comparison and one positive witness.
It separates the displayed traces, with v=(F1-1)/2>0 on Ti. The resulting
68-operation extension of FIFO66 is just a paid odd-F1 restriction; it is
not an encoding of the full simulator protocol or an arbitrary source
controller. In particular the obstruction in Section3 is not an arithmetic
lower bound: genuinely nonlocal tests can cost very little.

The useful conclusion is narrower. A codebook or a collection of bounded
row patterns does not by itself recover the unbounded propagation of even
versus odd state across a long run of copied blank cells. A proposed cheap
controller must pay for some mechanism that retains that information.

## 6. The binary three-row corollary

Use the same source and code beta in the binary variant of the simulator,
whose physical rows are00,01,10. Its active blocks are beta itself, rather
than2beta. The same words have width m=2k(N+3), but no PREPARE sweep occurs:

    t=2m+k+2, W=2^m, q=2^t.                              (9)

The false trace again uses the copying protocol with a false acceptance
decision at E. Each comparison changes exactly one data0 to1. Its exact
support of differences is now

    S_i={2ki+1, 2ki+k+1, m+k+2ki+1},                     (10)

with changed rows10,01,10. These three positions are the COMPUTE read,
COMPUTE write and ERASE read. The supports are pairwise disjoint for the
same interval and residue reasons as(4). Consequently N=2K+1 proves every
same-position linear/cyclic window comparison and the simultaneous boundary
comparison from Section3, with precisely the same scope restrictions.

In this binary radix, write F0,F1,F2 for indicators of00,01,10. All three
are positive, the first row is00, and

    D=F2, A=F1, F0+F1+F2=q-1, F0 odd,
    D=I+WA, 0<I<W, I even, D+A<q.                       (11)

The first physical digit is0, so I is even in radix2. Thus x=I/2>0,
width_beta=W-I>0 and L=q/W>0 meet the exact trace projection of
[the binary FIFO58 component](native_binary_three_row_fifo58.md).
Its positive converse extends these scalar data to the arithmetic component.
The input change is now

    x_i=x_*+2^(2ki).                                    (12)

The varying coded input remains excluded from the local predicates. Neither
version supplies an ordinary source-input loader or pays for its controller.

The two-addition guard(8) must **not** be transferred to this corollary:
F1 is numerically even for both kinds of binary trace, because its first
bit is0. Although the population of01 rows still has the parity in(7), its
extraction from a radix2 selector has not been paid for here.

## 7. Evidence and boundary

The [checker](four_row_local_window_obstruction.py) uses the literal compiled
simulator to construct the bad and good traces, then independently verifies
all four ternary or three binary difference positions, their disjointness,
and the local-window comparisons for K=1,...,32 in each radix. It exhausts
the intended physical controller on each rejecting initial word to confirm
rejection. The finite FIFO coordinates, field parity, scalar joint bound
and the ternary two-addition parity guard are checked exactly. The positive
Pell extensions are inherited from the component theorems.

Independent review of the ternary proof and source found no issues, and a
fresh default replay passed. A second implementation constructed the physical
sweeps directly, without calling Compiler.step, and matched230 complete
traces for N=1,...,20. A further independent review checked the ternary
support proof. Separate review of the binary extension likewise found no
issues; direct COMPUTE/SKIP/ERASE/finish sweeps independently matched230
binary traces for N=1,...,20 and verified their FIFO58 scalar projection.
These bounded audits support, rather than replace, the proof; the Pell
converse is a dependency on the respective arithmetic component theorem.

The theorem for arbitrary K is the support argument above. Finite checks
are supplementary, and no universal certificate below75 follows.
