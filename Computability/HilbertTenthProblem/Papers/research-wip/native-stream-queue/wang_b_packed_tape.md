# A uniform packed Wang tape with chronological reads and marks

One complete native AND certifies arbitrarily many rows of a bounded
binary tape, a positive one-hot head in every row, the current read,
a Boolean mark choice, and the chronological tape updates. The raw
certificate costs **139=63M+76A operations**, with **18 comparisons**
and **31 positive existential witnesses**. Its single sum-of-squares
polynomial costs **192=81M+111A**, of total degree **at most232**.
These counts do not depend on the number of rows.

The [source](wang_b_packed_tape.py) and [receipt](wang_b_packed_tape.json)
implement a complete batch relation extending the
[scalar Wang tape component](wang_b_single_and_tape.md). Heads are
independently chosen in each row: head movements and instruction/control
selection are not imposed. There is no whole universal Wang-program
certificate, TM input coding or improved universal bound in this packet.

The positive parameters are `initial_tape_hat=T_0+1` and
`final_tape_hat=T_t+1`, allowing empty initial or final tape words.
At a zero, some positive duration t and a dyadic cell radix decode
all supplied histories as a sequence

    H_i=2^(j_i)>0, I_i in {0,1}, C_i=T_i AND H_i,
    T_(i+1)=T_i+I_i*(H_i-C_i),       0<=i<t.           (1)

Thus a marked row writes1 at its head and an unmarked row retains
the tape. All reads use the tape in that row. Conversely, every finite
nonempty sequence satisfying(1) admits all the positive witnesses,
including a complete positive native Pell extension. No a priori bound
on the head positions or tape words is needed; a sufficiently large
existential dyadic height supplies the finite window.

## 1. Positive coordinates and paid radix

Besides the22 positive auxiliaries of prescribed AND64, supply

    height_slack, global_bound,
    T_hat,G_hat,C_hat,I_hat,N_hat,W_hat,V_hat > 0.

There are nine outer witnesses and31 in total. Lowercase hats below
represent whole packed numbers, not arrays of additional variables.
Decode the six nonnegative words

    T=T_hat-1, G=G_hat-1, C=C_hat-1,
    I=I_hat-1, W=W_hat-1, V=V_hat-1.

Compute

    D=initial_tape_hat+final_tape_hat+height_slack,
    B=8D, J=I_hat+N_hat-2,
    Pminus=(B-1)*J, P=Pminus+1,
    H=G+J, Mmark=(B-1)*I, Mrange=(D-1)*J.             (2)

Before any equation, D>=3, B>=24, J>=0, P>=1 and every displayed
word is nonnegative. In particular J=I+(N_hat-1) gives I<=J without
requiring any bit typing. This last relation prevents the mark mask
from overflowing its packed lane before the AND has decoded selectors.
The all-mark case I=J is permitted by N_hat=1.

Pay one global comparison

    J+T_hat+G_hat+C_hat+I_hat+W_hat+V_hat
       +global_bound=P.                              (3)

At any zero, J cannot be0: then P=1, while the left side is at least7.
Thus J>=1 and P>=B. Equation(3) gives strict bounds below P for
T,G,C,I,W,V and also H=G+J. Independently of any bit interpretation,

    0<=Mmark< P, 0<=Mrange<P, 0<B<=P.                 (4)

Indeed I<=J and(B-1)J=P-1; also D-1<B-1. No positive coordinate
for the head word H is supplied: its positivity in each row is proved
by the bounded shifted representation H=G+J after radix typing.

## 2. Seven scalar lanes and two reserved radix lanes

Use the following unpadded words in one complete prescribed-scale
[AND64 component](native_binary_masked_selection63.md):

| P-lane | First input | Second input | Output |
|---:|---|---|---|
|0|H|G|0|
|1|T|H|C|
|2|H|Mmark|W|
|3|C|Mmark|V|
|4|I|J|I|
|5|T|Mrange|T|
|6|G|Mrange|G|
|7 and8 together|B|B-1|0|

Precisely, compute

    A=H+PT+P²H+P³C+P⁴I+P⁵T+P⁶G+P⁷B,
    M=G+PH+P²Mmark+P³Mmark+P⁴J
        +P⁵Mrange+P⁶Mrange+P⁷(B-1),
    Z=PC+P²W+P³V+P⁴I+P⁵T+P⁶G,
    Scale=P^9.                                       (5)

Horner packs and a paid multiplication chain for P^9 evaluate(5).
The native ports are literally16A+12,16M+10,16Z+8 and16Scale;
no extra positive wrappers are supplied. All these inputs are positive
before any equation, since the unpadded words are nonnegative.

The complete native theorem first makes P^9 dyadic, hence P dyadic,
and gives A AND M=Z. The scalar bounds(3)--(4) already make all seven
low lanes canonical. J<P also follows from(3). The radix values B and
B-1 fit in two reserved lanes even when B=P; reserving only one lane
would not cover duration1. Therefore unique splitting gives every
row of the table as an exact scalar AND relation. In particular

    B AND(B-1)=0.

Since B>0, B is a power of two, and D=B/8 is a power of two as well.
The literal repunit equation P=(B-1)J+1, J>=1, and dyadic P give

    P=B^t, J=1+B+...+B^(t-1), t>=1.                  (6)

This uses the elementary divisibility criterion
2^a-1 divides2^b-1 iff a divides b. No independent unpaid duration
or radix predicate has been assumed.

## 3. Head positivity, selection and reads in every row

Now write every number below P in canonical base-B digits. The
selector lane I AND J=I and(6) give exactly digits I_i in{0,1}.
The range lanes give

    0<=T_i,G_i<D,

because(D-1)J is a run of D-1 all-one bits inside every B-cell.
Since G_i+1<=D<B, adding J causes no carries. Thus H=G+J has digits
H_i=G_i+1, each strictly positive. The head lane H AND G=0 now gives

    H_i AND(H_i-1)=0, 1<=H_i<=D,

so H_i is exactly a power of two for every row, including rows in
which the tape is empty. Zero head rows cannot be hidden by borrowing.

The read lane yields C_i=T_i AND H_i, hence C_i is0 or H_i and
0<=C_i<D. The mark mask has a full B-cell of ones exactly when I_i=1.
The two selected-product lanes therefore give

    W_i=I_i H_i, V_i=I_i C_i.                         (7)

Every selected output is identified by its own canonical packed lane.
This uses no multiplication of two unbounded histories as a substitute
for a digitwise product. In particular W_i>=V_i. Both inputs to each
native lane are nonnegative even before the read relation is known;
the source does not place a potentially negative H-C into an untyped
packed lane.

## 4. Paid chronological tape transport

The final outer comparison is the exact folded version of

    B*(T+W-V)+T_0 = T+P*T_t.                          (8)

The source uses the supplied positive endpoint hats and reuses Pminus:

    left = B*(T+W-V)+initial_tape_hat,
    right = T+P*final_tape_hat-Pminus,
    left=right.                                      (9)

This costs2M+5A, including all subtractions. There is no omitted
unhat endpoint operation.

From(7), the packed quantity T+W-V has digits

    U_i=T_i+I_i(H_i-C_i),
    0<=U_i<=2D-1<B.                                  (10)

There is neither borrowing nor a carry between cells: W_i>=V_i and
the strict radix margin holds in every row. Also T_0,T_t<D by(2).
The unique base-B expansions in(8) now force the initial digit T_0,
then U_i=T_(i+1) for i<t-1, and U_(t-1)=T_t at the top. This proves
the full chronological tape semantics(1), not merely a relation between
the initial and final union of marked bits.

Heads may move to unrelated cells between rows in this batch relation.
Constraining those choices to left/right/no-move instructions, selecting
a finite program instruction and proving its jump targets require an
additional controller/history construction. Equation(8) alone does not
supply those obligations.

## 5. Full positive converse at arbitrary finite duration

Fix any nonempty finite sequence satisfying(1), with arbitrary finite
nonnegative tapes, positive power-of-two heads and Boolean mark choices.
Choose a power of two D strictly greater than every tape and head and
than initial_tape_hat+final_tape_hat. Set

    height_slack=D-initial_tape_hat-final_tape_hat>0,
    B=8D, P=B^t, J=sum_(i<t)B^i.

Pack T_i,H_i-1,C_i,I_i,I_iH_i,I_iC_i to obtain T,G,C,I,W,V, and
supply each hat as its word plus1. Set

    N_hat=sum_(i<t)(1-I_i)B^i+1.

This makes the computed J in(2) exactly the repunit, including all-mark
and all-read-only runs. Every supplied hat is strictly positive, even
when its entire decoded history is zero.

Choose global_bound from(3). It is strictly positive with a uniform
margin. The digit bounds T_i,G_i,C_i,V_i<=D-1, W_i<=D and I_i<=1 give

    T+G+C+I+W+V <= (5D-3)J.

Consequently

    global_bound = P-J-(T+G+C+I+W+V)-6
                 >= (3D+1)J-5 > 0.                 (11)

Every lane relation in Section2 holds, and all packed inputs lie below
the dyadic scale P^9. The complete prescribed-AND converse therefore
supplies all22 positive native auxiliaries, including both ratio slacks,
the strong norm and the index/scale bounds. Equation(8) holds by the
assumed chronological sequence. This supplies every witness and proves
completeness for arbitrary positive duration, without numerical
materialization of enormous Pell coordinates.

## 6. Why a positive whole head word is insufficient

A tempting shortcut is to assume only 0<J<H<P and impose
H AND(H-J)=0. It does not imply a positive head in each row. At any
dyadic B>=4, take a two-row scale and

    J=B+1, H=2B, G=H-J=B-1.

Then H AND G=0, but the head digits are(0,2): the first row has no head.
Subtracting J borrowed from the second row. This remains a counterexample
at every radix admitted by the present construction. The G-range lane
excludes it, since its low digit B-1 exceeds D-1 when B=8D.
The checker retains eight concrete base cases for this local obstruction;
they are not zeros of the corrected batch certificate.

## 7. Literal arithmetic, degree and evidence

The wrapper costs75=30M+45A, including all packs, range masks, the
positive global bound and transport. It adds this to exactly64 native
AND gates,33M+31A, yielding139=63M+76A. The only outer comparisons
are(3) and(9), in addition to the16 native comparisons. Thus the18-term
SOS adds18M+35A and costs192=81M+111A. All fixed multiplications,
including B=8D and the four native padding multiplications, are charged.
Identical emitted expressions are reused; additions of zero and products
by one are not emitted as operations.

Conservative degree propagation assigns degree one to both parameters
and all31 positive witnesses. D,B,J have degree at most1, P at most2,
and P^9 at most18. The native first-norm residual has degree at most116,
dominating the other propagated residual bounds. The SOS consequently
has total degree at most232. No exact-degree or optimality claim is made.

The source checks384 independently assembled complete residual/SOS
identities,192 signed, against the canonical AND64 source with explicit
packed inputs. It separately constructs216 genuine chronological outer
paths of lengths1 through9, including empty tapes, all-read-only runs,
all-mark runs and repeated/idempotent marks. Another576 independent
canonical-digit tests check the transport iff, and eight local cases
check the zero-head borrowing obstruction. Finite outer paths do not
claim to be full numerical native Pell zeros; the complete native
extension is supplied by the theorem used in Section5.

```sh
python3 wang_b_packed_tape.py
```

Author receipt generation and fresh default replay pass. Independent
full proof/source review and a fresh default replay pass without findings.
That review separately checked192 complete residual/SOS identities,
96 signed, using an independent literal executor. It also packed96
physical set-of-cells Wang prefixes containing639 steps, including49
prefixes that visit negative cells, without using the author's path
helper. Every paid outer comparison and joined-AND/range identity held
after a fresh positive translation and choice of radix. Those finite
paths are outer fixtures, not expanded full native Pell zeros. All four
local links resolve.

Root full proof/source review and a fresh default replay also pass without
findings. The scope remains chronological tape read/mark transport; head
motion, instruction control and the universal input interface are not
included in this192-operation polynomial.
