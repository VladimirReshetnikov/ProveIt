# Fixing the idle selector: a57-operation FIFO with a regular input language

One nonabsorbing boundary of the [binary63 controller](native_binary_three_row_fifo58.md)
has an exact classification. If its coefficients satisfy a=b!=0 and c=-b,
the controller fixes the00-row selector to one numeral T. For positive odd T,
the resulting complete positive FIFO predicate costs **57=30M+27A**, with
**25 positive witnesses and17 equations**. Its ordinary positive inputs are
exactly

    {x>0 : 2x+T+1 is a power of two} union E_T,             (1)

where E_T is an effectively computable finite set contained in2x<T.
Thus this cheaper component has a regular, decidable input language; it is
not a complete universal certificate. The finite exception is essential:
T=9 accepts x=1 even though2x+T+1=12 is not a power of two.

## 1. Exact arithmetic specialization and operation count

Write F0,F1,F2 for binary row selectors00,01,10, A=F1,D=F2, and
I=2x. The established FIFO58 theorem supplies

    F0+A+D+1=q, D=I+WA, q=2^t, W=2^m,
    0<I<W, t>m, all three fields positive,
    one-hot row selection at every time, F0 odd.

For a=b!=0,c=-b, the nonabsorbing controller equality is

    bA+bD-bq=g.

The checksum reduces it exactly to `-b(F0+1)=g`. Unless
`T=-g/b-1` is a positive odd integer, the controller has no witnesses.
Otherwise replace the positive F0 coordinate by the fixed numeral T.
This is a compiler-parameter simplification, not a division of a varying
input or witness. A converse restores F0=T immediately.

Fold the checksum's two fixed constants before evaluation:

    F1+F2+(T+1)=q.

This uses two additions instead of the original three. The packing remains
`r=T+q(F1+qF2)`, costing2M+2A. All other kernel, width, and ordinary-input
instructions are unchanged. Hence the entire component costs57=30M+27A,
with25 supplied positive coordinates and17 comparisons. T and T+1 are
fixed numerals, and every multiplication by a numeral is still paid.

Soundness and the full strictly positive Pell converse follow from the
FIFO58 theorem with F0=T. No kernel witness is dropped by relying on a
finite run experiment. The [literal checker](binary_fixed_idle_controller.py)
independently expands every residual and retains the strong auxiliary-norm
correction from that theorem.

## 2. The fixed row pattern gives an effective finite-width test

Fix W=2^m>I. At every time j for which the jth bit of T is1, the row must
be00: its read bit must be0, and it appends0. At every other time the row
is either01 or10, so the visited cell is flipped. These instructions
uniquely determine the entire run from its initial queue I, or reject it
when a prescribed00 reads1.

Put h=bit_length(T). Simulate the first h steps, checking those forced
idle rows. Afterward every visit flips a bit. Exactly m visits complement
the entire queue, and2m visits restore it, including head position. The
zero queue is therefore reachable after the prescribed prefix if and only
if it appears among the next2m states, including the prefix endpoint.

If that first zero has no positive append stream yet, continue one whole
2m cycle. A zero queue first becomes all ones and then returns to zero,
using01 and10, while adding no00 rows. This supplies positive A and t>m.
The original I>0 already supplies positive D, and F0=T>0. Thus the test
is exact for the full FIFO interface, including all three positive fields.
No zero padding has been appended: the extra cycle flips and restores
every cell and is compatible with this particular nonabsorbing controller.

## 3. Every sufficiently wide queue forces a translated power of two

Suppose W>T. All prescribed idle rows occur during the first sweep of m
cells. Such a sweep is possible precisely when `I AND T=0`. Its output
queue is

    J=W-1-I-T=W-S, S=I+T+1.                            (2)

Here0<=J<W, and S is even because I is even and T is odd. Every later
visit flips a cell. Write the number of further steps as km+r, where
0<=r<m. Before the last partial sweep the queue is J when k is even,
and its bitwise complement when k is odd. That partial sweep ends at zero
if and only if its starting queue has exactly the first r cells equal to1,
namely the low-r repunit2^r-1. Therefore either

    J=2^r-1, giving S=W+1-2^r,
    or J=W-2^r, giving S=2^r.                          (3)

In the first case r>=1 would make S odd. The only remaining first case
is r=0 and S=W, itself a power of two. The second case already says S is
a power of two. This proves that every accepted input with W>T belongs
to the first set in(1). It also explains why fixing the00 field removes
the sustained state choices available in the general three-row simulator.

## 4. Every translated power has a full positive extension

Conversely suppose S=I+T+1=2^r and I=2x>0. Since T<S,
I=(2^r-1)-T is the r-bit complement of T, so `I AND T=0`.
Choose a power W=2^m>S. In the first sweep follow the prescribed T;
the resulting queue J=W-S is nonzero. The second full sweep complements
J to S-1=2^r-1. The next r steps erase those ones, ending at zero at

    t=2m+r.

Only the first sweep uses00, at exactly the positions of T. The nonzero
J supplies01, and the positive initial input supplies10. The first row
is00 because T is odd and I even. All fields are positive, and the exact
FIFO58 converse supplies the full positive arithmetic witnesses for the
57-operation specialized source.

Any remaining accepted input must use a width W<=T, hence2x<W<=T.
There are only finitely many such x and powers W. Apply Section2 to each
pair and discard inputs already in the translated-power family to compute
E_T. This proves both directions of(1), with an effective exception set.

For T=9 the values

    x=1, W=4, q=32, A=4, D=18, F0=9

satisfy all scalar typing, width, and transport conditions. They give the
announced finite exception. No claim that E_T is always empty is valid.

The infinite part is also regular as a language of binary input digits:
write d=(T+1)/2. Its elements are2^n-d>0. For sufficiently large n they
have a run of leading ones followed by one fixed suffix; finitely many
smaller words and the finite set E_T preserve regularity. This is not
merely a finite search exclusion of universality.

## 5. Verification and remaining scope

The checker compares the finite-width dynamical decision with an independent
scalar computation of `A=(2^t-I-T-1)/(W+1)`, including all pairwise binary
disjointness conditions. It checks the complete classifier on positive odd
T<=63 and1<=x<=80, tests the explicit infinite-family construction, and
records the actual small-width exceptions. Its source audit verifies the
57-operation gate list and all17 independent residuals symbolically.

The proofs establish the unbounded language classification; the finite
tests corroborate the implementation. The result applies only to the stated
fixed-idle coefficient specialization. Other nonabsorbing coefficients,
additional constraints, and different terminal queues remain outside it.
The established complete universal comparison bound remains75.

Independent proof/source review and default replay passed. A separate
circular-array implementation with an explicit head and visited-state
termination checked64,128 fixed-width cases and16,256 complete input
classifications for odd T<=255 and x<=127, independently checking every
accepted history's transport and checksum. It confirmed the finite
exceptions and the full flip-cycle extension used to obtain positive A.

From the repository root with the pinned verification dependencies installed:

    python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/binary_fixed_idle_controller.py
