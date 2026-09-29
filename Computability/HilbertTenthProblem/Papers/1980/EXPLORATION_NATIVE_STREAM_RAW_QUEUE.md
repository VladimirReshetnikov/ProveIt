# Native ternary streams eliminate the queue-content histories

The constant-length queue from
[the13-operation delayed-loader component](EXPLORATION_DELAYED_BLANK_RAW_QUEUE.md)
has a simpler stream interface. Record the removed and appended trits directly
in base three, rather than at a wider time radix. Its two queue transports
then cost four operations, and its raw initialization costs two. This gives
a **6-operation conditional interface, 3M+3A**. Paying one common bound on
the two removed streams gives an **8-operation variant, 3M+5A**.

Both counts are exact arithmetic subtotals. They require externally supplied
power geometry and one synchronized finite-controller path on the four
native streams. Neither interface is a complete universal Diophantine
certificate. In particular, a controller compiler working at a wider radix
cannot be imported by silently changing the radix of those streams.

The earlier13-operation artifacts are unchanged. The new checker records
canonical-LF SHA256 hashes of that frozen proof, source and receipt.

## 1. A complete scalar FIFO lemma, including short histories

Let m>=1 and t>=0 be integers. Put W=3^m and q=3^t. Let

    0<=I<W,       0<=A<q,       0<=D<q.

Interpret I as a queue of exactly m trits, least significant trit first,
including any high zeros. Interpret A as a proposed sequence of exactly t
appended trits, and D as a proposed sequence of exactly t removed trits.
Every step removes one trit and appends the corresponding trit of A.
Then

    D=I+W*A                                                   (1)

holds if and only if D is the actual removed stream and the final queue
is all zeros.

To prove this, concatenate the m initial trits with the t appended trits.
The numerical value of that concatenation is I+W*A. Because I<W, its two
parts occupy disjoint positions and their addition has no carry. A FIFO
induction identifies the actual removed stream with the first t trits of
this concatenation, and the final queue with its remaining m trits. Thus
for the actual removed value Dactual and final value F,

    Dactual=(I+W*A) mod q,
    F=floor((I+W*A)/q),
    Dactual+q*F=I+W*A.                                      (2)

The stipulated bound D<q makes (1) equivalent to D=Dactual and F=0.
This proof does not assume that t>=m.

When t<m, equation(1) forces A=0 and I<q. These conditions say exactly
that all appended trits and all unread high initial trits are zero. A
short zero-reaching history can therefore be legitimate: the three-trit
queue `(1,0,0)` becomes all zero after reading its first trit and appending
zero once. When t=0, the bounds force A=D=0, and(1) holds precisely when
the initial queue is already zero. Both cases are included in the lemma.

The bound on D is essential. For m=2,t=1,I=3,A=1, the unbounded equation
admits D=12. Its lowest removed trit is zero, but the genuine one-step queue
ends with value4, not zero. Here D is not a one-trit word: D>=q=3. This is
a scoped counterexample to omitting the stream bound, not a counterexample
to either bounded interface below.

## 2. Two coordinates and the finite controller must share one history

The nine queue symbols are exactly the nine ordered pairs of trits. Let
the two initial coordinate values satisfy 0<=Ii<W, and let Di,Ai be
nonnegative integers below q. Suppose a single path in the fixed finite
controller starts in its prescribed initial state and, on step j, reads

    (digit_j(D0), digit_j(D1))

and appends

    (digit_j(A0), digit_j(A1)).

The two instances of (1) force this path to be an actual queue run. Indeed,
the scalar FIFO lemma identifies both claimed removed coordinates with
the corresponding coordinates of the current queue head. The pair is
therefore the exact current head symbol. The specified controller transition
emits the exact pair used by both scalar recurrences. Induction through the
common t steps recovers the whole queue and controller run, with final
coordinate values zero.

It would not suffice to give the two coordinates different lengths, different
control paths, or independently selected transitions. The controller-path
hypothesis refers to the SAME paired symbols and the SAME t positions.
The six/eight arithmetic schedules do not implement that hypothesis.

No Boolean-digit restriction is needed for the four native numbers: ordinary
base-three digits are already in{0,1,2}, and every coordinate pair is one of
the nine symbols. The controller must still enforce the meanings of marked
cells, delimiters, loading phases and ordinary work states. Those are
semantic transition restrictions, not automatic consequences of the trit
alphabet.

## 3. The six paid operations and their power hypotheses

Use the fixed delayed-loader queue, its canonical-input normalizer and its
accepting erase pass. Choose L=3^ell>x and set W=3L. Its initial queue is
the ell ordinary ternary digits of x followed by `#`. Consequently

    I0=x,        I1=L,        0<=I0,I1<W.

The complete six-operation source is

    W=3L,
    x+alpha=L, alpha>0,
    D0=x+W*A0,
    D1=L+W*A1.                                             (3)

The literal instructions are

| Register | Operation |
|---|---|
| Wcalc | 3*L |
| input_bound | x+alpha |
| shiftA0 | W*A0 |
| read0 | x+shiftA0 |
| shiftA1 | W*A1 |
| read1 | L+shiftA1 |

Equality comparisons are free. Thus the source has four equalities and
costs exactly3M+3A. There is no time radix R and no content history X0 or
X1 in this system. In particular, R=3W is not being computed for free;
it has disappeared because the streams are represented at their native
base three.

For the six-operation interface, require externally

    L=3^ell, q=3^t, ell,t>=0,
    0<=D0,D1<q, 0<=A0,A1,
    the synchronized t-step controller path of Section2.   (4)

The appended-stream bounds are then automatic: (3) gives W*Ai<=Di<q,
so Ai<q. The positivity convention may require all four streams to be
strictly positive; Section5 proves that every true accepting run supplies
that stronger domain. L, W and alpha are positive, while the external
input x may be zero.

In this particular interface the general lemma's short-history cases cannot
produce a solution. Since D1>=L=3^ell and D1<q=3^t, necessarily
t>=ell+1=m. This derives the required history length from the delimiter
coordinate rather than assuming it in the FIFO argument. In particular,
t=0 is impossible. The cases ell=0 and ell=1 are rejected by the actual
loader/normalizer, as proved for the preceding component; they are not
silently excluded from the arithmetic power hypothesis.

All of (4), except the bounds replaced in the next section, remains unpaid.
No equation in (3) alone proves a power of three or an arithmetic encoding
of the finite controller. The variable q need not occur in the six paid
instructions because its role there is precisely the external length bound.

## 4. An eight-operation version pays the joint stream bound

Replace the two external removed-stream bounds by one positive slack beta
and the equation

    D0+D1+beta=q, beta>0.                                  (5)

Computing D0+D1 and then adding beta costs two additions. With nonnegative
Di, (5) implies both Di<q, so the complete source (3),(5) costs exactly
**8=3M+5A**, with five equalities. The appended bounds follow as before.
The two power hypotheses and the common controller path are still external.

This strengthened bound does not change the accepted set. One general way
to see completeness is to extend any accepted all-zero queue by one more
zero transition. The inherited accepting control copies ordinary zero to
ordinary zero. All four stream integers stay unchanged, while the time
power grows from q to3q. Since D0,D1<q,

    D0+D1<=2(q-1)<3q,

and beta=3q-D0-D1 is positive. Arbitrarily many further zero transitions
are also permitted; they do not alter the input or either stream identity.
This is an actual controller extension, not uncounted arithmetic dilation
of the four words.

For the particular delayed-loader machine, even that extra step is
unnecessary. In every first-zero run the last removed symbol is exactly
`#=(0,1)`. Every earlier symbol has coordinate sum at most4. Therefore

    D0+D1 <= 3^(t-1)+4*sum_(j=0)^(t-2)3^j = 3^t-2.

Hence beta=q-D0-D1>=2 already. Any postacceptance zero extension preserves
this strict bound. The general extension argument remains useful when
composing a different zero-word machine, but no extension is required to
provide the present positive beta.

## 5. Full conditional ordinary-input equivalence and positivity

Fix a recursively enumerable set and the preceding fixed four-symbol work
machine, delayed loader, normalizer, bounded scan compiler and accepting
erasure. If x belongs to the set, choose ell large enough that the last raw
trit is zero and the canonical computation fits. The exact queue theorem
then supplies a finite genuine run to the all-zero word. Record its four
native streams. FIFO gives (3), the positive input slack is alpha=L-x,
and the preceding section supplies beta if (5) is used.

Every such run has all four stream integers strictly positive. The successful
delayed loader emits a marked first cell, whose first coordinate is positive;
the mandatory normalizer later reads it. Thus A0,D0 are positive, including
x=0. The loader emits a provisional delimiter and reads the original
delimiter, so A1,D1 are positive. Every stream is below its common q.
No per-row adapters are needed for zero trits, and the final zero coordinates
are literals rather than zero-valued positive existential variables.

Conversely, suppose the positive arithmetic coordinates satisfy (3), either
bound interface, the power hypotheses and the single fixed-controller path.
Section2 reconstructs an actual constant-length queue run from the raw
input, ending in the all-zero word. The loader cannot have erased a nonzero
high raw trit, and no rejecting loop or nonaccepting work scan can eliminate
the delimiter. The first all-zero event must therefore be the final erasure
after genuine machine acceptance. The preceding normalization and bounded
simulation theorem gives x in the represented set. Insufficient padding
can reject but cannot create acceptance.

This establishes the whole machine contract under the specified unpaid
controller and power predicates. It does not replace those predicates by
unwritten polynomial equations.

## 6. Why a wide-radix controller is not automatically reusable

The four new words are sums of trits times3^j. The earlier histories used
powers R^j, where R=3W. For example, a two-trit stream `(1,2)` has value7
in the new interface and1+2R in the old one. These are different supplied
integers, not two readings of the same value.

A compiler that places rule choices in separated native positions of a
large row radix can convolve them with fixed numeral coefficients. To use
such a compiler here, it must also establish the exact correspondence of
all four streams to that row encoding. Merely substituting R for3 in (3)
does not preserve the FIFO identity. Conversely, stacking native streams
at offsets depending on the variable history length makes the routing
coefficients depend on that length; they are not fixed compiler numerals.

These are obligations for a future complete compiler, not impossibility
claims. The present result removes the content-history transport and its
typing problem, while leaving the synchronized native finite-controller
encoding as the remaining central task. No complete count below75 or
lower bound on future certificates is asserted.

## 7. A scoped limitation of one fixed-code state stream

One particular shortcut is impossible: encode every arbitrary length-t word
over S state symbols as a single integer sum c(sj)*3^j, where the finitely
many signed integer codes have absolute value at most a fixed C. Every
such value has absolute value at most C*(3^t-1)/2, so there are at most
C*(3^t-1)+1 possible integers. If S>3, this is eventually smaller than
the S^t input words, irrespective of how large the fixed codes are. The
map therefore cannot be injective at every length.

For d scalar streams with fixed bounded codes the corresponding capacity
is O(3^(d*t)); representing all arbitrary state words injectively requires
S<=3^d. This is only a statement about that fixed positional representation.
A particular controller may allow far fewer than S^t state histories;
indeed its state path can be determined by its inputs. Extra witnesses,
different encodings, nonlinear tests and redundancy are outside the claim.
It is not a lower bound for arithmetic controller verification or for a
universal certificate.

## 8. Reproducible source, FIFO and machine checks

The companion `../verification/explore_native_stream_raw_queue.py` checks
both literal DAGs independently: six operations/four source equalities and
eight operations/five source equalities. Its scalar gate enumerates31,980
arbitrary (I,A,D,m,t) tuples for m=1,...,3 and t=0,...,3, comparing the exact
integer equation with an independent FIFO simulation. This includes39
t=0 cases and2,550 cases with t<m. It separately checks131,160 forward
queue runs for m=1,...,4 and t=0,...,6, including58 legitimate short
zero-reaching histories, and checks the explicit omitted-bound example.

The integration gate reuses all genuine accepting histories from the frozen
predecessor's exhaustive-loader and seven-client tests. It retains every
predecessor arithmetic check and independently rebuilds the four native
integers. For each of463 histories, totaling43,665 queue transitions, it
decodes the native digits and replays both the actual queue and the complete
finite controller from its initial state. It checks both stream identities,
the paired-symbol transitions, the exact zero endpoint, strict positivity,
the forced t>=m bound, the final-delimiter joint bound and a genuine accepted
zero extension. The longest tested history has188 transitions. All463
native first-coordinate words differ from their corresponding wide-radix
words, making the absence of a silent radix identification explicit.

The in-process test hooks used to collect those histories are restored in
a finally block; no predecessor file is edited. Its three frozen artifacts
are hashed with canonical LF normalization in the saved receipt. Default
execution requires and compares that receipt; `--write` regenerates it.
Finite tests corroborate the general proof and exact accounting. They do
not supply the missing arithmetic controller or giant Pell witnesses.
