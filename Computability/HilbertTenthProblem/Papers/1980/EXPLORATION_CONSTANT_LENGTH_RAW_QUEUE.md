# A constant-length raw queue with zero-word acceptance

For every recursively enumerable set of nonnegative integers, there is a
fixed finite-state queue machine on nine symbols with the following contract.
Every transition removes exactly one symbol and appends exactly one symbol.
With enough existential input padding, its queue reaches the all-zero word
exactly for accepted inputs. The queue never becomes physically empty.

The nine symbols are exactly the nine pairs of ternary digits, so the queue
still has two numerical content coordinates. Its raw initialization and both
complete numerical transports together cost **14 operations=7M+7A**. The
append words are multiplied by one constant queue-length scalar; there are
no coefficientwise products of independently supplied histories, no packed
length history, and no unpaid terminal-coordinate products.

This is an affirmative machine theorem and a conditional arithmetic component.
It does **not** supply an arithmetic encoding of the finite controller, power geometry, digit
masks, or a complete Pell certificate. In particular, 14 is not a universal
Diophantine certificate bound and is not to be added to a kernel while
silently dropping those remaining obligations.

## 1. Alphabet and the four-operation ordinary-input interface

The work-machine tape alphabet is `0,1,2,blank`. Encode its four ordinary
and four head-marked cells, and the delimiter, as follows:

| Tape symbol | Ordinary | Marked |
|---|---|---|
| 0 | (0,0) | (1,1) |
| 1 | (1,0) | (2,1) |
| 2 | (2,0) | (1,2) |
| blank | (0,2) | (2,2) |

The delimiter is `#=(0,1)`. These are all nine possible pairs, exactly once.
In particular, no separate invalid-pair restriction is necessary, although
the finite controller must still enforce the roles of marked cells and `#`.

Choose `L=3^ell>x`, initially with `ell>=1`, and put

    I1=5L,       W=9L,       R=3W,
    I0=x,        x+alpha=L, alpha>0.                        (1)

The symbolic initial queue is the `ell` little-endian ternary digits of x,
then one genuine blank, then `#`. Its physical length is `ell+2`,
its length marker is W, and its two coordinates are exactly

    I0=x,
    I1=2*3^ell+3^(ell+1)=5L.

Its first raw digit can be zero, one or two; none is mistaken for a blank
or a delimiter. The high raw zero padding becomes spare work space through
the normalizer below. All powers in this paragraph describe
the external power-geometry hypothesis; no exponentiation is counted as a
free arithmetic primitive.

The four actual instructions in (1) are

    I1=5*L; W=9*L; R=3*W; input_bound=x+alpha.

The comparison is `input_bound=L`, together
with the definitions of I1,W,R if those registers are supplied separately.
Thus this subtotal is three multiplications and one addition. If surrounding
geometry proves R divides a power of three, (1) proves L is a power of
three. That surrounding divisibility condition is not among the four
instructions. When L=1 and x=0, the initial queue is `blank,#`; the normalizer
rejects a blank in its initial leftmost cell. Larger padding remains
available, so no extra positive-length
guard is needed for the existential-padding theorem.

## 2. A fixed normalizer and the exact space quantifier

Use a one-sided four-symbol Turing machine with a left-boundary test. In
the bounded simulation, leaving either end of its supplied tape rejects,
even if the attempted transition names an accepting state. No right-boundary
test is required by its transition table: the queue simulation detects a
pending right move at `#` before entering the next machine state.

Fix a machine M recognizing the intended set on the canonical little-endian
ternary digits of x, with blank tape to their right and head at position zero.
The four-symbol tape convention is a standard universal one: a fixed binary
block simulation can represent a larger finite tape alphabet, with a fixed
initial parser for the ternary input. The simulation is part of M; no
external input recoding is imposed on x.

Prepend the following fixed normalizer:

1. Move right over trits to the first blank, which is initially at position
   ell. Move left once.
2. While the current trit is zero and the head is not at the left endpoint,
   write blank and move left.
3. At the first nonzero trit, return left to position zero without changing
   the remaining input, then enter M. If the head reaches position zero
   with trit zero, retain that single zero and enter M there.

Every step stays within the original `ell+1` tape cells. On exit the tape is
precisely `canonical(x)` followed by blanks, with head zero. This includes
x=0, whose canonical representation is a single zero. The normalized
infinite-tape configuration is independent of ell.

If M accepts x, its finite accepting computation visits only positions
0 through some S(x). Choose ell so large that x<3^ell and ell>=S(x).
The normalizer fits, and the subsequent computation agrees with M through
acceptance. Conversely, an accepting bounded computation agrees with the
infinite-tape machine at every step. Insufficient padding can reject but
cannot create acceptance. No assumption that an arbitrary semidecider on
padded inputs uses O(ell) space occurs in this argument.

## 3. Exactly one appended symbol on every transition

First make one ordinary rotation of the initial queue. Mark the first cell,
copy every subsequent cell, and copy the delimiter. The controller knows
the first-step event; it does not identify the first cell by a reserved
input digit. This leaves the same tape, with exactly one head mark at zero.
Every transition in this marking pass appends one symbol.

At each subsequent work-step boundary the queue has exactly the marked
tape cells followed by one delimiter. The scan control holds one preceding
cell, initially none, and remembers the simulated transition and whether a
rightward mark is pending. At each data cell:

* With no held predecessor, append a **provisional delimiter** and hold the
  current cell. Otherwise append the held predecessor and hold the current
  cell.
* At the unique original marked cell, apply the Turing transition. For a
  stationary move, hold the newly written marked cell. For a right move,
  hold its unmarked replacement and mark the next data cell on reading it.
* For a left move, mark and append the held predecessor, then hold the
  unmarked replacement. If there is no held predecessor, reject instead.

The previously read cell has not yet been emitted, so a left move modifies
the correct cell. The provisional delimiter occupies the one output slot
that would have been empty in the older one-cell-delay simulation.

At the original delimiter, append the held last cell. If a right mark is
still pending, reject instead. A valid scan now leaves the queue

    provisional #, updated tape cells.

One additional transition moves this provisional delimiter to the end.
Only now does the controller enter the next Turing state. Thus a tape of
length f uses exactly f+2 queue transitions for a successful work step,
and the physical queue length is f+1 at **every intermediate step**.
The original and provisional delimiters are temporarily distinct copies;
the finite scan phase specifies which event is being processed.

All malformed scans, undefined transitions and boundary overflows enter a
rejecting loop that re-appends the symbol removed. Before rejection at least
one delimiter is still present. The loop merely rotates the word and cannot
remove that delimiter. Initial marking also rejects a delimiter as its first
symbol; ell=0 instead reaches the normalizer's leftmost-blank rejection.
These rules give a total finite transition table over
all nine symbols. Finite control stores only the work state, held symbol,
next state and two flags; no queue length is stored in it.

## 4. Zero-word acceptance has no free endpoint condition

On a genuine accepting work state, start a separate erasure pass from the
usual tape-first, delimiter-last queue boundary. Replace every data cell
by ordinary zero as it is removed, and replace the final delimiter by
ordinary zero too. Stop in the accepting control after that delimiter
transition. All these transitions still append one symbol, so the length
marker remains W.

Before the final delimiter erasure, at least one delimiter is present.
During a valid work scan the old delimiter remains until its provisional
replacement already exists; the marking and rotation passes preserve one.
Rejection preserves every remaining symbol. During erasure the old delimiter is ahead
of the zeros being emitted until its own final step. Hence the queue cannot
be all zeros earlier. Conversely, when that final delimiter is erased,
every cell is ordinary zero and both numerical coordinates are zero.

Because ordinary zero is the unique symbol with coordinate pair (0,0),
both complete coordinate values are zero exactly when the queue is the
all-zero word. Thus the accepting contract is simply **reach an all-zero
word**. A separately checked terminal controller state is semantically
unnecessary once the initial control and every transition are certified.
The zero-word condition is implemented by the zero endpoints in the
transport below, rather than by uncounted final-coordinate witnesses.

Combining normalization, bounded simulation and erasure proves that the
fixed queue reaches an all-zero word from (1), for some adequate padding,
if and only if x is in the represented recursively enumerable set.

## 5. Two complete transports with genuine scalar products

Let an accepting run take t>=1 queue transitions. Use the common time
radix R from (1) and write q=R^t. For coordinate i=0,1 let n_ij be the
source content, d_ij its removed trit, and a_ij its appended trit. Pack

    Xi=sum_(j<t) n_ij R^j,
    Di=sum_(j<t) d_ij R^j,
    Ai=sum_(j<t) a_ij R^j.

The final content is zero, the initial content is Ii, and the scalar W
has the SAME value in every source row. Each transition therefore obeys

    3*n_i,j+1=n_ij-d_ij+W*a_ij.

After multiplication by R^(j+1) and summation,

    R*(Xi-Di+W*Ai)=3*(Xi-Ii).

Since R=3W, the exact divided form is

    W*(X0-D0+W*A0)=X0-x,
    W*(X1-D1+W*A1)=X1-I1.                              (2)

Unlike the varying-length queue, `W*Ai` is an ordinary scalar product,
not a product of two packed histories. There is no length word Z, no
selected-length word T, and no length transport to establish. A hypothetical
arbitrary nonzero final word would add q*Fi and its addition to each right
side; the erasure theorem justifies removing all four of those operations.

Each equation in (2) is computed by five instructions:

    weighted=W*Ai; cut=Xi-Di; appended=cut+weighted;
    left=W*appended; right=Xi-Ii.

Thus (2) costs four multiplications and six additions/subtractions, and
(1)-(2) together cost **14=7M+7A**. The checker expands all six independent
source residuals and verifies the off-shell correction

    old_i-3*new_i=(R-3W)*(Xi-Di+W*Ai).

Every true row has 0<=n_ij<W and 0<=d_ij,a_ij<=2. The chosen R=3W gives

    n_ij+W*a_ij<R,       d_ij+3*n_i,j+1<R.

These are strict bounds on both nonnegative sides. They are established
for compiled runs, not automatically for arbitrary integer solutions of
(2). A later arithmetic controller/mask compiler must recover them in its
soundness proof rather than invoke them circularly.

All six packed words Xi,Di,Ai are positive on true accepting runs. The
initial marking pass appends a marked cell whose first coordinate is
positive; the subsequent nonempty normalizer scan reads that cell. The
marking pass both reads and appends a delimiter with positive second
coordinate. Thus both head streams and append streams have a nonzero
digit, and both content histories do too. This also covers x=0. Possible
zero individual rows require no per-row positive adapter. The fixed
zero final endpoints are literals, not zero-valued positive coordinates.

## 6. Remaining cost boundary and finite evidence

The mechanism resolves the weighted-selector problem but not finite control.
A complete certificate must still enforce, on the SAME rows, the control
transition, removed and appended coordinate pairs, the six field bounds,
the initial control, and genuine power/time geometry. Fixed-numeral
convolution might combine some of these checks; no such complete compiler
or operation count is asserted here. Even the direct addition of the
retained 43-operation kernel would leave only 18 operations at target75
for all these unpaid obligations. A newer kernel, if independently proved,
would change this ledger without discharging those obligations.

The maintained source is
`../verification/explore_constant_length_raw_queue.py`, with its adjacent
JSON receipt. Its author run checks seven fixed clients, 645 reachable
controls and all 5,805 entries of their nine-symbol tables. Every entry
removes/appends exactly one symbol. Across 420 padded inputs it checks 420
exact normalizations, 9,832 direct Turing steps and 80,278 queue steps,
including 1,100 rejecting-loop steps. Every queue step checks both scalar
coordinate identities, constant physical length, strict radix bounds and
the impossibility of a premature zero word.

There are 140 accepting runs, all of which check both full packed transports
and positivity of all six history words; 220 rejections; and 60 bounded
observations of the explicitly stationary nonhalting fixture. The latter
are not general divergence claims. Twenty inputs in a workspace fixture
reject at minimal padding but accept at larger padding. The ell=0 case
rejects separately.

An independent direct-step enumeration inside the checker covers every tape
of length one through four, every head position, every write symbol and
every move. It checks 15,024 scans and 79,200 queue steps, with 12,304 valid
passes and 1,360 rejections at each boundary. The finite evidence supports
the general induction and universality argument; it is not a full
Diophantine solution decoder or a materialization of enormous Pell witnesses.
Default execution requires and rechecks the saved receipt; `--write`
regenerates it. Author and two independent complete scoped proof/source
reviews pass, with fresh default receipt checks. An additional independent
runtime audit covered 1,120 padded runs, 335,024 queue steps and 360 accepting
positive-history tuples. These reviews retain the component scope above.
