# A finite-state universal queue with an ordinary numerical input

This is an affirmative machine contract, not a count for a universal
Diophantine certificate. A fixed finite-state queue machine can receive the
ordinary ternary digits of x, perform its own preparation, and halt by
emptying the queue exactly when a fixed Turing machine accepts x. It uses
seven queue symbols, deletes one symbol per step, and appends at most three.
Its transition table is independent of x and the input padding length.

The two-coordinate numerical initialization is particularly small:

    N0=x, N1=L, Winit=3L, x+alpha=L, alpha>0.             (1)

Here L=3^ell with ell>=1 is supplied by external power geometry. Formula
(1) costs two operations, one multiplication and one addition. For positive
x the bound already forces ell>=1 once L is a power of three. If a geometry
allowing L=1 must exclude it also for x=0, the optional equality L=3Y with
positive Y costs one additional multiplication. All work after (1) is an
actual finite computation, including the internal input encoding.

This architecture has finite control and two content coordinates. It is
not the binary tag system 0->0,1->u and does not inherit that system's
conditional operation count. Control selection, coordinate masks and
bounds, and positive adapters are still to be compiled and counted.

## 1. Seven symbols and a precise input interpretation

Use ordinary cells 0,1,2, head-marked versions of these three cells, and
one delimiter #. Encode them by pairs of ternary digits:

    plain a -> (a,0), marked a -> (a,2), # -> (0,1).

Thus seven of the nine possible coordinate pairs are used. The two other
pairs are invalid alphabet symbols. The initial symbolic queue is

    d0 d1 ... d(ell-1) #,

where x=sum di*3^i and the word is padded with high zero digits to length
ell. Its coordinate values and length marker are exactly (1). Neither
input digit is reserved as a delimiter, and x's radix is unchanged.

The work Turing machine has tape alphabet {0,1,2}, with 2 as blank and
binary input. A first finite-state rotation converts each raw trit d to
the two-bit word

    code(0)=00, code(1)=01, code(2)=10.

The first bit of the first pair is marked as the head position. When the
delimiter is read, append one ordinary blank 2 followed by # and enter
the initial Turing state. The resulting queue is the marked first bit,
the rest of code(d0)...code(d(ell-1)), a blank 2, and #.

Each raw-digit step appends exactly two symbols, and the delimiter step
also appends two. The original delimiter stays ahead of every appended
symbol until the last loading step, so this is exactly one pass over the
original input. There is no uncontrolled recognition of a delimiter inside
the raw digits. The resulting binary input has an explicit end blank.

This preparation is necessary. Simply treating raw trit zero as the
simulated blank would erase the input endpoint and would not justify a
strong ordinary-input contract. Here the conversion occurs inside the
verified queue computation; it is not an external arithmetic dilation.

## 2. One finite scan implements one Turing step

At each simulated-step boundary the queue contains a nonempty finite tape
interval with exactly one marked cell, followed by #. Outside the interval
the tape is blank 2. The queue control stores the Turing state.

During a scan the finite control holds at most one preceding cell without
yet appending it. It also records whether the original marked cell has
been seen, its next Turing state, and whether a rightward head placement
is pending. These are all finite choices for a fixed Turing machine.

Before the marked cell, read an ordinary cell, append the held predecessor
if there is one, and hold the new cell. At the original marked cell read
the Turing transition, replace its contents by the written symbol b, and
do the following:

* For a stationary move, hold marked b and append the old predecessor.
* For a right move, hold ordinary b, append the old predecessor and mark
  the next cell when it is read.
* For a left move, mark and append the held predecessor, then hold ordinary
  b. If there is no predecessor, append a new marked blank first; this
  extends the finite interval one cell to the left.

After that event continue the same one-cell delay, applying any pending
right mark to the next ordinary cell. The appended cells lie behind the
old delimiter and cannot be read again during this scan.

At #, flush the held last cell. If a right placement is still pending,
also append a new marked blank, extending the interval to the right.
Finally append # and enter the next Turing state. At most three symbols
are appended at this delimiter step. Ordinary scan steps append at most
one. The left-boundary case also appends only one symbol at its data step.

The output tape interval, marked head and next state are exactly those of
the Turing transition, including both boundary-growth cases. A left move
does not require access to an already emitted cell: that is the purpose
of the one-cell delay. The pass order and delimiter position give a direct
induction on the cells, and then on complete simulated steps.

The scan control is finite. An explicit overestimate uses the current
Turing state, an optional next state, seven possibilities for a held cell
(six cell symbols or none), and two Boolean flags. With n Turing states
this is at most 28n(n+1) scan descriptions, plus two loader states, a
draining state and a rejecting loop. The executable compiler enumerates
the reachable subset, not configurations of the unbounded queue.

## 3. Acceptance, rejection and all boundary cases

On entry to an accepting Turing state, use a draining state: delete every
remaining queue symbol and append nothing. A finite queue becomes empty.
On entry to a rejecting state or an undefined Turing transition, enter a
nonhalting loop. The transition into that loop appends # if necessary, and
the loop thereafter re-appends each symbol it removes. Malformed scans
also enter this loop. Thus rejection cannot accidentally empty the queue.

Before acceptance, the initial loader always has the old delimiter or a
nonempty appended word present. During a scan the old delimiter remains
until its final step; that step appends at least a held cell and a new
delimiter. No valid nonaccepting computation empties the queue. A
nonhalting Turing computation therefore gives an infinite queue run.
An initially accepting Turing state is handled after the finite loader;
the initially rejecting case similarly enters the nonempty loop.

Consequently, on every correctly initialized input, the queue becomes
empty if and only if the simulated Turing machine accepts the prepared
binary word. Rejection and nontermination are both nonacceptance. This
is an empty-queue halting convention, not reachability of an unchecked
intermediate control state.

For any recursively enumerable set of ordinary integers, choose a fixed
binary-input Turing machine that parses pairs 00/01/10, reconstructs their
little-endian ternary value, ignores high zero padding, and semidecides
membership. It can be chosen with tape symbols binary plus blank. The
construction above gives one fixed seven-symbol queue program for this
set. Its program does not depend on x or ell. Hence for every x>=0 and
every adequate ell>=1, its run from (1) empties exactly when x belongs to
the set. Existentially choosing a larger L does not change acceptance.

The usual equivalence of finite-control queues and Turing machines is
also treated in [Petersen and Robson, Efficient Simulations by Queue
Machines](https://epubs.siam.org/doi/10.1137/S0097539799350608). That paper's
stated input convention includes a one-way input tape; it is not used as
a substitute for the exact initial-queue construction proved here. The
present loader, seven-symbol scan and input arithmetic are explicit
constructions in this investigation.

## 4. Exact scalar queue identities and cost boundary

For either coordinate i, write Ni for its little-endian integer value,
di for the coordinate of the removed symbol, Ui for the coordinate value
of the appended word, and a for that word's length. If W is the current
length marker, each compiled transition satisfies

    3*Ni_next=Ni-di+Ui*W, i=0,1,
    3*W_next=3^a*W, 0<=a<=3.                            (2)

The empty queue has both coordinates zero and W=1. Every nonempty source
has W>=3. All coefficients Ui and 3^a are fixed by the finite transition
table. Formula (2) has the same queue transport form as the scalar tag
recurrence, but it has two coordinates and a controlled rule choice.

The initialization (1) is fully counted. No total verifier count is claimed:
in particular, the finite transition relation, the seven valid symbol
pairs, both extracted head trits, intermediate row bounds, shared length
history, and strictly positive treatment of possible zero words are not
free. A valid smaller certificate would have to compile these obligations.

## 5. Executable finite-state evidence

`../verification/explore_finite_state_raw_queue.py` constructs the actual
finite transition table from small Turing machines. It checks every table
entry deletes one symbol and appends at most three, and simulates the
queue one dequeue at a time. After each complete scan it independently
compares the entire tape interval, head and state with a direct Turing
step. Cases include left and right growth, stationary moves, zero input,
high-zero padding, initial acceptance/rejection, undefined transitions,
and explicitly nonhalting machines. Every exercised dequeue also receives
both exact coordinate checks in (2) and the length check.

The finite runs corroborate the general simulation proof. A cutoff in a
nonhalting test is not a claim that arbitrary unobserved runs diverge, and
the receipt is not a complete Diophantine source certificate.

Review status: the author run and two independent complete proof/source
audits with fresh checker runs (root and binary_encoding) all passed without
findings. Binary_encoding additionally checked one complete scan for every
tape of length one through four, every head position, and every write/move
combination: 3,834 scans and 18,036 dequeues, including 360 extensions on
each side. That supplementary audit is separate from the maintained
author-regression counts in the receipt. The machine contract and checker
are frozen for publication; this review status does not assert a complete
Diophantine operation bound.
