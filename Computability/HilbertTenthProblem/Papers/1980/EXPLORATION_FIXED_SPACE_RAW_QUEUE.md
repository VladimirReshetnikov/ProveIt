# A fixed-space raw queue with existential input padding

This is an affirmative ordinary-input machine contract. For every recursively
enumerable set A of nonnegative integers there is one fixed seven-symbol,
finite-state queue machine such that

    x in A  iff  some L0=3^ell>x makes the initial queue empty eventually.

The queue starts with the ordinary ternary digits of x padded to ell places,
followed by a delimiter. Its two numerical coordinates are exactly x and L0.
After its loading phase, the simulated tape has a fixed interval of 2ell+1
cells. Attempts to leave that interval reject. Every queue transition deletes
one symbol and appends at most two. Larger padding supplies more blank work
space after an explicit, fixed input-normalization procedure.

This statement quantifies existentially over padding. Some accepting inputs
can be rejected with insufficient padding. The proof does not assume that an
arbitrary machine which recognizes padded inputs uses O(ell) space.

The exact arithmetic interface is

    N0=x, N1=L0, Winit=3L0, x+alpha=L0, alpha>0,
    R=243 L0^2.                                                    (1)

It costs four operations: three multiplications and one addition. Two of the
multiplications construct R. If external history geometry establishes that
R divides a power of three, (1) also establishes that L0 is a power of three.
No total Diophantine verifier count is claimed: controller selection, valid
alphabet pairs, history masks, and their complete arithmetic realization are
outside this interface.

## 1. Alphabet, input, and the bounded work model

Use the same seven queue symbols as
[the unbounded queue contract](EXPLORATION_FINITE_STATE_RAW_QUEUE.md):

    plain a=(a,0), marked a=(a,2) for a in {0,1,2};  #=(0,1).

The head of the queue is the least significant ternary position. For
x=sum d_i*3^i, the initial word is

    d_0 d_1 ... d_(ell-1) #.

It has coordinate values N0=x, N1=3^ell and length marker Winit=3^(ell+1).
All three raw digits 0,1,2 are allowed; none is reserved as a delimiter.

The loading pass appends code(d)=(floor(d/2),d mod 2), marking the first bit
of the first pair. At its original delimiter it appends the ordinary blank
2 followed by #. The resulting tape interval has exactly 2ell+1 cells:

    code(d_0)...code(d_(ell-1)) 2.

The head is on cell 0. The queue, including its delimiter, has length

    F=2ell+2.                                                      (2)

The work machine has tape alphabet {0,1,2}, where 2 is blank. Its finite
transition table reads (state, symbol, left), where left is true exactly at
cell 0, and returns (new state, written symbol, move), with move in {-1,0,1}.
An undefined rule or an attempted move to a negative position rejects. This
is the one-sided tape convention used throughout this note. In the bounded
version, an attempted move to position 2ell+1 also rejects, even when the
rule's target state is accepting.

One-sided machines with a left-boundary test and this alphabet can implement
ordinary semidecision algorithms. For completeness, the usual changes of
model are finite ones: fold a two-sided tape at the origin into two tracks
on a one-sided tape, retain the chosen track in finite control, and encode
the resulting finite tape alphabet in fixed binary blocks with blank
unallocated space. Block position and the finite alphabet codes are finite
control information. This does not require additional queue symbols: the
queue simulates the resulting three-symbol work machine. Its input parser
can decode the finite pair word 00/01/10 into ordinary trits and apply the
desired numerical semidecider.

The left-boundary test is part of this explicit work-machine convention,
not a symbol silently prepended to the raw numerical input.

## 2. A fixed normalizer reclaims the padding

Let canonical(x) be code(d_0)...code(d_(k-1)), where the high digit is nonzero
when x>0; for x=0 let canonical(0)=00. Choose a fixed work semidecider M for A
on canonical(x), starting at cell 0 with blanks everywhere to the right.
Prepend the following fixed normalizer to M. Its states are disjoint from
the states of M.

1. Scan right over the binary input to its first blank. This is the blank at
   position 2ell. Move left to the second bit of the last pair.
2. Remember that bit in finite control and move left to the first bit. The
   pair is one of 00,01,10. If it is 01 or 10, the highest nonzero trit has
   been reached; return to cell 0 and enter M.
3. If the pair is 00 and its first bit is not at cell 0, erase both bits to
   blank 2. From the erased first bit, move left to the second bit of the
   preceding pair and repeat step 2.
4. If the pair is 00 and its first bit is cell 0, keep that pair and enter M
   at cell 0. This is the normalization of x=0.

Returning to cell 0 uses the left-boundary flag. The erasure of a pair whose
first position is 2j>=2 goes through positions 2j,2j+1,2j,2j-1; it never
moves outside the existing interval. The initial scan reaches position 2ell
and does not step beyond it. The finite table rejects malformed pairs,
unexpected blanks, or a second bit erroneously occurring at the boundary.

An induction on the number of erased pairs proves that after the normalizer
the tape is precisely

    canonical(x), followed by blanks up to position 2ell,

with head 0 and control at M's initial state. The physical interval is
unchanged. In particular, erased 00 pairs become available blank work space;
they are not retained as a long input that M must repeatedly interpret.

This normalization uses no new tape or queue symbols. It takes time
depending on ell, but its maximum tape position is exactly within the given
interval. The source compiler generates its finite table explicitly.

## 3. Fixed-space queue simulation and both boundaries

The queue scan is the one-cell-delay construction of the unbounded queue
contract, with both growth cases replaced by rejection. At each simulated
step boundary there is exactly one marked tape cell followed eventually by
the unique delimiter, and the control stores the current work-machine state.

During a scan the control holds the preceding cell. Before the marked cell,
ordinary cells are copied with a one-cell delay. At the marked cell:

* A stationary move holds the newly written cell with its mark.
* A right move holds the written cell without a mark and marks the next
  ordinary cell read. If no such cell exists, the pending mark is still set
  at #, and that delimiter transition rejects.
* A left move marks and emits the held predecessor, then holds the written
  cell without a mark. If there is no predecessor, that data transition
  rejects.

The condition that the predecessor is absent is exactly the work-machine
left flag: it occurs only when the original marked cell is cell 0. No global
queue-length or unbounded position test is stored in finite control.

An ordinary successful data transition emits zero or one symbols. At a
successful delimiter the held last cell and # are appended, exactly two
symbols, and control enters the new work state. There is no extra left or
right blank. Induction over the cells proves that every completed pass
has exactly the tape contents, head position and state of one bounded
work-machine step.

On acceptance, enter the deleting drain state. On rejection, an undefined
rule, or malformed scan, enter the nonempty loop. The transition into a
rejecting loop emits # when needed, and the loop thereafter re-appends each
symbol it removes. A valid scan always has its old delimiter ahead of its
new output; at a completed pass the delimiter is restored. Thus a valid run
can become empty only by accepting and draining. Boundary rejection cannot
accidentally empty it.

The machine is finite. Its scan control has the work state, an optional next
state, one held cell or none, and the two flags for head seen and right move
pending. The bound 28n(n+1)+4 from the unbounded compiler still applies for
n work states. Reading the left-boundary flag does not add a stored counter.
The actual compiler enumerates the reachable controls and all seven input
symbols at each control. Every entry, including malformed-input entries,
appends at most two symbols.

## 4. Ordinary-input universality under existential padding

Fix A and its canonical-input one-sided work semidecider M. The normalizer
and queue compiler are fixed functions of M and do not depend on x or ell.

Suppose x is accepted by M on its infinite right-blank tape. Its finite
accepting run visits only positions 0,...,S(x), for some finite S(x). Choose
ell with x<3^ell and 2ell>=S(x). The normalizer fits in the supplied interval
and leaves exactly the canonical configuration of M. M's entire accepting
run then fits in the same interval, so the queue accepts and drains.

Conversely, if a padded bounded queue empties, its normalizer has established
the canonical input, and every simulated step before accepting stayed in the
interval. These same steps are steps of the infinite right-blank machine M.
Consequently M accepts x. Insufficient padding can only cause rejection;
it cannot create acceptance. For each accepted x, every sufficiently large
padding works, although some smaller paddings need not work.

The argument deliberately places the normalizer before M. No bound is
assumed on a general machine's behavior on different padded versions of the
same input. After normalization the infinite-tape configuration is identical
for every padding; only the right endpoint of the bounded simulation varies.

If the arithmetic permits L0=1, the input bound forces x=0 and the initial
queue is just #. The loader's first-state delimiter rule enters the nonempty
rejecting loop. This extra rejected padding creates no false acceptance and
does not prevent acceptance of 0 using ell>=1. Thus no separate ell>=1 guard
is needed for the existential-padding theorem.

## 5. Phase lengths and one fixed radix formula

During loading, after j raw-digit steps the queue length is ell+1+j.
The original delimiter step raises the length from 2ell+1 to F=2ell+2.
During every successful normalizer or client scan the first data step emits
nothing, reducing the queue length to F-1. Each remaining data step emits
one symbol and preserves F-1. The delimiter emits two and restores F.
The left-boundary rejection and right-boundary rejection append only #;
neither increases the length beyond F. Rejection loops preserve their
nonzero length, and draining only decreases length. Therefore every
configuration of a run with ell>=1 satisfies

    queue length <=2ell+2,  W=3^(queue length)<=9L0^2.               (3)

For either coordinate let N be the current value, d the head trit, U the
coordinate value of the appended word, and a its length. Every transition
satisfies

    3N_next=N-d+UW,   3W_next=3^a W.                               (4)

The seven-symbol encoding and a<=2 give 0<=N<W, 0<=U<=8 and 3^a<=9.
Consequently the nonnegative sides used to bound local coefficients obey

    N+UW <9W <=81L0^2,
    d+3N_next <=2+3(9L0^2-1) <27L0^2,
    3^a W <=81L0^2.                                               (5)

Thus R=243L0^2 strictly dominates both content coordinates, their local
nonnegative transport sums, all weighted append terms, all length terms,
and the head trits. The constant 243 is deliberately loose and costs the
same single scalar multiplication as any sharper fixed choice. For ell=0
the sole malformed input # immediately loops with length one and also
satisfies these numerical bounds.

The initial queue length marker is 3L0, not L0. The multiplication by three
is explicitly present in (1); no length conversion is implicit.

The straight-line schedule for (1) is

| Register | Operation |
|---|---|
| Lsquare | L0*L0 |
| radix | 243*Lsquare |
| initial_length | 3*L0 |
| input_bound | x+alpha |

Its free comparisons are R=radix, Winit=initial_length, input_bound=L0,
N0=x and N1=L0. The checker expands all five independent source residuals.
Here x is a nonnegative external parameter; alpha, L0 and R are positive.
The content coordinate N0 can be zero, so treating it as a separately
positive existential in a later system would need an adapter or direct
parameter substitution.

Suppose a surrounding certificate proves q=3^u and q=Rv for positive v.
Then R is a power of three. Since 243=3^5 and R=243L0^2, every prime divisor
of L0 is three, hence L0=3^ell for ell>=0. Equivalently, the exponent of R
is 5+2ell. This is a consequence of (1) plus externally proved power
geometry, not a free variable exponent. Neither q=Rv nor a power predicate
is included in the four operations above.

Equations (4) fit the conditional shared-radix transport in
[the twelve-operation transport note](EXPLORATION_RAW_QUEUE_TRANSPORT.md).
This observation does not yet yield a complete verifier: the weighted
fields must still select the actual append word and length on the same
controller rows, and the two-coordinate alphabet restriction must be
enforced. In particular, the local bounds (5) are proved for compiled
queue runs; an arbitrary arithmetic solution has not yet been decoded as
such a run. No old binary-tag count is imported.

## 6. Maintained executable evidence

`../verification/explore_fixed_space_raw_queue.py` contains the finite
left-aware work-machine convention, fixed normalizer, bounded queue
compiler, four-operation source schedule and an independent direct bounded
TM interpreter. It reuses the frozen queue alphabet, elementary coordinate check,
finite-control enumerator, and verified loader/drain/loop transitions from
the unbounded artifact; bounded scan transitions and the normalizer are
implemented in the new module.

The author run checks 12 fixed test machines with 1,647 compiled controls
and 11,529 complete symbol transitions. All outputs have length at most two.
For 1,152 padded inputs, it verifies 1,152 exact normalizations, 41,436
bounded work steps and 426,386 queue steps, each with both coordinate
identities, the length identity and the strict radix bounds. There are 496
accepting drains, 560 nonempty rejecting runs and 96 bounded observations of
the explicitly stationary nonhalting fixture. No other cutoff is called a
result. The runs include zero inputs, 768 high-zero paddings, 192 left
overflow rejections and 128 right overflow rejections.

For each x in 0,...,31, a fixture which needs two cells beyond its canonical
input rejects with the minimal padding and accepts with either of the next
two padding lengths. This exercises the existential-space distinction.
The ell=0 zero-input rejection is checked separately.

An exhaustive independent direct-step comparison tests every tape of length
1,...,4, every head position, every write symbol and every move: 3,834 scans,
16,758 queue steps, 3,114 valid passes and 360 rejections at each boundary.
The finite checks supplement the induction proofs and the generic compiler
theorem; they do not enumerate arbitrary semideciders or assert a total
Diophantine count. Author and independent root/binary_encoding complete
proof/source audits and fresh checker runs PASS, with no mathematical
findings. Review metadata and an explicit dependency clarification were
updated after those runs; the mathematical source is unchanged. The three
files are frozen for publication, which remains a separate step.
