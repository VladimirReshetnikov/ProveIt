# Unary counter equality against a biased source field

This is a prepared-frame component, not a complete proof verifier or a
blank-tape consistency machine. No uncharged selector, marker creator,
bootstrap, or call/return dispatcher is included.

## Exact interface and state accounting

Let c be the counter sentinel coordinate. For arbitrary natural a,b:

* cells c through c+a contain ones and cell c-1 is zero;
* a gap of at least two zeros follows the counter;
* the gap is followed by a header consisting of positive one-runs separated
  by single zeros, ending in one zero. In particular the seven-cell header
  `1^k 0 1^(5-k) 0`, 1 <= k <= 4, is allowed;
* a finite stream of nonempty unary fields follows the header, with a single
  zero separator between fields;
* the selected source has b+3 ones, except that its first one at s is erased;
* the initial head is s, in state `init`.

All other cells are arbitrary. In particular the exterior left of c-1 and
right of the selected field's ending separator may be arbitrary and are
never read.

The output restores the source's erased first one and every other source,
header and arena cell. The counter is exactly the single one at c. The head
is c, and the output port is EQ iff a=b, otherwise NEQ. Thus the only changed
cells are source cell s, restored to one, and the original counter cells
c+1,...,c+a, cleared to zero.

The total binary table has 29 working states: 28 operational states and one
invariant-failure sink. EQ and NEQ are two separate external ports, not
working states. They must be wired and charged by any enclosing machine.
The pre-fold version has 31 working states; two symbol-disjoint folds remove
two states. The sink is never reached on this interface; behavior on malformed
frames is not a certificate-rejection contract.

## Main invariant

The three initialization transitions restore s to one and erase s+1,s+2.
At each entry to `next_source`, for an integer j satisfying
0 <= j <= min(a,b):

1. The head is s+j+3.
2. The source differs from its restored original only at s+j+1 and s+j+2,
   which are zero. Its first j+1 cells are ones.
3. The counter is exactly 1^(a-j+1), beginning at c.
4. Every header, other field, separator and exterior cell is unchanged.
5. The counter gap has grown by j cells, so it still contains at least two
   consecutive zeros.

At j=0 initialization establishes all five assertions.

If j<b, the next source cell is one. The transitions through `back_one` and
`restore_old_left` erase it and restore s+j+1, shifting the two-zero marker
one cell right. The head then lies strictly left of that marker. A left
shuttle reaches the rightmost counter one. `loop_gap` erases that one and
moves left to `decrement`.

If j<a, `decrement` reads one. It leaves that one unchanged, moves right into
the enlarged gap and performs a right shuttle. The next entry to
`next_source` has j replaced by j+1 and satisfies all five assertions.

If j=a, `decrement` instead reads the specified zero at c-1. The just-erased
one was the sentinel. `restore_exhausted` restores the sentinel and enters a
failure-mode right shuttle. Here b>a is already established; the shifted
marker still lies entirely inside the source since j+1<=b. The failure
shuttle locates the marker, restores its two cells, and makes a failure-mode
left shuttle. At the sentinel it temporarily erases that sentinel, and
`clear_counter`, `restore_counter`, `return_neq` restore it and exit through
NEQ with head c. Every source and arena cell is restored.

If j=b, `next_source` reads the original source-ending zero. `restore_right`
and `restore_left` restore the marker, and a done-mode left shuttle reaches
the rightmost counter one. It moves left without erasing that one and enters
`done_check`.

* If a=b, the counter has only its sentinel. `done_check` reads c-1=0, moves
  right and immediately exits EQ on c.
* If a>b, the read cell is one. It moves right to the rightmost counter one;
  `clear_counter` erases the entire finite counter run moving left, detects
  c-1=0, and moves right. `restore_counter` writes the sentinel one;
  `return_neq` bounces left from its adjacent zero and exits NEQ on c.

These are exhaustive cases, and give the exact comparison result.

## Shuttle lemmas and confinement

A left shuttle starts strictly left of the two-zero marker, or after it has
been fully restored. Between it and the counter gap, every zero is an isolated
field/header separator. Its `ones` and `zero` states preserve each cell and
recognize the first adjacent zero pair; its `gap` state then crosses the
remaining gap zeros and stops at the rightmost counter one. This is proved by
induction over the finite sequence of positive unary runs crossed.

A right shuttle starts in the counter gap. `gap_right` crosses zeros and
enters `find_ones` after the first header one. `find_ones` and `find_first`
traverse positive unary runs and isolated separators. The first adjacent zero
pair is exactly the source marker. The original source-ending zero can be a
third zero, but the first pair remains the marker. Normal and failure modes
have identical preserving scans and differ only at that second marker zero.
The same induction covers any positive-run header, including all four
seven-cell header modes; no header decoder or rewrite is hidden here.

All productive shuttles cross finite intervals. Each normal productive cycle
increases j by one. It either reaches j=b or, when a<b, attempts j=a+1 and
finishes on the failure path. Every terminal scan is finite. This proves
termination for all a,b and all permitted finite intervening fields.

The only possible read to the left of the sentinel is c-1, whose zero is part
of the contract. No read occurs right of s+b+3, the original source-ending
separator. No exterior assumption beyond these stated boundary cells is used.

## Forced-symbol folds

In the pre-fold table:

* `erase_first` reads only one, whereas `return_neq` reads only zero;
* `erase_second` reads only one, whereas `restore_counter` reads only zero.

The first two facts follow from b+3>=3 at initialization. `return_neq` reads
the blank immediately right of the restored single sentinel. `restore_counter`
reads the just-cleared sentinel cell. Replace each pair by one state retaining
the appropriate transition on each symbol and retarget incoming edges.

The old-state projection, identical tape, and identical head give a literal
one-step simulation on every valid execution. Induction on execution length
therefore proves that the 29-state table has the same result, time and head
trajectory as the 31-state construction.

Every remaining one-symbol state has precisely the valid read set listed in
`compare_biased_counter_guards.json`; all other operational states have both
symbols conservatively admitted. The guard argument is structural: marker
restorers read their designated zero cells, and the two folds above read the
indicated initialization ones or cleared counter zeros. These universal
claims are not inferred from test coverage.

## Evidence and limitations

`compare_biased_counter.py` constructs the table and checks 5,072 deterministic
small and seeded-random whole-tape cases, including a=b, a<b, a>b, all four
header modes, minimum gaps, arbitrary intervening field lengths and arbitrary
exterior cells. Maximum observed run length is 74,803 transitions. These
finite regressions supplement the induction above; they do not establish its
universal quantifiers by themselves. No proof-assistant kernel compilation is
claimed.
