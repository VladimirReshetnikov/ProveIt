# Mathematical and engineering notes

## 1. Contract and notation

Let the nine prescribed natural register values be `v_0,...,v_8`, with sum
`S`. The fixed physical permutation is `(2,4,3,7,6,8,0,1,5)`. A value `v` is
represented by `0 1^(v+1)`. Therefore the physical register word `R` has
length `18+S` and has exactly `9+S` one cells.

For positive integers `n,m`, the initializer starts on a wholly blank
bi-infinite binary tape, with head coordinate zero. It terminates at the
runtime's decoder root with exactly the word

`1 0^g 1 R`

on otherwise blank tape, with its head immediately right of the first one.
The first one is the marker and the second distinguished one is the header.
No scratch marks and no spare register blocks remain. The final head is
`-(18+S+g)`. The arithmetic assumptions are just `v_i>=0` and `n,m>=1`.

The standalone initializer can exit to any fresh target state. The smaller
shared-cleanup form additionally uses unchanged transitions of the clean
Mira runtime. The generated binary tables include that entire runtime.

## 2. Standalone contiguous-counter construction

The initial leftward writer emits the reverse of the physical register
word, then `1 0 0 1^n 0 1`. Viewed in increasing tape coordinates, the
result is a marker, one zero, a contiguous run of `n` counter ones, two
zeros, the header, and the physical register word. The head is immediately
right of the marker. This writer has `S+n+23` states and literal steps.

Let the initial marker be at `f_0`, the first counter cell at `a=f_0+2`, and
the unchanged header at `h=f_0+n+4`. At the start of iteration `k`, for
`0<=k<=n`, the complete invariant is:

1. The marker is at `f_k=f_0-km`; the head is `f_k+1` in state `right`.
2. Exactly the counter cells `a,...,a+n-k-1` contain one; the interval is empty
   when `k=n`.
3. The header and all register cells remain at their initial coordinates and
   retain their initial values.
4. All remaining cells are zero.

The loop moves right across zeros, finds the first one, crosses its entire
run, and inspects the cell after the first following zero. If that cell is
zero, it found the counter run: the original two-zero delimiter is still
present and erased counter cells only lengthen it. It moves back two cells,
erases the rightmost counter one, returns left across the remaining counter
ones and then across zeros to the marker, erases that marker, moves `m`
cells left, writes its replacement, and returns to `right`.

This changes precisely the two parts of the invariant that should change:
the counter run shortens by one and the marker moves `m` cells left. In
particular the routine neither consumes register data nor confuses data
ones with an unfinished counter run.

When the counter is empty, the first one found by the same scan is the
header. The next cell is the first register delimiter, zero, and the cell
after it is one even when the first register value is zero. This is the
other branch of `test`. The routine returns across the delimiter and header,
leaves both unchanged, scans left to the marker, and exits immediately to
its right.

Thus the invariant proves the complete contract. The final gap is

`g = n(m+1)+3`.

There are ten fixed control states, `m` stride states, and `S+n+23` writer
states. The exact state count is

`I_standalone = S+n+m+33`.

The loop's iteration `k`, with `r=n-k` counter ones remaining, takes

`2r+2km+m+6`

literal transitions. Summing over `k=0,...,n-1` gives

`(m+1)n^2+7n`.

The final scan and return take `2g+6` transitions. Including the writer, the
exact blank-tape time is

`T_standalone = S+35+8n+(m+1)n(n+2)`.

These are full literal transition counts, not accelerated scan counts.

## 3. Shared cleanup and the selected new controls

The shared form inserts a sentinel one followed by a zero immediately
before the header. Its writer emits the reverse register word followed by
`1 0 1 0 0 1^n 0 1`. The complete post-writer order is therefore:

marker, zero, counter run, two zeros, sentinel, zero, header, register word.

The same loop and invariant apply, with the sentinel at `h-2` added to the
preserved support. Now `h=f_0+n+6`. Once all counters have disappeared, the
scan first encounters the sentinel and tests the header, which is one. It
then enters old runtime state 14 with its head on the zero between sentinel
and header.

Only the following unchanged runtime rows are used for the first cleanup
steps:

| Old state/read | Write | Move | Target |
|---|---:|---|---:|
| 14/0 | 0 | L | 20 |
| 20/1 | 0 | L | 2 |
| 2/0 | 0 | L | 2 |
| 2/1 | 1 | L | 4 |

They erase the sentinel, preserve the header and register word, and scan left
to the marker. Beyond that marker, the unchanged dispatcher crosses its
nine-state zero counter `(4,6,9,13,19,29,41,58,74)`, then state 84 scans
right to the marker and enters the new decoder root immediately to its
right. All cells visited beyond the marker are blank and remain blank.

The implementation checks each shared row, the nine-state counter, and both
state-84 rows before constructing a machine. The formula is specialized to
this nine-state dispatcher; a compiler that extends its counter needs the
corresponding adjusted time formula.

In this form:

`g = n(m+1)+5`,

`I_shared = S+n+m+32`,

`T_shared = S+57+8n+(m+1)n(n+2)`.

The state count uses `S+n+25` writer states and only `7+m` new control/stride
states: three standalone finish states have been replaced by existing
runtime states. The final phase takes `2g+22` transitions. The additional
dispatcher excursion accounts for the constant 57 in the full time formula.

For required gap 102, minimal state cost occurs at `n+m=19`. The legal
choices include `(9,10),(10,9),(11,8)`; the first is fastest. The standalone
version then has gap 102 and the shared form has gap 104. For `S=0`, the
shared initializer has 51 new states before quotienting and takes 1,218
steps. For `S=2`, it has 53 states and takes 1,220 steps. The public-program
control starts at the decoder root with source-order registers
`[2,0,0,0,0,0,0,0,0]` in the latter case.

## 4. Exact minimization within these explicit initializer families

Fix a required gap `G` and write `c=n+m`. For either contiguous-counter form,
with offset `d` equal to 3 or 5,

`g = n(c+1-n)+d`.

For each integer `c>=2`, the maximum over positive `n,m` is exactly

`floor((c+1)^2/4)+d`.

The maximizing choices are the integer(s) nearest `(c+1)/2`; they satisfy
`1<=n<=c-1`, apart from the harmless small boundary where `n=1` already
attains the maximum. Completing the square proves the bound and these
choices attain it. Consequently the exact minimum possible `n+m` is

`c_min = max(2, ceil(sqrt(4 max(0,G-d))) - 1)`.

The implementation computes the integer ceiling square root without
floating-point arithmetic, enumerates only `n=1,...,c_min-1`, and breaks
ties by exact literal time and then actual gap. This reduces the parameter
search itself from an `O(G)` scan to `O(sqrt(G))` arithmetic candidates.

For comparison, the previous source21 initializer uses `c_old=2n+m` and

`g_old=n(c_old+2-2n)+2`.

For fixed integer `c_old>=3`, its exact maximal gap is

`floor((c_old+2)^2/8)+2`.

Thus its exact minimum variable cost is

`max(3, ceil(sqrt(8 max(0,G-2))) - 2)`.

For large `G`, the full new shared initializer therefore has cost
`S+2 sqrt(G)+O(1)`, while the old family has cost
`S+2 sqrt(2G)+O(1)`. These are upper/lower statements **within the two given
constructor families**; they imply no global lower bound on binary
initialization and no busy-beaver record. The new tape algorithm is a local
improvement found in this investigation, with no assertion of priority over
the entire initializer literature.

## 5. Three exact state identifications

All 18 reported clean-assembler controls admit three savings under ordinary
transition partition refinement:

1. The generic decrement helper `e:5` and explicit break scan `b:1` have
   matching transition actions after identifying those two states. Their
   read-zero transition is `0,L,e:7`; their read-one transition is
   `0,L,b:1`.
2. The final writer state and the final stride state have the same two rows:
   write one, move right, enter `i:right`.
3. The penultimate writer state and penultimate stride state have the same
   two rows after the preceding identification: write zero, move left, enter
   the shared final state.

The second preceding stride state exists when `m>=2`, as it does in every
reported control. The implementation does not assume these three pairs;
its ordinary refinement algorithm finds them from the complete literal
tables, and the separate checker validates the emitted maps row by row.

Let a complete source transition be `(w,d,q')`, with a distinct halt state,
and let `f` map source working states to target working states and source halt
to target halt. The certificate equation is, for both read symbols and every
source state,

`delta_target(f(q),b) = (w,d,f(q'))` whenever `delta_source(q,b)=(w,d,q')`.

Map configurations by `f` on the machine state while leaving head coordinate
and every tape cell fixed. One transition commutes with this map because
both machines read the same cell, write the same symbol, make the same move,
and reach mapped states. Induction proves exact commutation for every finite
number of steps. Because working states map to working states and only halt
maps to halt, halting is preserved and reflected at each exact time. The
whole tape, final score, and arbitrary-input behavior are therefore preserved.

This is the same mathematical sufficient condition formalized generically
in ProveIt's `StateReduction.lean`. The supplied Python certificates are
not new Lean instantiations. The new initializer invariant is also an
ordinary mathematical proof, independently accompanied by complete finite
boot replays.

Exact refinement of the original published 254 table and the public 253
table yields no nontrivial classes. This prevents transferring the clean
assembler's three-state saving to those already optimized literal tables.

## 6. Measured evidence and research boundary

Each of 18 raw controls and its quotient has its entire initialized finite
tape support checked, including the absolute head coordinate and all exterior
blanks. All 18 quotient controls pass all 8,391 symbolic instruction cases,
which include both branches of every decrement site. The three input DAGs
all expand to the same count of instruction/branch cases even though their
sharing differs. The ordinary initializer formulas are additionally exercised
for `n,m=1,...,12` with all-zero registers, next-proof two, and register vector
`[0,1,2,3,4,5,6,7,8]`: 432 standalone cases and 432 shared-cleanup cases.

The affine instruction checks retain their existing assumptions about
arbitrary register-box execution and the Python checker. Our state quotient
does not need those assumptions. Its source and target machines are compared
on all transition rows and its correctness follows directly from the
certificate equation.

The best complete generated control here has 309 states with all-zero
registers, or 311 states with the accepted next-proof-two seed. Those figures
are not competitive with the public 253 machine. They improve the separate
clean-assembler initialization route and provide a cheaper, fully counted
backend for future logic/theory experiments. No new minimal theory,
logical-completeness argument, proof-search simulation, or internal
ZFC-consistency equivalence is claimed by this component package.
