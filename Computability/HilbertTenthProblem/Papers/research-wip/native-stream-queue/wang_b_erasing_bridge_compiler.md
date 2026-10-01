# An explicit erasing-TM compiler with a paid framed input

This packet supplies the finite transition compiler missing from the
[non-erasing TM-to-Wang bridge](wang_b_nonerasing_tm_compiler.md). Every
fixed total binary TM with a unique halt is compiled into a concrete
finite binary non-erasing TM. A separate complete scalar graph maps
ordinary positive binary input x to the exact framed Wang tape required
by the two simulations. This is an effective construction, not a fixed
universal table or an improved universal polynomial bound.

The [source](wang_b_erasing_bridge_compiler.py) returns every binary
transition explicitly; the [receipt](wang_b_erasing_bridge_compiler.json)
records table hashes, differential executions and the complete input
loader. The default ordinary machine erases its read symbol, moves right
and halts. Its compiled non-erasing table has1,481 nonhalting states and
2,962 transition rows. The resulting Wang list has19,254 instructions.
The loader itself costs **190=94M+96A**, with143 certificate gates,
16 comparisons,38 positive witnesses and degree at most402.

The complete Wang DAG for the large example was not materialized:
expanding the frozen helper's dependency audit was too large. The
proved inherited source-size formula instead gives a **312,967-operation
upper bound**,25 comparisons,23,763 witnesses and degree at most12,092,924
for this example. These are paid bounds, not an actual emitted whole-DAG
ledger, and this example is not universal.

## 1. Source machine, records and input convention

A source table has h rows, states0,...,h, start0 and sole halt h. Each
nonhalting state has two transitions(write,L/R,target), with binary
writes and target in0,...,h. Erasures1->0 are allowed. The source rejects
partial rows, stationary moves and invalid targets. Halting occurs after
the transition's write and move into h. The empty table starts halted.
A partial semidecider must first be given its intended halt/reject
convention; missing transitions are not silently treated as acceptance.

Ordinary x>0 places bit_j(x) at cell j>=0, starts at cell0, and leaves
all other cells0 on a bi-infinite tape. Choose any n>=max(2,bitlength(x)).
Only the represented interval0,...,n-1 is initialized; its extra high
zero bits are ordinary blank cells, so all such paddings have the same
source behavior.

Use aligned five-bit blocks in physical left-to-right order

    (present, delimiter, data, head, processed).

The integer of a block uses this order from least to most significant:

    empty=0, L=3, R=7,
    cell(b,h)=1+4b+8h, processed(v)=v+16.

A record is L, finitely many cell blocks, R. It has exactly one head bit.
All record blocks are present; the exterior is all-zero binary tape.
An ordinary initial record is

    L, cell(bit_0(x),1), cell(bit_1(x),0), ...,
       cell(bit_(n-1)(x),0), R.                    (1)

The simulator starts on the first bit of L. Its finite control stores
the source state, so no source-state code is needed on tape. Every new
record is appended immediately after the previous R, without gaps.
Previously copied records are retained forever.

The record-copying idea is consistent with the overview in
[Neary–Woods–Murphy–Glaschick2014](https://mural.maynoothuniversity.ie/id/eprint/12409/1/Woods_Wang_2014.pdf),
Lemma5, printed p637. That overview uses different three-bit cells and
does not specify the transition table here. The five-bit protocol,
finite control expansion and input framing below are proved directly.

## 2. A finite record-copying transition system

At a record boundary the source interval is[l,l+m-1], the control holds
its source state q, and the binary head is at that record's L. The next
record represents[l-1,l+m], adding one blank cell at each end. Its copied
contents and head simulate one source transition.

Mark the processed bit of the source L. Scan right to the first empty
block, write the new L, and scan left to the rightmost processed block.
Initially this is the source L. Advance one block to fetch the first
source cell. All scans advance by whole five-bit blocks; data bits inside
a block are never mistaken for record delimiters.

The finite control carries a delayed cell(buffer_bit,buffer_head),
initially the new left blank(0,0), a seen-head flag, a pending-right flag,
and the source state before the head or target state after it. When a
source cell is fetched:

1. Read its bit and old head flag. Its new bit is unchanged unless this
   is the unique old head, when the actual source transition supplies
   the new bit and target state.
2. A left-moving old head sets the delayed buffer's head flag. A
   right-moving old head sets pending-right for the next fetched cell.
   The previous pending-right value sets this cell's new head flag.
3. Mark this source cell processed. Scan right to the first empty block
   and append the delayed buffer as a fresh unprocessed cell.
4. Scan left to the rightmost processed block, which is exactly the
   source cell just fetched, and advance to its successor. The current
   transformed cell becomes the new delayed buffer.

The new record is unprocessed, and the unconsumed source suffix is also
unprocessed. The consumed source prefix is processed. Therefore the
return scan crosses the entire new record and unconsumed suffix and
stops at exactly its own source cursor, independent of the data values.
No test for an unknown number of trailing blank source cells is used.

On reaching the source R, append the delayed last cell, then the new
right blank carrying pending-right, then a new R. Scan left to the
nearest L, which is the new record's L. Enter the retained target source
state there. If it is h, enter the unique simulator halt instead.

The delayed cell is essential: a left move can change the preceding
cell's head flag before that cell is emitted. A right move is transferred
by pending-right, including a move into the new right blank. Thus every
step produces exactly one new head, even on either original boundary.
The old record's data/head bits are untouched; only its L and cell
processed bits change from0 to1. New output is written only on all-zero
blocks. Consequently every physical write is non-erasing.

The implementation's block controls are start, begin, return, fetch,
seek_emit, finish_seek, finish_pad, finish_R and find_L. Their finite
parameters are source/target states and Boolean buffer flags. At the
validated start/fetch/finish sites, invalid blocks or repeated heads
enter a total right-moving sink. The sink never
halts. Reachable control generation over the32 possible block integers
therefore terminates and gives a complete finite block table.

## 3. Literal binary expansion and halting equivalence

`binary(table)` returns the complete binary table, its control-label map
and the block table. It normalizes list or tuple input first. Every
nonhalting binary state has both read0 and read1 transitions, every move
is L or R, and every read1 transition writes1. The initial binary state
is0 and the sole halt is numbered last, matching the frozen Wang bridge.

At a block entry, five binary reads retain the block's complete value in
finite control. The first four reads move right while preserving the
read symbol. The fifth selects the specified block transition. If only
the last bit changes, it writes that bit and walks directly to the next
block origin. Otherwise it writes the remaining desired bits while
walking left, then walks to the specified adjacent block origin. Each
write is an OR with the old bit. A stationary block transition uses a
right-left pair, so no stationary binary transition is introduced.

Every block transition is thus implemented by at most14 binary steps,
with the same five-bit output, the requested displacement(-5,0,+5), and
all other tape bits unchanged. The finite expansion shares identical
write/walk tails, but this sharing does not change their literal rows.
All row targets are concrete integer states; there is no uncompiled
macro call, implicit multi-tape operation or oracle.

Induct on source steps using Section2. Each finite source record causes
only finite scans, since an empty block exists at its right frontier and
its processed cursor exists to the left. The next record has precisely
the source successor tape, state and head. Conversely, the only halt
entry after a nonempty simulation is from find_L with stored source
state h. Therefore the simulator halts exactly when the source does.
For h=0 its binary table is empty and the frozen Wang expansion is the
single final M. Extra finite initial blank padding changes neither
halting equivalence nor the source tape represented by each record.

For input length n and t simulated steps, record lengths are n+2t.
The shuttle construction takes O((n+t)^2) binary steps per source step;
its finite table is fixed independently of x,n,t. No efficiency or
state-minimality claim is required for the halting equivalence.

## 4. Paid ordinary-input framing and both positive directions

The frozen Theorem7 expansion replaces every physical binary bit0 by
10 and bit1 by11, in spatial order. For a five-bit block of integer v,
let P(v)=341+2*spread_2(v), a ten-bit word. Directly,

    P(L)=351, P(R)=383,
    P(cell(b,h))=343+32b+128h.

A width10 instance of the [complete unit recoder](native_binary_input_dilation_unit179.md)
provides, at every positive zero,

    q=2^n, Q=q^10=2^(10n), 0<x<q,
    z=sum_j bit_j(x)*2^(10j), n>=2.

Make z an existential positive coordinate and introduce r>0 with the
paid equation1023r=Q-1. Then r=sum_(j=0)^(n-1)2^(10j). The exact paired
word of(1), including its first-cell head mark, is

    y=351+128*1024+343*1024*r+32*1024*z+383*1024*Q.

Using the paid repunit equation folds this to

    y=523615+401563648*r+32768*z.                   (2)

The actual source computes the right side of(2). The coefficients are
fixed numerals, and every multiplication by one is charged. Three
multiplications pay1023r,401563648r,32768z; two additions pay(2). No
supplied length, frame endpoint or uncharged bit-spreading map is used.

The unaugmented width10 recoder has138 certificate gates,15 comparisons
and36 witnesses, with182=90M+92A polynomial operations. Adding the five
gates, one comparison, r and existential z gives143 certificate gates,
16 comparisons,38 witnesses, one parameter x, and190=94M+96A polynomial
operations. `loader()` emits that entire source and finalizer, together
with its computed frame_input port. The four framing gates do not affect
the standalone zero constraint; their output is consumed by the Wang
component in Section5. They are included in the190-gate ledger.

Every positive loader zero gives exactly the word of(1) followed by the
Theorem7 pairing. Conversely every x>0 admits any sufficiently large
padded n, and the parent recoder's complete converse supplies all native
auxiliaries; the displayed positive r then extends it. This is an
existential native extension, not a claim that arbitrary off-zero
recoder tuples have typed bits. The emitted y is strictly positive on
all positive supplied tuples, before any equation, because every term
in(2) is positive. It is affine in r,z.

## 5. Complete composition and conservative size accounting

For any fixed table, let W(y,...) be the frozen computed-action Wang
polynomial of its literal instruction list. Use disjoint recoder/Wang
witness names, substitute the computed affine y, and emit

    F(x,...)=R(x,...)^2+W(y,...)^2.                 (3)

Both terms are integer polynomials, so(3) vanishes exactly when both
complete component predicates hold. The positivity and two converse
arguments above prove F has a positive zero exactly when the original
erasing source TM halts on ordinary x. The conjunction costs two
multiplications and one addition in addition to both component sources.

This packet emits the complete small loader and literal machine tables.
It does not emit the oversized whole Wang DAG. The following bound uses
the proved formula in the [packed-program compiler](wang_b_packed_program.md),
whose computed-action successor only removes gates and comparisons.
Let H be the actual number of compiled nonhalting binary states, put

    j=3H, K=16H+1, delta=1 if H>0 else0,
    L=12+K+2delta, mu(L)=floor(log2 L)+popcount(L)-1,
    C=115+7K+6L+mu(L)+delta*(j+3).

The normalized literal Wang polynomial costs at most C+45. Formula(3)
therefore costs at most C+238, including the190-gate loader and three
conjunction gates. Its complete equation metadata is25 comparisons;
its positive witness count is65+K+delta. The latter sums the computed-
action literal child's27+K+delta witnesses and the loader's38. There is
one ordinary input parameter x.

The loader inherits unit degree286 and retained-residual bound58 from
its actual width10 parent; the additional repunit residual has degree10.
Thus its product polynomial still has degree at most286+2*58=402.
Equation(2) has degree1. For literal Wang input the frozen bound is
72(2+3L)+13(3L-2)+39=255L+157, so(3) has degree at most

    2max(402,255L+157).

`machine_ledger` records these formulas and their actual finite table
sizes. For the default erasing example H=1481,K=23697,L=23711,C=312729,
which gives the stated312967 bound. It would be incorrect to label it
an exact source ledger or a numerical universal result.

## 6. Reproducible checks and scope

Run `python3 wang_b_erasing_bridge_compiler.py`. Author checks include:

* All1,344 block transitions in the default finite controller, against
  the separately executed binary rows on varied neighboring tape. The
  checks cover8,067 binary microsteps and verify the exact local output,
  head displacement and unchanged exterior.
* All64 total one-state ordinary binary tables, three inputs and two
  paddings, plus24 independently generated multi-state tables. In total
  456 traces cover1,316 ordinary TM steps and2,984,409 literal non-erasing
  steps, with324 halts. A direct ordinary-TM stepper and literal binary
  interpreter are compared at complete record boundaries. The entire
  accumulated physical tape, including old processed records, is checked.
* 2,035 exact ordinary-input morphisms and128 complete loader-output
  identities,64 signed. The latter derive the norm factors and retained
  residuals from the earlier raw recoder under its actual coordinate
  lift, rather than merely re-evaluating the new finalizer.
* Four table/size records include the initially halting case. Partial,
  stationary and invalid-target source tables are rejected. All generated
  binary rows are total and non-erasing.

These are finite trace/component checks supporting the uniform proofs;
no full positive Pell zero is constructed. The construction now removes
the missing ordinary-erasing-to-non-erasing compiler and its input-map
obligation. Instantiating a particular fixed universal table, its valid
program/input slices and a complete numerical universal schedule remains
separate work. The established universal arithmetic bounds are unchanged.

Author receipt generation and a fresh default replay pass. Independent
proof/source/fresh-default review passed with no findings; all five local
links resolve. The reviewer used a separate integer physical tape and
dictionary source-TM interpreter for152 traces across19 new tables:
560 source steps,2,267,662 binary steps,106 actual erasures,280 steps
with a negative source head and103 halts. Entire physical tapes matched
at every record boundary, including processed old records. Another60
independently concatenated input words matched the paid affine loader.
These are bounded physical executions and component identities, not
constructed complete positive Pell zeros.

Root also completed a full proof/source/fresh-default review with no
findings. Its independent integer-tape microcode audit covered15,168
complete block cases across two new multi-state tables and91,658 binary
steps, with maximum13 per block transition; whole tapes and exact head
displacements matched, including stationary block transitions. A separate
literal executor passed192 complete parent-polynomial correction
identities,96 signed, against the width10 unit recoder. Root independently
derived the framing constants and402/C+238 degree/cost bounds, with the
same distinction between the emitted loader and the bounded whole DAG.
