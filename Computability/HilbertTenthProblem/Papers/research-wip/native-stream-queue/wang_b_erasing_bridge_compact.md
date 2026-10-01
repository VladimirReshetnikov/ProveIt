# Compact records and a literal Wang compiler

The same illustrative erasing machine previously compiled at312942
operations now has a complete emitted polynomial with
**41286=15648M+25638A**, **41210 certificate operations**,25 comparisons,
3153 positive witnesses and degree **at most1581824**. The only parameter
is ordinary positive binary input x. Every emitted gate reaches the output.
This is an improvement to the finite compiler and its illustrative example;
no fixed universal transition table or new universal bound is claimed.

The [source](wang_b_erasing_bridge_compact.py) and
[receipt](wang_b_erasing_bridge_compact.json) implement three explicit
changes: four-bit records, a finite control quotient, and a variable-length
Wang expansion. The default has764 binary states before quotienting,
377 afterward, and2362 Wang instructions, with725 jumps and3087 control
edges. The [historical five-bit compiler](wang_b_erasing_bridge_compiler.md)
and its [312942 materialization](native_binary_dependency_projection.md)
are unchanged.

## 1. Exact four-bit record protocol

The ordinary source convention is unchanged. A table has states0,...,h,
start0, unique halt h, and one(write,L/R,target) row for each read bit in
every nonhalting state. State h has no transitions. Erasures are allowed;
stationary moves, partial rows and invalid targets are rejected. A move
into h performs its write and displacement before halting. An empty table
starts halted. Ordinary x>0 has bit_j(x) at cell j>=0, zeros elsewhere,
and head0 on the bi-infinite tape. Any n>=max(2,bitlength(x)) supplies the
same source tape with extra finite blank padding.

Use aligned four-bit blocks with integer codes

    empty=0, L=2, R=6,
    cell(b,h)=1+2b+4h, processed(v)=v+8.             (1)

The four cell codes1,3,5,7 are distinct from both delimiters2,6 and the
empty block. All six unprocessed symbols are nonzero and below8; their
processed copies are above8 and distinct. There is no separate presence
bit. The record algorithms need only the tests zero, exact L/R/cell, and
processed, which(1) preserves.

This is an exact finite-alphabet restriction and relabeling of the frozen
five-bit protocol. For v=0,...,15 define

    phi(v)=d[v mod8]+16*floor(v/8),
    d=(0,1,3,5,2,9,7,13).                          (2)

Thus phi sends empty to empty, L/R to the old3/7,
cell(b,h) to the old1+4b+8h, and processed flags to processed flags. The
unused unprocessed code4 goes to the old invalid code2. The image has
sixteen distinct symbols. For every reachable block control and every
one of these symbols, the old transition writes a symbol in that image.
The source emits the new transition by applying phi, the old literal
block transition, and phi inverse to its written symbol. It checks
closure and v OR write=write on every emitted row. This is a finite table,
not an assumed alphabet conversion or a run-time encoding operation.

For clarity, the valid-record invariant is the same constructive one as
in the parent. Each step marks the old L, appends a fresh L, and consumes
the old cells in order. A delayed cell carries the new left blank or the
previous source cell. At the unique source head a left move marks that
buffer's head; a right move sets a pending flag for the following cell.
Each consumed source cell is marked processed, its delayed predecessor
is appended on the fresh zero frontier, and the return scan finds exactly
the rightmost processed source block. The unconsumed source suffix and
new record are unprocessed. At old R, the last buffer, new right blank
and new R are appended. The scan back finds the nearest L, the new one.
The source state is held in finite control throughout.

Consequently the next record represents the exact successor source tape
on an interval extended by one blank at each end. Only old processed
bits and fresh blank output blocks are changed. The unique new head and
full old records remain correct even after an erasure or either boundary
crossing. All scans are finite, and the only simulation halt is entry
with stored source state h after finding the new L. Induction proves both
halting directions, for every permitted initial padding.

## 2. Literal binary expansion and exact control quotient

At an aligned block origin, the binary expansion reads four bits into
finite control while preserving them. The fourth read selects the block
transition. If only bit3 changes, it writes that bit and walks directly
to the requested adjacent origin. Otherwise it walks left while writing
the desired low bits by OR, then walks to the requested origin. A
stationary block transition uses a right-left detour. Every output row
has movement L or R and every read1 row writes1. The starting state is0,
and the unique halt is numbered last.

This expansion has at most11 binary steps per block transition. Its
movement is exactly-4,0 or4, its written block is the specified code,
and all other bits are preserved. Finite write/walk tails are shared
only when their literal control parameters agree. For the default table
there are42 block controls and764 nonhalting binary states.

The quotient begins with all nonhalting states in one class and halt in
a distinct class. Refine each nonhalting class by its two signatures

    (write_bit, movement, target_class), for read0 and read1.           (3)

Refinement cannot merge classes and terminates on the finite state set.
At a fixed point, any two states in one class have the same write and
movement for either bit and reach the same next class. The emitted
quotient uses one representative row per class. The source verifies(3)
for every original transition, keeps halt separate, and numbers the
start class0 and halt last.

Induction on actual binary steps now gives a bisimulation on arbitrary
binary tapes: original and quotient have identical physical head and
whole tape, with state related by the class map. They halt at exactly
the same step. This proof is stronger than agreement on the finite
fixtures and does not assume a valid record. Applied to the default,
it gives377 nonhalting states. No smallest-machine claim is made.

## 3. A shorter exact paired Wang expansion

The [primary2014 paper](https://mural.maynoothuniversity.ie/id/eprint/12409/1/Woods_Wang_2014.pdf),
Definition6 and Theorem7, printed pp637–639, defines the Wang instruction
model and the physical encoding0->10,1->11 used by the
[frozen non-erasing bridge](wang_b_nonerasing_tm_compiler.md). The new
compiler preserves that pair convention and proves its shorter literal
macros directly. It does not invoke the paper's copying overview as an
unspecified transition table.

At a state entry the head is on the first, marked bit of the current
pair. Let j(q) be the computed one-based address of state q's code, and
write J(q) for the actual instruction J(j(q)). An adjacent pair may be
entirely blank; arriving there and executing M initializes its first bit
without changing its zero data bit. Let

    V_R=R, V_L=L,L,L.                              (4)

These move from the second bit of a pair to the first bit of its right
or left neighbour respectively. The compiler uses three cases:

* If both binary transitions have the same direction d and target q,
  and read0 writes0, they copy the bit. Emit d,d,M,J(q). This moves
  directly between first bits, initializes the destination, and jumps.
* If both transitions have the same d,q and read0 writes1, both write1.
  Emit R,M,V_d,M,J(q). This marks the current data bit, moves, initializes
  the destination and jumps.
* Otherwise emit R,J(one), then the read0 block
  `[M if write0=1],V_d0,M,J(q0)`, followed by the read1 block
  `V_d1,M,J(q1)`. The first J tests the current data bit; its target is
  the calculated address of the read1 block. The last J of either arm
  is unconditional because the immediately preceding M marked its cell.

The first two cases use4 or5/7 instructions. A general state block has
8 through13 instructions; repeated padding marks are unnecessary because
all following addresses are computed from actual block lengths. Every
jump target is an actual one-based address. The sole final block is M,
whose fall-through is the sole Wang halt. For an empty binary table the
entire program is that one M.

The macros preserve exactly the source data bits, update precisely the
written bit, make the prescribed one-cell binary move, and arrive at the
correct marked first bit and state address. An initialized finite pair
interval therefore grows exactly when a new neighbour is entered. All
other pair data and the exterior remain unchanged. Induction gives exact
whole-tape simulation, including arbitrary left exterior extensions.
Each macro finishes in finitely many instructions, and only the binary
halt reaches the final M; hence both halting directions hold.

The default377-state quotient emits2362 instructions and725 jumps,
instead of the4902 instructions and1131 jumps its unmodified13h+1
expansion would use. Its literal instruction list is passed to the
existing chronological Wang compiler; no control-flow edge is free.

## 4. A complete ordinary-input loader of189 operations

For a four-bit record v, its eight-bit paired word is
P(v)=85+2*spread_2(v), where the least significant bit is the physical
leftmost bit. Direct substitution gives

    P(L)=93, P(R)=125, P(cell(b,h))=87+8b+32h.

The initial record is L,cell(bit0(x),1),cell(bit1(x),0),...,R. A width8
complete recoder supplies, at every positive zero,

    Q=2^(8n), z=sum_i bit_i(x)*2^(8i),
    n>=2, 0<x<2^n.

Introduce positive r and the paid comparison255r=Q-1. Then
r=sum_(i=0)^(n-1)2^(8i), and the exact finite paired input is

    y=93+32*256+87*256*r+8*256*z+125*256*Q
     =40285+8182272*r+2048*z.                       (5)

The source charges three multiplications, for255r and the two variable
terms, and two additions. All fixed coefficient multiplications count.
The output y is positive on every positive supplied tuple, before any
comparison. The entire loader emits142 certificate gates,16 comparisons,
38 positive witnesses, and **189=93M+96A** polynomial operations, with
degree at most348. Its four affine framing gates feed the subsequent
Wang source; they are counted even though its standalone zero finalizer
does not consume y.

Every loader zero supplies the exact input word above. Conversely every
ordinary x admits sufficiently large n; the complete recoder converse
supplies its native auxiliaries and the positive repunit r. This uses
fresh native witnesses, without asserting typed bits on arbitrary
nonzero tuples.

## 5. Whole source, positivity and actual ledger

Let R(x,...) be the complete loader output and W(y,...) the complete
computed-action Wang output for the actual finite program. The emitted
source uses disjoint witness/register namespaces, substitutes the paid
positive y, and appends exactly three gates for

    F=R^2+W^2.                                     (6)

Over integer assignments, F=0 iff both complete component outputs vanish.
Their positive converses, (5), and Sections1–3 give a positive zero of F
exactly when the original erasing source TM halts on ordinary x. This is
a theorem for every fixed total source table, not merely the default.
For an infinite source computation each simulated step is finite and no
halt block is entered, so no false finite accepting history is introduced.

The default source is actually materialized:

| Component | Operations | Certificate | Comparisons | Witnesses | Degree bound |
|---|---:|---:|---:|---:|---:|
| Compact Wang child |41094=15553M+25541A|41068|9|3115|790912|
| Paid framed loader |189=93M+96A|142|16|38|348|
| Full conjunction |41286=15648M+25638A|41210|25|3153|1581824|

The upper degree of (6) is twice the larger component bound. The affine
y does not increase the child's degree. The new repunit comparison has
degree at most8, below the width8 recoder's already accounted outer
residual degree50. These are conservative complete-source degree bounds;
no exact whole degree is claimed.

`build(table)` emits the actual certificate and component metadata;
`polynomial_source(packet)` emits every gate of (6). The ledger checks
unique producers, available operands, distinct witness names and the
whole output ancestor set, then records the source hash. Thus the41286
count is neither a formula-only bound nor an unexpanded macro count.
The unchanged illustrative source machine has one nonhalting state;
both rules erase the read cell, move right and halt. It is not universal.
A concrete universal table and a paid compatible input/program slice
remain a separate application obligation.

## 6. Verification scope

The checker covers every complete default block row, including invalid
blocks, against the literal binary table and quotient. It separately
executes all one-state non-erasing transition pairs through the compact
Wang macros, with initialized and blank neighbours and odd/even spatial
shifts. Whole-record tests independently execute erasing source TMs and
compare every physical old/new record after each simulated step; selected
runs also execute the literal Wang list and compare the entire paired
tape. The empty initially halted machine is included.

The affine loader is compared with directly concatenated physical words
and with the original raw recoder residual oracle on signed and positive
assignments. Whole-source checks independently restore the raw Wang
comparisons, apply its guarded unit correction, and verify every renamed
register and the squared conjunction. Edge words are fixed to their
bounded off-zero value for these large-source algebra checks. They are
not constructed full positive Pell zeros. The receipt gives exact totals.

Author writer PASS. Exact checks cover672 block rows/3266 binary steps,
1528 quotient transitions,576 compact Wang cases/3420 instructions, and
439 whole source traces/1131 source steps/1711032 binary steps. The83
whole Wang runs use1526360 instructions. The traces include173 erasures,
571 negative-head source steps and306 halts. There are2035 direct framed
input identities,128 raw-loader output identities(64 signed), and32
complete raw-oracle composition identities(16 signed), including the
initially halted table. These are finite execution/algebra checks, not
full Pell-zero constructions. Historical packets and helpers are unchanged.
Author fresh default replay also PASS.

Root's independent full proof/source/fresh-default review PASS, no
findings. It rederived the alphabet relabeling, record invariant,
binary head offsets, halt-preserving quotient, all three Wang cases,
the exact input coefficients and the degree bound. Its separate Wang
interpreter checked1408 local cases across64 additional random tables
with2 through9 nonhalting states, executing8614 instructions and
checking whole local tapes, both read symbols, blank/initialized
neighbours and arbitrary spatial shifts.

Franklin's independent full proof/source/fresh-default review PASS,
no findings. Its own physical-record interpreter checked52 whole traces
across13 tables:182 source steps,436804 binary steps,31 erasures,
98 negative-head source steps and28 halts, with36158 quotient rows
checked. A separate Wang interpreter checked720 multi-state macro cases
and4446 instructions;70 independently assembled input words verified(5).
All five local links resolve. Source and receipt are frozen; these
additional finite checks retain the scope stated above.
