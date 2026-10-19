# Independent audit of the K228 transfer

## Finding and proof status

The supplied K228 table has a complete ordinary mathematical route to the
released K230 consistency calibration. I found no remaining mathematical gap in
that route after making the source interface, path normalization, initialization,
and state renaming explicit below. The necessary route uses the **direct K228
symbolic runtime proof**, rather than assuming a conditional local state fold is
valid at every possible future checkpoint.

The conclusion concerns the blank-tape machine with 228 working states, two
symbols, and a separate halting state. It is an ordinary mathematical proof
supported by reproducible finite calculations and induction schemas. **There is
no newly compiled Rocq endpoint for K228 in these artifacts.** I did not run a
Rocq compiler. The frozen K230 theorem and its proof sources are inherited from
`elliotglazer/k230-rocq` at commit
`3142e4dd980f0be12f4abb636c4ae2528afc17eb`.

The independently checked machine identities are:

| Artifact | Working states | Initial / dispatcher / halt | SHA-256 |
|---|---:|---|---|
| `machine/k228.tm` | 228 | 0 / 83 / 228 | `06726bd731f3a42e3ccd1c4189d80af74ba2d486e333045097480fcaa3313001` |
| `machine/k228_normalized.tm` | 228 | 95 / 96 / 254 | `0466c10a478b573d98ca91ea68a4159a83b15247aecd525388172f473cfe522c` |
| `source/sites_logical.json` | 5,121 source leaves | Complete binary source tree | `61450579877bc79cc4bc323ff0b8ae506064c79644107f4d818401dcfbce941b` |

The runtime receipt checks the **normalized** table. The canonical table is its
exact state conjugate; it is not the byte string named by the runtime table hash.
The distinction matters when assembling a final reproducible package.

## 1. Calibration of the source data

I independently parsed the literal `p230_tab` in the pinned
`coq/tm/Prog230.v`, without importing the construction or runtime modules. Its
5,124 internal tree nodes expand to exactly the 5,125 leaf records in the
released `upstream/k230/machine/sites230.json` after translating its instruction
names to the logical opcodes used in this package.
Consequently, the source being transformed is the actual source in the K230
theorem chain, rather than a program inferred only from similar interpreter
rows.

The four replacements were independently reconstructed from those leaves. Their
pairwise disjoint roots are:

```text
111010010010111111000011
11101001001011111110011
1110100101100011
111110011
```

At each root the old relative leaf list is

```text
00   CD 6
010  CI 5
011  CC 2
1    CI 5
```

and the new list is

```text
0    CI 5
10   CD 6
11   CC 2
```

Replacing precisely these four lists yields the supplied transformed JSON,
with no other instruction edit. I checked prefix freeness, completeness of
every binary internal node, valid instruction arguments, and maximum depth 40.
The transformed leaf inventory is 1,535 decrements, 2,054 increments, 102 breaks,
1,429 continues, and one halt. Thus the exact number of guarded runtime cases is

\[
2(1535)+2054+102+1429+1=6656.
\]

The standard structural bounds on escaping breaks and continues both vanish at
the root. For a node with children \(a,b\), these bounds satisfy

\[
B(a,b)=\max(B(a)-1,B(b)),\qquad
C(a,b)=\max(C(a),C(b)-1),
\]

where subtraction is truncated at zero, a decrement has break bound 1, and a
literal break or continue has its indicated bound. The independently computed
root triple is `(height, break bound, continue bound) = (40, 0, 0)` for both
programs. This is the ordinary finite well-formedness argument matching
`RMEquiv.v`.

The claim that the programs have 212 distinct DAG nodes counts 189 distinct
internal subtrees and 23 distinct leaf instructions. It should not be described
as 212 distinct internal decoder nodes.

## 2. The H-loop equivalence is unbounded and contextual

Write \(D=D_6\), \(I=I_5\), and \(C=C_2\). The two programs are

\[
H_{\rm old}=((D,(I,C)),I),\qquad
H_{\rm new}=(I,(D,C)).
\]

Their meaning must use the actual structured semantics in `RM.v`. A zero
decrement exits with break level 1. A break consumed through a car edge loses a
level; a continue consumed through a cdr edge loses a level, and level 1 at that
cdr restarts the corresponding cons node. Ordinary sequential reassociation
alone would not justify this edit.

Let the entry values be \(R_5=a\) and \(R_6=b\), with all registers natural.
The register indices 5 and 6 are distinct.

For the old program, the first zero test when \(b=0\) exits its inner loop and
executes the final increment. When \(b>0\), the initial successful decrement,
the increment, and the continue execute one loop cycle, leaving values
\((a+1,b-1)\) at the same inner-loop entry. There are exactly \(b\) such cycles,
then the zero decrement and the final increment. Its unique normal exit is

\[
(a,b)\longmapsto(a+b+1,0).
\]

For the new program, the initial increment occurs before testing the decrement.
At zero the inner cons consumes the decrement's break and the whole program
exits normally. At a positive value the continue restarts the outer cons,
so the next increment occurs at the start of the next iteration. Induction on
\(b\) gives the same unique normal exit. Both programs execute exactly
\(3b+2\) primitive source instructions, of which \(b+1\) are increments and
\(b\) are successful decrements. No other register changes.

This argument proves termination for **every natural** \(b\); it is not a check
of small inputs. The finite induction also excludes any divergent execution
inside either replacement. Neither subtree contains halt or allows an escaping
break or continue.

### Why arbitrary surrounding structured control is allowed

The relevant contexts are occurrences in the **unfolded structured source
tree**, entered from their root. The claim does not identify arbitrary numeric
instruction pointers initially placed inside the two different subtrees.

From an instruction outside a complete occurrence, increment goes to the next
subtree in the structured traversal. Break first strips to an ancestor boundary
and then increments; continue strips to an ancestor boundary and starts its
leftmost traversal. If such a transfer enters the occurrence at all, its first
instruction is the occurrence's entry instruction. An ancestor of an outside
instruction cannot be a proper internal node of the occurrence. Thus external
structured control cannot jump past the entry to a different internal leaf.
Sharing decoder states does not add such source-language jumps: each occurrence
is analyzed in the unfolded source, and the direct runtime theorem checks all
resulting leaf paths.

At the old occurrence's final increment, the source successor is
\(\operatorname{inc}(p1)\), where \(p\) is the occurrence root. At the new
occurrence's final zero decrement, stripping the last zero from \(p10\) gives
\(p1\), so its source successor is exactly the same
\(\operatorname{inc}(p1)\). The contextual exit is therefore identical, including
the root-overflow case.

One can now contract each occurrence to an atomic instruction with the total
register function just proved. Outside the four occurrences, both programs
have identical instructions and contextual successors. As an independent finite
cross-check, I compared all 6,639 outside nonhalting guarded edges and found them
identical after this contraction. Each occurrence has precisely one external
incoming edge, and that edge reaches its entry in both programs.

For a finite halting computation, expand or contract every visited occurrence
using its positive finite execution. This transfers halting in both directions.
For an infinite execution, either infinitely many contextual steps occur or
execution would eventually stay inside a single occurrence. The latter is
impossible by total termination of the occurrence. Infinitely many contextual
steps expand to infinitely many source instructions, since every expansion has
positive length. This establishes preservation of divergence as well as finite
halting, for every natural register file at the whole-program entry.

At the interpreter level, increments append spare blocks and positive decrements
increase the available gap. The direct runtime theorem quantifies over those
auxiliary data. Moreover, both H variants execute the same number of each
operation and have the same contextual overflow, so their exit spare lists and
gap increments can also agree. No finiteness bound on the surrounding execution
is being assumed.

## 3. Audit of the quantified symbolic runtime rules

The portable active checker is `verification/verify_k228.py` calling
`prove_blocks` and `case` in `verification/kernels/runtime_engine.py`. The
latter uses the literal table parser, physical permutation, increment, and strip
operations from `runtime_support.py`. The retained discovery versions are
`symbolic_runtime.py` and `independent_runtime.py`; their bytes are kept for
historical receipt pinning, and their legacy command-line entry points are not
part of the portable replay.

### Tape representation and arbitrary parameters

At the normalized dispatcher 96 the tape frame has a single marker 1 immediately
to the left of the head, then to its right a source path, enough zeros to place
the header at distance \(64+g\), the header 1, and the register blocks. With

\[
B(v)=0\,1^{v+1},\qquad C(v)=1\,0\,1^v,
\]

the file consists of nine primary \(B\)-blocks, one arbitrary spare
\(B\)-block, an arbitrary finite list of further spare blocks, and the all-zero
exterior. There are therefore at least ten blocks. Every finite valid spare list
is represented by choosing its first element and its possibly empty tail.

The affine variables are: a nonnegative additional gap, nine independent
natural primary values, an independent first-spare value, and the width of the
remaining spare list. A decrement's zero branch substitutes exactly 0; its
positive branch substitutes \(1+v\). These two branches exhaust the naturals
without imposing any relation on the other register values.

The spare-tail width denotes
\(\sum_{v\in S}(v+2)\) for the actual finite tail \(S\). It is not an assumption
that every width is independently realizable by every list. Algebraic checking
with a nonnegative formal width is stronger than is needed after making this
substitution. The empty tail is allowed and has width zero.

The exact logical-to-physical map is

\[
\operatorname{phys}=(6,2,0,4,3,7,8,5,1),
\]

which agrees literally with `Interpreter230Check.phys_of`. Interchanging this
with the inverse physical-order list would break calibration; the actual helper
uses the correct map.

### Literal and unary rules

The symbolic tape is a directional zipper. Its left and right lists are nearest
cell first, and the direction records which list contains the current cell.
For a reversal, the just-written cell stays on the old side and the current
side changes. For a step continuing in the scan direction, the cell moves from
the current side to the opposite side. These are exact tape updates. The
explicit motion accumulator separately records the physical head displacement.

A literal rule consumes a cell only when the affine run length has constant
term at least 1. All coefficients of every represented run length are checked
nonnegative. Thus no potentially empty variable run is read without proof that
a cell exists.

A unary rule is used only for a row which returns to the same control state and
moves in the current scan direction. Induction on the natural run length proves
that the whole run can then be traversed, applying the row's write symbol to
each cell. Length zero is the identity; positive length is one literal step
followed by the induction hypothesis. This remains valid if the row changes the
symbol it reads, because the head does not revisit the cells it just wrote.

### The four list lemmas are checked on the modified table

The checked entry schemas, on normalized labels, are:

| Entry | Direction | Input block | Output block | Steps |
|---:|:---:|:---:|:---:|---:|
| 64 | R | \(B(v)\) | \(B(v)\) | \(v+2\) |
| 95 | R | \(B(v)\) | \(C(v)\) | \(v+2\) |
| 40 | L | \(B(v)\) | \(B(v)\) | \(v+2\) |
| 97 | L | \(C(v)\) | \(B(v)\) | \(v+2\) |

Entry 95 is the renamed original state 0. The normalization swaps 0 with 95,
and 84 with 96, and changes the terminal label 230 to 254. Thus adopting 95 as
the list-conversion entry is necessary; the old original state 95 would be a
different routine.

Each schema is rederived from the supplied K228 rows with an arbitrary natural
block value and opaque contexts on both sides. Its proof is not allowed to read
either opaque exterior. It finishes at the same control state and scan
direction after traversing and rewriting exactly one block. Induction on a
finite list then justifies the list rule, with duration its total width. The
empty-list case is the identity. The use of an opaque list atom therefore does
not impose a finite bound on the number or values of its elements.

The list normalization identity is

\[
C(S)\,1=1\,B(S),
\]

and its reversal. For one element this is the literal identity
\(1\,0\,1^v1=1\,0\,1^{v+1}\). The empty case is immediate, and applying the
one-element identity and the induction hypothesis proves the finite-list case.
Other normalization steps only concatenate adjacent equal-symbol runs, delete
zero-length runs, or absorb finite trailing zeros into the all-zero exterior.
All preserve the full represented tape.

### What a successful case proves

For each nonhalting source instruction and guard, the checker reaches the exact
successor dispatcher frame, including both tape exteriors, the register file,
the spare list, and head displacement. At a halt leaf it reaches terminal state
254. There are no outgoing rows from 254, so a nonhalt case cannot silently
pass through a halt and later return to its target frame.

The computed duration is an affine expression whose coefficients are all
nonnegative and whose constant term is positive. I independently checked this
condition on all 6,656 stored case records; the minimum constant term is 13.
The 4,000-rule limit bounds the construction of the symbolic proof, not the
concrete runtime, unary values, gap, or spare-list length. The largest successful
proof here uses 415 symbolic rules.

The stored receipt and case data have consistent hashes and exactly the ordered
site/guard coverage implied by the transformed source. They record 1,614,426
symbolic rules in total. The independently checked used-row set is all 456 rows.
Row coverage is useful bookkeeping; the universal simulation follows from the
rules and the exact target comparisons, not merely from coverage.

## 4. Stitching leaf cases into an unbounded program execution

This bridge must be stated explicitly because the runtime checker starts a case
with a **full leaf path**, whereas source increment and strip may return a
shorter prefix or a longer path with trailing zeros.

Let \(P\) be a source instruction pointer. Walking the finite tree with implicit
trailing zeros reaches a unique leaf at depth \(d\le40\). Let \(p\) be the
\(d\) bits actually consumed. For every reachable pointer, all bits of \(P\)
after position \(d\) are zero. This is the generic `RMEquiv.no_stray` argument:
strip returns a prefix of the previous leaf path; increment either becomes all
zeros or flips the last relevant zero and replaces the later bits by zeros.
Such a transfer cannot leave a nonzero bit after the depth of the next leaf.

I also independently checked this property on every nonhalt successor of every
old and new leaf/guard: 13,314 finite structural edges in total. Since it holds
after every source step, this finite check supplies an alternative direct
induction for this particular transformed program.

Consequently the physical word representing \(P\), followed by its zero padding,
equals the word representing \(p\), followed by the correspondingly shorter or
longer zero padding. The header stays at the same place. This lets every exact
successor frame of one case serve as the exact input frame for the next leaf
case. The initial pointer is empty and reaches the first leaf `000`; its tape
already has the required zeros.

For clarity, the auxiliary gap and head updates established by the cases are:

| Source operation | Pointer | Register change | Spares | New extra gap | Head change |
|---|---|---|---|---|---|
| Increment \(j\) | \(\operatorname{inc}(p)\) | \(R_j+1\) | Append value 1 | \(g+o\) | \(-o\) |
| Positive decrement \(j\) | \(\operatorname{inc}(p)\) | \(R_j-1\) | Same | \(g+1+o\) | \(-o\) |
| Zero decrement | \(\operatorname{inc}(\operatorname{strip}_0^1(p))\) | Same | Same | \(g+o\) | \(-o\) |
| Break \(k\) | \(\operatorname{inc}(\operatorname{strip}_0^k(p))\) | Same | Same | \(g+o\) | \(-o\) |
| Continue \(k\) | \(\operatorname{strip}_1^k(p)\) | Same | Same | \(g\) | 0 |

Here \(o\in\{0,1\}\) is the overflow of the indicated increment, including the
empty-prefix case. Overflow restarts the main source program with an all-zero
pointer, as specified by `RM.v`; it is not an implicit source halt. All new gaps
remain nonnegative, the spare list stays finite and nonempty at every finite
stage, and the nine primary values remain natural.

Induction now simulates each finite source prefix by an actual finite TM run.
If the source reaches its halt leaf, the corresponding halt case gives a finite
TM halt. If the source continues forever, the positive block durations give
strictly increasing TM checkpoint times, bounded below by the number of source
steps. They cannot accumulate at a finite time, and no block can contain an
unaccounted halt. Thus the TM also continues forever.

Conversely, suppose the TM halted after \(t\) steps from a valid dispatcher
frame while the source never reached halt. Simulating \(t+1\) nonhalting source
steps gives a defined deterministic TM run longer than \(t\), contradicting
that halt. This proves the reverse direction without assuming that local
existence of finite simulations alone automatically implies reflection of
halting.

## 5. Exact blank initialization and state renaming

I ran a separate dense-array implementation, with a bounds assertion on every
read, directly on the frozen release and on the canonical K228 table. No
construction or runtime-checker code was imported. The original machine after
408,419 steps and K228 after 409,835 steps have the same entire tape and head
position. Both simulations stay between positions -15 and 701, safely within
the represented array. Every cell outside the array remains blank because none
is read or written.

The K228 final canonical state is 83, corresponding to original dispatcher 84
and normalized dispatcher 96. The head is at -5; the marker is at -6; the header
is at 176. There are 351 one-cells, the last at 701. Decoding the full file gives

\[
[0,0,0,3,0,0,3,0,0]\;{+\!+}\;[1]^{167}.
\]

Under the calibrated physical map, the nine logical values are

\[
R_0=[3,0,0,0,3,0,0,0,0].
\]

This is exactly `Prog230.R0 = upd (upd regs0 0 3) 4 3`, and the released source
theorem identifies it with `seed230`. The header is 181 cells to the right of
the head, so the runtime parameter is \(g=181-64=117\). The spare sequence has
167 entries of value 1, meeting the nonempty-spare premise. There is no assumed
or externally supplied initialization tape.

The supplied startup receipt additionally checks all 409,692 mapped checkpoints
of the 409,691-step H-loop K229 predecessor bootstrap and gives the 144-step
delayed-erasure overhead. Its six visits to the exceptional right-neighbor
guard satisfy that guard literally. These are exact finite startup facts.

I checked both renumberings row by row: sources, targets, read/write symbols,
directions, start, and halt. The old-label K228 state set is exactly the release
state set minus 79 and 140. The canonical state set is exactly
\(\{0,\ldots,227\}\), with 456 total working transitions and sole external
target 228. A bijective state renaming preserves every finite transition and
therefore finite and infinite runs on every tape.

## 6. The conditional delayed-fold premise is not an outstanding global axiom

The local delayed-erasure proof explicitly requires

\[
q=140\land t(h)=1\quad\Longrightarrow\quad t(h+1)=1.
\]

The incoming transition inventory does not imply this fact. The local checker
correctly labels its result conditional, and the finite startup check only
discharges the finitely many startup uses. Neither statement alone would prove
unbounded blank-halting equivalence by a one-old-step fold simulation.

There is nevertheless a complete route here: the final K228 table itself passes
the quantified instruction-frame proof. That proof derives all of its traversals
from the final rows and does not use the conditional old-state simulation as a
premise. The exact new blank initialization starts the induction on valid
frames. Thus no unproved assertion about every future old state-140 checkpoint
is needed. The same direct-runtime approach also avoids making the separate
79-to-63 fold theorem a necessary logical premise of the endpoint transfer.

The local fold proofs explain the construction. The source equivalence, direct
new runtime proof, and exact new initialization establish the endpoint.

## 7. Scope of the transferred consistency statement

The resulting ordinary proof chain is

\[
\begin{aligned}
\operatorname{Halt}_{\rm blank}(K228)
&\iff \operatorname{Halt}(P_H,([],R_0))\\
&\iff \operatorname{Halt}(P_{230},([],R_0))\\
&\iff \operatorname{Thm}_{230}(1)\\
&\iff \operatorname{StandardZFC}\vdash\bot.
\end{aligned}
\]

The first line is the direct runtime, finite initialization, and exact
renumbering argument audited here. The second is the contextual H-loop theorem.
The final lines use the released K230 source and theory calibration, reviewed
separately in `K230_THEORY_AUDIT.md`; in particular, they do not infer the
meaning of the edited table merely from the unchanged theorem about K230.

Negating the endpoints gives blank nonhalting iff `Con(StandardZFC)`. The new
arguments use finite syntax, elementary inductions, exact tape identities, and
finite computations and can be carried out in ZFC. These artifacts do not
contain an internally encoded ZFC proof object or a fresh Rocq declaration
certifying that conclusion for the 228-state table. An integration report should
state the ordinary mathematical theorem and the absence of a new kernel endpoint
as two separate facts.

## 8. Evidence produced by this independent audit

`verification/audit_transfer.py` imports only Python standard-library modules.
It produces `transfer_audit.json` (delivered under `receipts/audit/`) by
independently checking the following:

- The actual Coq source expansion and its identity with both released and local
  baseline leaf lists.
- Exact four-occurrence source replacement, instruction coverage, tree
  completeness, depth, escape bounds, no-stray successors, and contextual
  incoming/outgoing edges.
- Exact row conjugacy between old-label, normalized, and canonical K228 tables.
- A fresh full blank bootstrap of canonical K228 and of frozen K230, with tape
  bounds checked on every read and the resulting register file decoded.
- Hash consistency of the runtime, case, helper, source, and startup artifacts;
  exact ordered guard coverage; positive affine durations; and the complete
  used-row inventory.

I inspected the symbolic rule implementation and its four one-block derivations.
The independent audit checks the complete runtime receipt without rerunning the
symbolic engine. A fresh complete portable runtime replay is supplied separately
under `receipts/replay/runtime/`, pinned to the inspected engine and helper; it
took about 119 seconds in the preparation environment. The audit was then
replayed against that complete portable receipt. The independent checks above
cover the finite interfaces most likely to invalidate composition even when
the instruction calculation passes.

The retained discovery file `symbolic_runtime.py` contains an inactive
`validate_inputs` function with an old source count and hash. It was not a
premise of the discovery run. The portable `runtime_engine.py` omits that
function; `verify_k228.py`, `build_h229.py`, and this audit supply the active
input pinning, source validation, and calibration. The extraction audit checks
the retained computational definitions separately.

All upstream theorem references in this note refer to the pinned source tree at
<https://github.com/elliotglazer/k230-rocq/tree/3142e4dd980f0be12f4abb636c4ae2528afc17eb>.
The decisive primary files are `coq/tm/RM.v`, `RMEquiv.v`, `Prog230.v`,
`Interpreter230Check.v`, `Boot230.v`, `Sim230.v`, `Sim230Main.v`,
`coq/prog/Main230.v`, and `coq/tm/Correct230.v`.
