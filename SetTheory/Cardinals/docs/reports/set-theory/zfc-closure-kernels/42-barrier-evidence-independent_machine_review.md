# Independent review of the 252-state blank-start construction

## Verdict and scope

I independently inspected the frozen standalone package's transition-table
generator, finite-prefix simulator, periodic-segment simulator, register-graph
macro recognizer, exact arithmetic DAG, uniform site checker, and recorded
root frame. I then copied the package into a fresh directory and reran its
complete offline reproduction. The run passed, including exact comparison
with every stored certificate, in 9.07 seconds.

Together with the separately reviewed monotone DROP theorem, the construction
supports an ordinary mathematical proof in ZFC that the displayed 252-state
blank binary machine halts exactly when C254 derives falsity. Composing the
inherited published C254/ZFC calibration gives the requested equivalence
between nonhalting and Con(ZFC).

The new chain is not a complete Coq or Lean kernel build. Its new finite
computational proof is executable Python plus the supplied ordinary proofs,
using the generic register-file excursion lemmas proved in upstream Coq.
The generic fresh-selector and stack-counting Lean lemmas in the main report
are separate partial formalizations. I found no outstanding mathematical
defect in the new construction; the inherited program/logic calibration and
the distinction from an end-to-end kernel theorem must remain explicit.

The independent replay is at
`/tmp/repo_audit_runtime252_final__2gcgx32/replayed`; its stdout and stderr
are saved beside that directory. These are review-workspace paths, not
dependencies of the delivered standalone reproduction.

## 1. Exact machine identity

`generate_machine.py` checks the complete table difference against the pinned
254-state original. The only changed surviving transition is

\[
 (3,0):\quad 0L5\longmapsto0L48.
\]

The deleted working states are 5 and 8. In the old labels, blank execution
starts at state 64 and the terminal state is 254. Renumbering places this
start at 0, lists all 252 working states as 0 through 251, and uses 252 as
the separate terminal state. Every working state has both binary transitions.
All targets are valid after renumbering. No unused input word or nonblank
initial tape is part of this specification.

The distributable table has SHA-256
`5919a993e3c539c91636cdeb1a43461e630ad43bd03e39faed141202a6945987`.
The old-label form has SHA-256
`2edff39278ffa1dd3ab76903f0d12aa45afdcc3f86e5352827db974d9ea3eb4b`.
This runtime table was known in prior work. The new contribution is the
complete successful blank-bootstrap analysis and the argument allowing its
dirty logical stack, not inventing or reattributing the already known fold.

## 2. The literal prefix retains the whole tape

The first 999,186 steps are ordinary one-step sparse simulation of the
complete modified table, starting from the empty set of nonzero tape cells.
The checkpoint checks state 96, absolute head 4, a gap of 32, all nine
physical register values, all 359 spare block values, and every nonzero cell.
Repainting the proposed frame must reproduce the complete sparse tape set,
not merely a selected window. The four nonzero spare block values are
retained explicitly. No old data to the left of the PC marker is omitted.

## 3. Exact finite periodic tape acceleration

`periodic_tape252.py` represents finite segments as a finite bit pattern plus
an exact natural-number cell length, with implicit blank tape beyond the
represented finite support. Its representation supports either head-facing
orientation, and reversal is handled explicitly when crossing a segment.

A bulk skip is permitted only when every transition in a finite cycle moves
in the same direction, the machine returns to the same state, and the input
pattern returns to the same phase. The number of skipped copies is an integer
quotient of the available segment length. Written bits are placed, in the
correct reversed order, behind the advancing head. The state and input phase
return exactly, so induction on the number of copies proves the skip. A
halting state cannot be skipped, since it would stop the finite cycle check
before a return to the original working state.

The two header-repair segments are handled with this literal transition
method rather than a presumed register interpretation. Their complete tapes
are then reparsed. A dispatch checkpoint requires exactly one left marker,
a valid path followed by a zero gap, all nine complete register blocks, and
a completely parseable finite spare tail. The physical head is recorded.
The full reproduction includes 11,788 independent comparisons against a
one-step sparse simulator on deterministic controls.

The enormous recorded TM step counts for the two periodic repairs are counts
of those repair segments. They must not be described as the total blank-to-root
time: the intervening register macros have their own much larger computations.
The proof requires finiteness, not expansion of the entire startup timeline.

## 4. Register macros are recognized graph shapes

The macro recognizer works from the pinned literal 6,459-node register-program
table. It does not infer a macro from a few matching executions. It verifies
the exact finite instruction/control graph for transfer, pairing, and
unpairing, including every positive guard branch, zero exit, and intervening
break/continue path. The local binary-machine contract is checked for every
instruction branch occurring in any accelerated macro at the actual gap.
If a short-gap zero exit fails, only a separately valid positive transfer
loop is accelerated, stopping precisely at the failing zero guard.

For a transfer from r, each cycle decrements r once and increments its
specified distinct destinations. It therefore runs r times and has the
recorded linear register, step, and positive-decrement effects.

For a pair macro, write the three distinct source/temporary/destination
registers as x,t,y and n=x+t. One iteration copies t into x,y, tests/decrements
x, increments y, and transfers the remaining x back to t. Summing the
decreasing loop sizes gives

\[
 y'=y+P(x,t),\qquad x'=t'=0,
 \qquad \#\text{positive decrements}=t+n^2.
\]

The recorded step formula counts the recognized copy and transfer cycle
lengths, their zero exits, and the intervening control instructions. The
triangular-number factors also handle n=0 correctly.

For an unpair macro, each positive source decrement performs exactly one
successor step in Cantor order on (x,y): it sends (x,y) to (x-1,y+1) when
x>0 and sends (0,y) to (y+1,0) otherwise. Starting with source r, its output
is therefore unpair(P(x,y)+r) and r'=0. If a=x+y and b=x'+y', the number
of wrap steps is b-a. Summing their transfer lengths yields the recorded
decrement count

\[
 2r+\frac{(b-a)(a+b-1)}2.
\]

The corresponding instruction-count formula uses the same exact wrap count
and sum. These derivations justify arbitrary natural inputs; the 2,172
small direct graph tests are diagnostic controls rather than the general
proof. Register aliases prohibited by each formula are excluded by the
recognizer's source/destination checks.

I additionally checked all control successors in the full program:
8,387 nonoverflow branch successors discard only zero suffix bits when
canonicalized, and three branches overflow. Thus the graph interpreter does
not silently discard a live PC bit while padding paths with zeros. None of
the 7,784 distinct cases used inside the accelerated macros crosses a root
or overflow boundary.

## 5. Symbolic natural arithmetic does not guess branches

The final stage retains exact expressions in a shared DAG using integer
constants, addition, subtraction, multiplication, integer division, and
Cantor pairing. It performs only exact simplifications. In particular,
unpair(pair(a,b)) cancels structurally, and a nonstructural unpair is evaluated
only when its exact integer size is small enough. An unresolved large unpair
or zero test raises an explicit undecided-result exception and prevents the
success certificate.

Structural zero tests for sums and pairings use nonnegativity of register
values. This invariant is supplied by the recognized natural-number macros
and by decrementing only on a positive branch. The internal arithmetic
expressions for step counts can contain intermediate subtraction terms;
their closed-form derivations establish the resulting nonnegative counts.
Such count expressions are not used as unproved register-branch assumptions.
Loose bit-length bounds decide only whether an exact calculation is feasible;
they are not used to decide numerical equality or inequality.

The successful replay produces the same 6,321 DAG nodes and the same complete
1,210-operation final-stage ledger. Its terminal physical registers are

\[
 (\mathrm{WS},0,0,0,0,0,0,\mathrm{TW},0),
\]

where WS and TW are two specified exact DAG expressions. The other seven
registers are the literal zero node. It also explicitly records the sole
normal overflow, the resulting relative head displacement, and the gap 37.

## 6. The physical spare tail and generic Box laws

The root frame includes the entire prior spare tail as runs of exact block
values, followed by exactly the DAG-specified number of new zero blocks.
Nonzero spare blocks remain present. Both the far-left exterior and the
far-right exterior beyond the finite encoded file are blank.

Upstream `Box.v` proves all four register excursions for arbitrary finite
block-value lists of length at least nine. Its `rest` parameters have no
zero-value restriction. `Sim.Inv` likewise quantifies an arbitrary spare list
ext, preserving it or appending a zero. Thus these nonzero spare values meet
the actual generic invariant.

The Box proof transports to the modified table. States 5 and 8 do not occur
in its primitive excursions. The return scan in zero decrement uses
state 3 reading 1, and the Box theorem stops at the state-3 exit before any
state-3/read-0 transition. Hence the sole changed surviving row is outside
the primitive proof. This is checked at the source-proof level, not by
assuming all register-file data is zero.

As an additional independent control, `check_box_transport.py` runs the four
exact excursion contracts with a plain sparse simulator on 270 examples
across all nine target registers, zero and positive values, different left
contexts, and nonzero spare tails. It checks full endpoint tape equality and
verifies that every transition read is identical in the old and new tables.
All 17,128 literal steps pass. The 52 observed transition keys include (3,1)
and exclude (3,0) and both deleted states. The evidence is
`box_transport_check.json`. These finite checks supplement the generic
source proof rather than replace its induction over arbitrary block lengths.

## 7. Uniform continuation and connection to the abstract theorem

The site executor keeps the whole register file opaque and applies only the
four generic Box laws. Outside the file it executes exact individual bit
transitions or same-state scans of affine-length constant runs. Run lengths
remain nonnegative, and the affine parameter ranges over every natural
number. Its expected final state includes the complete PC frame and the
complete ordered list of register-file effects.

The independent replay checks all 8,391 path/branch cases at exact gaps 37,
38, and 39, and again for the affine family 40+n. These four cases cover
every gap at least 37. Positive instruction segments preserve that bound,
with a normal PC overflow increasing the gap. This adapts the old D0=40
simulation to the observed root. The initial-register parameter of the
inductive simulation is the recorded dirty R, while the initial path is
empty; no assumption R=0 is required by the instruction proof or no-stray
argument.

At the recovered root, the abstract controls pl=np=d=0 and the required
scratch registers are zero. TW and WS may be arbitrary. The separately
proved monotone DROP barrier applies exactly to this state: candidate zero
first resets the active formulas; an injective map sends every later NIP to
a strictly earlier DROP; and no NIP reaches the dirty initial WS tail.
Halting therefore yields C254 falsity. The existing arbitrary-state proof
compiler and cofinal candidate enumeration give the converse implication.

Every runtime instruction corresponds to a finite positive binary segment.
Consequently an infinite abstract run gives arbitrarily long nonhalting
binary prefixes, while a finite abstract halt gives a binary halt. The machine
is deterministic, so no separate unobserved binary behavior can intervene.
This closes the new bootstrap/soundness gap at ordinary ZFC proof level.

## 8. Novelty relative to the audited repository snapshot

The thirty-four reconciled reports and five newer unplaced archives at
ProveIt commit `61e77836565f63582561f54745f633d50efd9c7d` already contained
this runtime table and substantial failed canonical-boot searches. Their
sound-start extensions required theorem-valued formula registers and an
entirely theorem-valued WS stream. I found no monotone DROP injection or
arbitrary-dirty-WS safe-start theorem in those materials.

The new result is therefore a new proof of a valid blank start for this
existing 252-state runtime, enabled by a different invariant and exact
acceleration through the earlier short-gap obstruction. The assertion of
novelty is relative to the explicitly audited sources, not a claim to have
searched all unpublished or historical constructions.

## 9. Addendum: the inherited bridge applies to this exact dirty root

I checked the universally quantified upstream program theorems directly at
busy-beaver commit `297ab8df7e5de329605c3875b4934643b371a5e3`. This resolves
the distinction between the new root and the old blank boot with nextproof=2.
No new generalization of the program-to-enumerator theorem is required.

`ZF/m254/coq/tm/Check254.v` defines physical order
`[2;4;3;7;6;8;0;1;5]`, with source registers numbered
`(np,tw,ws,ac,d,h,s1,s2,pl)`. For arbitrary natural numbers W,T, define

\[
 R_{W,T}=(0,T,W,0,0,0,0,0,0),\qquad
 s_{W,T}=\operatorname{mkState}(0,0,T,W,0,0).
\]

Extend R by zero at source indices at least nine. Then `vregs R` is exactly
the recovered physical vector `[W,0,0,0,0,0,0,T,0]`. Moreover,
`approx R (enc s)` holds by direct evaluation: `enc s` is
`mkSt (np s) (tw s) (ws s) 0 (d s) (h s) 0 0 (pl s)`, and `approx`
means equality at every source register index. The nonzero physical spare
blocks belong to the separate `ext` parameter in `Sim.Inv`; they do not
become source registers at indices at least nine.

The exact inherited chain is as follows.

1. `ZF/m254/coq/prog/Bisim254.v`, `p254_dag R`, states
   `rm_halts p254 ([],R) <-> rm_halts dag254 ([],R)` for every R.
   The concrete `Cert254.v` certificate is checked in both directions by
   `cert_fwd` and `cert_bwd`; the proof invokes `Bisim.check_iff`.
   There is no reachability, zero-register, or formula-soundness hypothesis.
2. `ZF/m254/coq/tm/RMEquiv.v`, `rm_halts_iff_iter p`, assumes only
   `wf p` and quantifies every R. `Main254.dag254_wf` supplies the program
   hypothesis for the literal 219-node DAG. Hence the previous right side
   is equivalent to `iter_halts dag254 R`.
3. `ZF/m254/coq/prog/L2Root254.v`, `iter_halts_dag s R`, assumes only
   `approx R (enc s)` and proves
   `iter_halts dag254 R <-> halts_from s`. Its supporting
   `root_step_gen` and `root_step_det` are likewise universal in s and R
   under that encoding condition. They impose no invariant on TW, WS or H.

Consequently the exact original decoder tree, started at empty path with
the recovered register file, halts if and only if the abstract enumerator
started at `(pl,np,tw,ws,d,h)=(0,0,T,W,0,0)` halts. The new monotone DROP
theorem applies to precisely this state. `Main254.prog254` is a later
specialization to R0 and is not the theorem used in this composition.

The matching Lean port at ProveIt commit
`61e77836565f63582561f54745f633d50efd9c7d` independently exposes
`L2.root_step (s : Enum254.St)` and `L2.iter_iff (s : Enum254.St)` with
no formula invariant, and `RMEquiv254.path_halts_iff_iter (R : Regs)`.
Its `Dag254.lean` header identifies the exact upstream `Dag254.v` by
SHA-256 `538ddaddd932058c2b319011126579d77783231f54331772377c05848a0599e3`;
the preserved Coq file has that hash. The concrete original-tree
bisimulation cited above is the existing Coq instance, not an assertion
that the corresponding Lean instance was already completed.

`DirtyRoot254.root_equiv` was also checked. It preserves every structured
root outcome for arbitrary nine-field inputs by replacing the input with
an explicit scratch-clean virtual root. Its theorem has no formula
invariant, but `virtual_enum_iff` does require `Enum254.Inv`. The present
root is already scratch-clean, so using the direct L2 theorem avoids both
that unnecessary virtual-state transformation and the inapplicable Inv
hypothesis on the dirty stack.

The ordinary adaptation still needed at the physical layer is exactly the
one described in Section 7: parameterize `Sim.Inv` by the recovered initial
register file instead of R0, transport the unchanged Box laws, and use the
new uniform checks for every gap at least 37. That adaptation is supplied
by the new construction; it is not claimed to be a pre-existing Coq
endpoint. No additional ordinary program or logical bridge gap remains.

The selected inherited files, including the complete concrete bisimulation
certificate, were preserved with their repository paths, pinned commits,
Git blob SHA-1 and SHA-256 values in `inherited_bridge/source_manifest.json`.
Every preserved file's Git blob hash was independently checked against the
GitHub response. These are source provenance excerpts, not a complete
standalone build of the upstream Coq or Lean projects.
