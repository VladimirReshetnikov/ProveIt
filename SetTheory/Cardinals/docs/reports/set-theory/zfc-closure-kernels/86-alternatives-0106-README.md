# Arithmetic-core redesign investigation

No complete machine below 246 states is established here. The new positive
results are prepared-frame unary equality components with 28 states (gap>=2)
or 24 states (gap>=3), an exact
18-state copier quotient, and a universally checked arithmetic closure using a
changed spare invariant and a borrowed decoder row. The borrowed-row closure
has failed whole-machine return/blank-start checks; files named `partial` are
not consistency machines.

All labels refer to the supplied Context246 original-label table, SHA-256
`303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee`.
The local proofs use the supplied explicit literal-step, unary-loop induction,
finite-list induction, and free-word identity checker. They are ordinary
checked mathematical arguments, not new Lean/Rocq kernel theorems.

## A new closure with a final-spare invariant

Delete state 255 and make three changes:

| Row | Transition |
| --- | --- |
| 75 / 0 | 0 R 63 |
| 48 / 0 | 1 L 131 |
| 131 / 0 | 1 L Q |

Here Q can be 33 or 126. Both already have the required row `Q/1 = 0 L 48`.
No new state is introduced: the full partial table has 245 working states.
The former nine-state arithmetic SCC is no longer closed, since `Q/0` is an
existing decoder exit. That fact alone does **not** make it a correct return.

Let `B(v)=0 1^(v+1)`. Require the last spare to be exactly 1. For a marked file
`B(A) 00 1^x B(S) B(1)`, the unbounded contracts are:

* Increment returns in 48 at head -1 with
  `B(A) B(x+1) B(S) B(0) B(1)`. It changes the former final spare from 1 to 0
  and appends a new 1, preserving the final-spare-one invariant.
* Positive decrement has the original contract: selected `x+1` becomes `x`,
  the file origin moves right one cell, and 48 is reached at old head 0.
* Zero decrement has the original contract, with a nonempty following block:
  the file is restored, and 112 is reached at head -1.

All primary values are arbitrary natural numbers; A and S are arbitrary
finite lists. The untouched left context is arbitrary and the right exterior
is blank. If `p=width(A)` and `w=width(file)`, the times remain `2w+7`,
`2p+4`, and `2p+7`, respectively.

The new tail mechanism is specific. The old nine-state core reaches the tail
with `C(S) C(1) 1 0 0`, where `C(v)=1 0 1^v`. The changed rows close it using
`Q/1`, ending with an ordinary file whose final spare pair is `B(0) B(1)`.
The exact literal and induction traces are in the proof JSON files.

Reproduce:

    python research_sub246/arithmetic_core/prove_borrowed_tail.py --borrowed 33
    python research_sub246/arithmetic_core/prove_borrowed_tail.py --borrowed 126
    python research_sub246/arithmetic_core/check_borrowed_tail.py

Outputs are `borrowed_tail_33_inductions.json`,
`borrowed_tail_126_inductions.json`, corresponding `*_partial.tm` files, and
`borrowed_tail_literal_checks.json`. The independent literal tests are finite
regressions, not premises for the unbounded claims.

The program-counter integration fails in the tested unchanged-prefix family.
The compiler lane found two distinct source instruction contexts whose complete
tape/head configurations first coincide when 48/0 and 112/0 execute their now
identical `1 L 131` transitions. A downstream-only edit to 126/0 and 108/0
cannot recover that erased phase bit. See the independently recorded collision
in `../machine_encoding/borrowed_tail_first_collision.json` and
`borrowed_tail_exact_collision.json`. This is a precise obstruction to that
first-correct-return interface, not a lower bound for arbitrary alternate
simulations.

Three earlier marker variants, preserving the file-header one via 57/1 and/or
30/1, were also tested with all repairs in that two-row family. None survived;
source CD at PC000 supplies an earlier failure independent of the CI collision.
The finite search scope is recorded by the compiler lane in
`../machine_encoding/borrowed_marker_search.json`.

`prove_blank_obstructions.py` independently proves the unmodified blank-start
failures of both partial tables. Q=33 reaches state42 with an entirely blank
right ray after 54 steps and then writes right forever. Q=126 has an exact
whole-configuration repeat at steps 1547 and 1697, a 150-step cycle. Complete
finite witnesses and the induction criterion are in `blank_obstructions.json`.
Neither partial table can be presented as a proof-search simulation.

## A second nine-state variant: exact destructive effect

Deleting 255 and setting only `75/0 = 1 R 131` preserves the old counter-return
rows. It has correct increment with an appended spare 0 and correct positive
decrement. Its zero case is not the required operation:

    B(A) 00 B(y+1) B(S)  ->  B(A) B(1) B(y) B(S)

It returns through 112, but transfers one unit from the following register to
the selected zero register. If the following register is zero, it is emptied
into a lone delimiter, breaking the canonical register-file representation.
These are exact unbounded statements, recorded by
`prove_transfer_zero.py` and `transfer_zero_inductions.json`. No data-liveness
or alternate source semantics justifying this destructive effect is claimed.

## A strengthened spare-count proposal that cannot work in this family

The forward244 collision could conceivably be excluded by a stronger
reachable-frame invariant. We tested one precise family:

    spare_count mod 2 = f(program_site) XOR sum(c[r] * register[r] mod 2).

The nine coefficient bits are fixed and `f` is an arbitrary label on each
source instruction site. The forward244 effects append one spare on increment
and zero decrement, but not on positive decrement.

No invariant in this family is closed under every edge admitted by the
supplied interval certificate. The finite graph has 6,456 admitted sites and
8,384 edges. Four independently reconstructible cycle equations suffice:

    c[N] XOR c[X] = 1
    c[N] XOR c[L] = 0
    c[Y] XOR c[L] = 1
    c[X] XOR c[Y] = 1

Their left sides XOR to zero and their right sides to one. The full spanning
forest, edges, cycle equations, and elimination witness are saved in
`spare_parity_audit.json`. Reproduce with `audit_spare_parity.py`.

This result concerns the stated affine-parity family over the guarded CFG
**overapproximation**. It is not a theorem about every actual blank-run
invariant, nonlinear/history-dependent markers, or all smaller machines.

## Bounded synthesis

`synthesize_core9.py` is a bitvector SMT encoding. Its six-case run timed out.
`synthesize_core_sat.py` is a separate direct CNF encoding with the standard
return interface fixed and seek/carry/tail rows allowed to change. A three-case
24-step model was found, then independently refuted by incrementing the local
file `[0,1]`: it crosses the opaque left boundary in state 131 after nine
steps. A six-case run hit its conflict budget and is inconclusive.

The stored JSON results state their exact case, edit, step, and interface
restrictions. `replay_sat_candidate.py` is the independent sparse literal
screen. Neither a finite model nor an exhausted bounded search establishes
an unbounded arithmetic theorem or a state lower bound.

## New direct-tape equality component

`compare_biased_counter.py` builds a 29-state binary component (28 operational
states and one failure sink), with separate EQ and NEQ ports. Its prepared
input is a left counter `1^(a+1)` with zero immediately to its left, a gap of
at least two zeros, a header made of positive unary runs separated by isolated
zeros, and a finite stream of nonempty unary fields. The selected source has
`b+3` ones with its first one erased. The head starts on that erased cell.

It decides a=b, restores the complete source/header/arena, clears the counter
to its sentinel, and returns on that sentinel through the appropriate port.
`compare_biased_counter_PROOF.md` gives the unbounded moving-marker/counter
induction and proves every loop terminates. The two symbol-disjoint state
folds and universal read guards are explicit. `compare_biased_counter_guards.json`
is intended for subsequent global guarded packing. The 5,072 finite whole-tape
regressions in `compare_biased_counter_results.json` supplement that proof.

The inputs, marker creation, counter loading, call/return dispatcher, malformed
input behavior and blank bootstrap must all be charged by a complete machine.
This component alone does not reduce the old 246-state machine.

## Exact 18-state copier quotient

`biased_reference_copy18.py` imports the separate 19-state biased copier in
variable-anchor mode and identifies `after_anchor` with `find_ones`. After the
identification both rows are exactly equal (zero moves right to `find_first`,
one scans right in the merged state). The generator asserts this equality;
no reachability approximation is needed for the quotient itself.

The resulting table has 18 states including its sink, with a separate return
port. The same positive-run shuttle induction permits the fixed seven-cell
four-mode header. The 1,980 tests include all header modes and variable single
anchors. Artifacts are `biased_reference_copy_18.tm` and
`biased_reference_copy18_results.json`. Original 19-state files are unchanged.

### Smaller comparison with a stronger capacity premise

`compare_biased_counter27.py` builds a 27-state alternative when the loaded
counter gap is at least THREE. On counter exhaustion it creates a two-one
dummy counter, restores the source, and reuses the normal done-return path,
which reports NEQ and clears the dummy. This removes three failure-return
states and adds one writer. The universal argument and explicitly charged
capacity premise are in `compare_biased_counter27_PROOF.md`; 5,072 whole-tape
regressions pass. This version is not valid for arbitrary gap2 inputs.

### Latest exact guarded quotients: 28 and 24 states

`fold_comparator_entries.py` removes one redundant initialization role from
both versions, and identifies two additional common source-restoration roles
in the stronger-gap version. The resulting tables have 28 states for gap>=2,
or 24 states for gap>=3, including their sink and excluding EQ/NEQ ports.
`compare_biased_counter_quotients_PROOF.md` gives the exact row agreements and
stepwise simulation argument. The complete guards and structural certificates
are in `compare_biased_counter28_results.json` and
`compare_biased_counter24_results.json`. Additional tests check 5,534,670 literal
step projections, not just final output. The earlier tables remain available
for independent audit and are not silently overwritten.

## Independent review

The comparator29/comparator27 constructions and copier18 passed separate
review in `../verification/comparators_and_copy18_review.md`, including all
31-to-29 fold rows, every copier quotient row, arbitrary positive-run headers,
and 1,512 additional whole-tape cases per comparator. Their guard certificates
were supplied separately to the global packer. The smaller comparator tables
are explicit guarded quotients of those reviewed tables.

Global compatible-row packing may already discover these local folds. Never
subtract a local saving again from a globally packed state count.
