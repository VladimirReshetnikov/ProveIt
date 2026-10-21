# Independent review of MarkerFold and its three instances

Reviewed source: `research/marker_certificate/MarkerFold.v` and
`MarkerInstances.v`, together with the four native `.tm` tables and
`MarkerTables.v`, during the present session. The review does not change
those sources and is distinct from their compiler/kernel audit.

## Verdict

No mathematical blocker was found in the finite checker or the positive
simulation proof. The conclusion is an exact relative halting theorem
from initial control zero, for every integer head position and every
complete Boolean tape. It is not a theorem from every internal control,
and it does not by itself import the full original ZFC endpoint.

## Finite checker

`finite_rows` covers both symbols at every index below the old table's
length. Equal old/new list lengths, plus `row_above`, cover all indices
outside this bound. Holes in the sparse native indexing are explicitly
`None`, rather than omitted from the finite scan.

`incoming_check` establishes the two one-step facts for every old incoming
row: entry to `a` writes 1 and moves right; entry to `b` writes 0 and moves
right. Thus the immediately preceding cell distinguishes the old logical
role. The hypotheses `a<>0` and `b<>0` make the initial invariant vacuous,
so no initial-tape condition is being hidden.

`outer_check` proves literal row agreement modulo the control map at all
other old states. `shape_check` covers both old role rows, both new merged
rows, both selector rows, the required provider read-zero rows, and both
new halt rows. No assumption of source-code validity, register contents,
blank startup, or theoremhood enters this checker.

There is no missing requirement that provider labels be distinct from all
other labels: whatever coincidences a prospective certificate uses must
satisfy all the exact row equations simultaneously, and the local block
proof uses those equations directly. Similarly, terminal old targets are
allowed and are handled by the control map's halt-reflection lemma.

## Tape semantics

`put` returns the old tape function on a no-op write. Its `put_standard`
lemma proves pointwise agreement with the usual tape update. This is a
constructive way to avoid functional extensionality in exact whole-tape
boundary equalities; it does not alter the machine's contents.

The marker blocks preserve every tape cell and move the head one cell
right, in exactly one or three new steps. They read only the current cell
and its predecessor. The incoming-marker invariant is proved for every
old successor state, independently of any finite-support assumption.

## Positive time and reverse implication

The potentially delicate implication is new halting implies old halting.
The proof is sound. If the new machine is halted after `n` steps, simulate
`n` old steps. Positive block lengths provide a new clock `m>=n`, and the
explicit new-halt row equations make the new halt absorbing. Therefore
the new state at clock `m` is still halt. Boundary equality and
`phi q=halt <-> q=halt` imply that the old state after `n` steps is halt.

This argument needs no reverse local simulation, no limiting argument,
and no consistent choice of clocks for all natural numbers. The finite
existential clock supplied for that particular `n` suffices. The upper
bound `m<=3*n` records quantitative cost but the reverse implication uses
only the lower bound and absorption.

## Totalized versus conventional halting

The formal `step` leaves a configuration unchanged when its row is `None`;
`Halts` means reaching the designated halt label, not merely encountering
an undefined row. For the four concrete tables I independently verified:

- exactly 215 working controls and 430 complete binary rows;
- start control 0 is working;
- no outgoing row at halt254;
- every working-row target is working or halt254;
- every working control is graph-reachable;
- the 303-entry Coq list is a sparse ambient indexing representation,
  not a count of working states.

Consequently an arbitrary-tape run from control0 cannot enter a nonhalt
`None` hole. Reaching halt254 is exactly ordinary finite halting, and
making that terminal configuration absorbing changes no prehalt trace.
This explanation should accompany the theorem when it is compared with
the repository's partial-step or finite-support zipper semantics.

## Exact data audit

All 430 rows of every Coq table match the corresponding native `.tm`
file. The old table is byte-identical to the accepted K215 table. M124 and
FM215 are byte-identical to their respective incoming packet tables.
M125 differs from the primary in exactly the four documented rows, and
from FM215 only by `127/1: 1 R 109` becoming `1 R 125`.

The explicit independent receipt is `marker_review_receipt.json`. Provider
125 is already allowed by the inherited M124 construction note, so M125
should be described as a newly supplied instance of that documented
family, not a new general reduction idea or a 214-state construction.

## Remaining endpoint boundary

The checked theorem compares these concrete tables in the new arbitrary-
tape semantics. A compiled bridge to the existing repository's native,
dense, or zipper endpoint is still a separate formal integration task.
Neither an exact file hash nor an informal representation argument is a
compiled bridge theorem.

Ordinary mathematical composition is nevertheless straightforward: on
blank tape these semantics implement exactly the same transition rows
and designated halt as the accepted K215 convention. Its established
ordinary ZFC-provable consistency equivalence therefore transports to
each new instance through the finite positive simulation. The whole
argument is finitary and formalizable in ZFC. This is distinct from
claiming a freshly rebuilt complete Lean/Rocq endpoint or an internal-PA
arithmetization result.
