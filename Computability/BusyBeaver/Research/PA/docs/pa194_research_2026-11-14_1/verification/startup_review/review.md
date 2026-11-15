# Independent review of adaptive bounded bootstrap search

Reviewed source: `research/bootstrap/adaptive_startup.cpp`, SHA-256
`fe106006b08e10fb199679e6ee99c5fdfa7ff1a37cff6de38e90c746e5281cf3`.

## Conclusion and exact scope

No correctness defect was found in the adaptive enumeration, restoration,
exact cycle check or future-edit-aware ray pruning for the supplied valid
inputs. This is a source review plus the positive controls below, not a
proof-assistant certification of the C++ program.

The input pool has 346 replacement actions on 92 distinct transition rows.
The program considers fixed tables obtained by choosing at most K distinct
rows from this pool and one listed action for each chosen row. It starts at
native control 74 on the wholly blank binary tape, head 0. Unmodified rows
retain the Runtime 193 table's actions. The only acceptable output sought is
a whole syntactic source frame at dispatcher 84 for one of source sites 25–44,
with header padding at least 48, arbitrary values of the nine primary
registers and an arbitrary nonempty finite spare list. This frame detector
is deliberately broader than the intended logical seed state. A detected
frame would still need a source-state/initialization proof and verification
that the selected row edits preserve runtime behavior.

Each branch stops at the supplied time bound (200,000 in the reported runs),
a head coordinate with absolute value greater than 20,000, or more than 20,000
one-cells. The frame check precedes these resource checks, so a frame reached
on the boundary step is still accepted. A resource-limited outcome is
unresolved; it is not a divergence certificate. The negative conclusion is
bounded and relative to this pool, frame family and start control.

Increasing K above 2 extends the start 74 slice of the old 58,485-pair screen.
It does not subsume that older experiment's runs from the other 192 starting
controls. The adaptive branch count counts trajectory branches after
factoring out edits to rows that are never executed, not distinct complete
modified transition tables. The `ticks` counter includes steps executed
again during exact cycle replay; report it as simulator step calls, including
those replay checks.

## Why the adaptive choices cover the fixed-table family

A row's choice is postponed until its first execution. At that point the
program recursively explores each listed replacement, then continues with
the original action. It marks that row fixed in every branch. The decision
therefore remains a fixed transition-table decision, not a time-dependent
rewrite. Any preselected table with at most K edited rows follows exactly
one of these branches until termination or a resource bound. An edit of an
unvisited row cannot affect the current trajectory and need not be chosen.

The complete configuration (`q`, head, step count, finite support and tape
hash), the fixed-row bitset and the selected-edit vector are copied into
recursive calls. The transition rows are global, but each frame restores
its changed row after all recursive alternatives, while nested frames do
the same for their own rows. Thus sibling branches see precisely their
parent's table. Passing a configuration before the selected action is
executed is correct: the child's first step uses its newly selected row.

## Why the pruning is sound

The finite-support hash is a lookup accelerator. A repeated hash, control,
head and support cardinality triggers a fresh replay from this recursion
frame's initial configuration. Only equality of the resulting control,
head and complete support set causes cycle rejection. Hash collisions can
add work or miss an optimization; they cannot certify a false cycle.
Within that recursion frame the table used by the replay is the same fixed
table used by the previous trajectory: exploratory child edits have been
restored. By the time a configuration repeats, every row occurring on the
cycle has had its alternatives explored or the edit budget is already used.

The blank-ray test is invoked only when the head is strictly beyond every
one-cell in the direction being considered. It follows zero-reading rows,
requiring every move to have the same direction, and requires a repeated
control before accepting a ray. Newly written symbols remain behind the
head, so all later reads are zero. Crucially, when budget remains, the test
refuses to prune if any future zero-reading row on that path is unfixed and
has a listed replacement. This preserves possible repairs that have not
yet been encountered on the ordinary run.

The frame recognizer checks the entire finite support, not only a local
window or the dispatcher label. It requires the left marker, exact source
path ones, an adequate blank gap, a delimiter, and at least ten consecutive
unary blocks separated by single zeros. Since the finite support contains
all one-cells, the exteriors are blank. Every supplied source path has at
least one 1, so the initial support-size filter `>=13` cannot exclude a
frame in this declared family. The `Seed.any` field is unused; arbitrary
register values are intentionally admitted.

## Fresh positive and cross-check evidence

1. Reconstructed the primary 194 native table using its dense-to-native label
   map. With K=0, the adaptive detector found its known frame after exactly
   58,154 steps, dispatcher 84, head−2, source site 25. A separately written
   Python scalar simulator reproduced all 66 one-cell positions and the
   entire blank exterior.
2. Deliberately damaged two startup rows of that primary table and supplied
   their exact repairs together with halting distractors. K=1 produced no
   frame; K=2 found the unique two-repair branch and the exact 58,154-step
   baseline frame. This exercises nested branch choices and restoration.
3. Replaced a later zero-reading startup row by an outward self-loop ray.
   With K=0 the detector certified the ray. With its single repair available
   and K=1, the future-edit guard prevented premature ray rejection and
   recovered the exact baseline frame. This directly tests the subtle
   future-edit condition.
4. On the actual Runtime 193 pool at K=2, adaptive search completed 1,119
   branches, with 1,027 rays,89 exact cycles,3 resource limits and zero
   frames. Independently compiled the inherited nonadaptive pair enumerator
   and replayed all 58,485 distinct-row pairs from start 74:58,072 rays,413
   resource limits and zero frames. These counts differ because the adaptive
   search shares common prefixes, includes zero/one-edit behaviors, detects
   cycles and omits irrelevant off-trajectory choices.

Files `positive_controls.json`, `positive_scalar_replay.json`, the JSONL hits
and logs retain the concrete evidence. The intentionally damaged tables are
checker tests, not proposed small consistency machines.

## Input preconditions

The supplied native file has two actions per working state, a unique halt
label 254, all state labels below 3000, and no comments before numeric rows.
Every edit selects an existing row and targets a retained state or halt.
These conditions matter because this small C++ experimental parser does not
independently validate arbitrary malformed input, comment syntax or array
bounds. The supplied pool, table and templates meet the preconditions.
