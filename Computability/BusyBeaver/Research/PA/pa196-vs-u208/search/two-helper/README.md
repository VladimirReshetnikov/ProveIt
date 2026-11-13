# Two arbitrary changed rows in a PA196 state fold

This search finds no 195-working-state machine within the following local
simulation template. It is not a general state-count lower bound and supplies
no new PA-consistency equivalence. It strictly extends the previous
[two retained-state rows](../two-row/README.md) and [single arbitrary helper
row](../helper-row/README.md) screens: after deleting one state and redirecting
all incoming references to a retained state, it allows **two distinct rows at
arbitrary retained states** to be replaced. The replacement destinations may
be any retained working state or halt. Other rows retain the original
transitions, except for the target redirection.

The screen considers all 38,220 ordered deleted/retained-state pairs, including
deleting the blank-start state. There are 390 remaining rows, 784 possible
replacement triples per row (two write bits, two directions, and 196 possible
destinations), and therefore 1,781,997,214,233,600 raw two-row assignments
including harmless no-op replacements. The screen also tests zero and one
replacement row. We count working states separately from the distinguished
halt control.

For each parent configuration at the deleted state, keeper, or either modified
helper, and for each admitted five-cell window, the child must match the
parent's **one** transition by a positive block of at most 16 transitions,
reading only those five cells, with the same resulting projected state, head,
and entire five-cell tape. All other parent rows commute in one transition.
The admissible windows are the projection of the inductive radius-six
blank-start closure in the previous search: 270,067 abstract windows project
to 2,774 five-cell state/windows, and the abstraction can reach halt. The
closure is an overapproximation and is not a claim that each window occurs in
the concrete run.

## Necessary-condition pruning

The checks are deterministic. In an unpatched child simulation of any parent
step that fails the template, at least one row modified by a successful
candidate must be visited before that failed run terminates or exits the
window; otherwise the candidate follows the same failed trace. The search
chooses a shortest visited-row set among failed contexts at the deleted and
retained parent states, and enumerates each of its rows as the first patch.
This covers at least one of the two changed rows for every possible repair;
the choice of which patch is first is otherwise immaterial. If the unpatched
child already passes, the search reports that plain witness and does not need
to enumerate additional modifications.

For every first-row triple, the search simulates all contexts at the two
merged states and at the first helper. For each failure, a second patch must
change a row visited on that particular first-patched trace. Intersecting the
visited sets of **all** such failures is therefore a necessary condition for
the second row, even when it is at another helper state. The search excludes
the already-patched row and the deleted state's nonexistent rows, then tries
every retained-or-halt destination and every bit/direction pair at each
remaining row. Finally, it checks all admissible contexts at the deleted
state, keeper, and **both** helpers. No context for a different parent state
needs a multi-step check, because its original transition has not changed
except for target projection. If a first patch alone succeeds, it is reported
as an existence witness and further second patches for that first row need not
be enumerated. Thus the algorithm is an existence screen, not an enumeration
of all possible redundant representations of a successful fold.

For PA196 the unpatched screen has no survivor. The first failure set yields
103,550 first-row locations over all pairs, and the search tries 81,183,200
first-row triples. The failure intersections retain 528,136 second-row
locations, on which it tries 414,058,624 second-row triples. None passes. The
counts and the literal input SHA-256
`e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8` are
recorded in [receipt.json](receipt.json).

## Independent control and reproduction

A four-state synthetic control has a genuine two-helper solution: deleting
state 2 and retaining state 0 requires changing both `(0,0)` and `(1,1)`.
The optimized search finds the unique passing pair. A separate unpruned Python
implementation brute-forces zero, one, and all pairs of modified rows and
checks **every** five-cell window at **every** original state; it confirms no
zero- or one-row solution and exactly that two-row solution. This control
exercises the need to preserve first and second patches at different states,
including states other than the deleted/retained pair. It is a finite
cross-check, not formal verification of the entire search.

From the repository root with Python 3.10+ and a C++17 compiler:

```sh
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/search/two-helper/replay.py --output /tmp/pa196-two-helper.json
```

The command builds its executable in a temporary directory, recomputes the
radius-six closure, runs the unpruned control, runs the complete search, and
writes the deterministic receipt. The full C++ screen took about 70 seconds
of CPU time on the research host; elapsed time varies with load. Neither this
finite computational screen nor its control is a Lean or PA proof.

The restrictions matter: the search does not exclude a fold using blocks
longer than 16, blocks that leave the window, a different representation of
states or tape, multiple parent steps per matching block, more than two changed
rows, or a more precise invariant that excludes some abstract windows.
