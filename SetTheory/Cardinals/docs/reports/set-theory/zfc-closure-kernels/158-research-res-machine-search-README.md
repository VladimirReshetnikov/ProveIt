# Fully synthesized two-action folds of K218

**These searches have not produced a verified 217-state machine.** They
provide new, reproducible bounded proof-search results. Their negative
outcomes are not lower bounds on machine size, semantic counterexamples to
every enumerated table, or evidence that a 217-state construction is
impossible.

The main change from the repository's earlier continuation searches is to
allow **both actions of the merged state to vary independently**, over every
write bit, movement direction and surviving target. A demand-driven C++
implementation makes this feasible for every state pair. The same extension
is applied to the shifted-head relation. Two further experiments specialize
the context domain to a blank initial window and to observed primitive
interfaces.

## Frozen input and conventions

The upstream snapshot is ProveIt's commit
`704b87442afbd571833a628cd558f1d207fd8b2f`. The primary input is the native
K218 table from `Computability/BusyBeaver/Research/ZFC/candidate-k218/`:

```
SHA-256  2dfaba6da09b78291e534777cd30c5f0d68bd84faa670e868e779c396aeb308f
start    0
halt     254, with no outgoing rows
states   218 working states
symbols  0 and 1; blank 0
tape     one two-way-infinite tape; L/R moves
```

The native numeric labels are sparse. The input table, upstream attribution
and upstream license are included. No network access or full repository
checkout is needed to reproduce this packet. The accepted K218 consistency
calibration remains an upstream premise; this packet does not reprove it.

## Completed primary families

Every pair has 217 surviving working states. An action has two writes, two
directions and 218 possible targets, including halt: `872` possibilities.
Thus each pair or eligible pair-shift has `872² = 760,384` complete
two-action assignments.

| Context domain and relation | Pair specifications | Complete assignments represented | Result |
| --- | ---: | ---: | --- |
| All initial tapes, equal heads | 23,653 | 17,985,362,752 | No survivor |
| All initial tapes, shift ±2 | 41,167 | 31,302,728,128 | No survivor |
| Blank initial window, equal heads, affected pairs | 1,917 | 1,457,656,128 | No survivor |
| Blank initial window, shift ±2, affected pairs | 3,370 | 2,562,494,080 | No survivor |

These are counts of **assignment specifications**, not necessarily distinct
machines up to relabelling. Counts from overlapping families should not be
added and described as a number of different Turing machines. The stored
primary runs took approximately 106.5, 201.9, 11.2 and 17.5 seconds in this
workspace, excluding compilation and initial domain construction. Timing is
not part of the mathematical claim.

The fully synthesized equal-head family also completed on each of the three
other accepted 218-state layouts. Each run covered the same 23,653 pairs and
17,985,362,752 assignments, with no survivor:

| Alternate input | Recorded seconds |
| --- | ---: |
| Primary layout with the row157 rewrite | 81.5 |
| Contextual layout | 89.6 |
| Contextual layout with the row157 rewrite | 80.9 |

The literal alternate tables, hashes in the replay driver, and separate
receipts are included. These are additional layout searches, not deductions
from the primary table's negative result.

The raw receipts and progress logs are in `evidence/`. The shifted receipt's
`delta` field is the loop variable at the end of enumeration; both signs
are included in the family. It is not a claim that only that sign was tested.

## Exact finite families

### Equal-head folds

For each unordered pair `{keep,drop}`, the smaller numeric label is kept.
Every incoming destination `drop` is replaced by `keep`; the two rows of
`drop` are deleted. All other states retain their original rows after that
target replacement. The keeper's two rows are synthesized independently
over all 872 actions.

Only one orientation of a pair is needed here. When both keeper rows are
arbitrary, reversing the keeper and dropped labels produces an isomorphic
candidate family, including the corresponding declared initial state.
There are `218 choose 2 = 23,653` pairs. Initial state 0 is included.

The configuration relation maps the dropped state to the keeper and
preserves the head and entire tape. The source invariant is recomputed from
all binary initial tapes with initial state 0. At every represented original
configuration, the filter seeks strictly positive old and new blocks that
end in related configurations with identical complete tapes, or both halt.

### Shifted-head folds

Every ordered `keep != drop` is considered, with `drop != 0`, for each
`delta` in `{-2,+2}`. At the dropped state, the candidate head is displaced
by `delta`; at all other states it is unchanged. The tape is identical.

Every old incoming row from outside `{keep,drop}` must admit the direction
`old_direction + delta` as an L/R move. Such a row changes its target to
the keeper and flips its direction; its write bit remains unchanged. Pairs
failing that requirement are outside the family. All remaining nonkeeper
rows are prescribed copies. Both keeper actions are freely synthesized.
There are exactly 41,167 eligible ordered pair-shifts for the pinned table.

The original state 0 is not dropped in this family, so the initial head and
tape are literally the same. The independent Python accounting script
re-enumerates eligibility from the literal transition table.

## What the context and fuel bounds mean

The proof-search radius is 7: each context contains the current bit and
seven bits on either side. The all-tape domain has **1,009,191** working-state
contexts. It is a finite inductive overapproximation: a window shift admits
either value for the newly exposed exterior cell. It therefore does not
assume a finite tape or restrict unknown exterior bits.

For each original state and context, original paths are cached without a
candidate state map. The map is applied when testing a particular candidate.
Old and new paths may each take up to 97 transitions. A block must join
before reading an unrepresented exterior cell. It may end immediately
after moving out of the window, provided the two configurations already
join there. Complete-window equality then establishes complete-tape
equality because the unknown exterior was not changed.

A successful collection of these positive, uniformly bounded diagrams
would establish unbounded halting equivalence by composing blocks. A failed
join says only that this particular bounded criterion failed. It does not
prove inequivalence. Wider windows, longer joins, other configuration
relations, additional changed rows, source transformations and altered
calculi are outside these negative results.

## Demand-driven synthesis

A partial candidate initially has neither keeper action assigned. The
filter simulates an obligation until it joins, fails within its bounded
criterion, or encounters an unassigned keeper row. In the last case it
branches over that row's 872 possible actions. A failure before reading any
remaining unassigned row is independent of those missing actions, so every
completion of that partial assignment can be rejected together.

This is why billions of complete assignments can be represented by fewer
partial checks. The four primary runs used respectively 309,317,693;
695,572,783; 23,334,893; and 60,455,642 partial checks. The receipt records
rejection counts at assigned depths 0, 1 and 2. Their weighted sum must equal
the complete-assignment count. A separate Python audit also checks the
complete branching-tree arithmetic and independently enumerates the pair
families.

The filter first tests the first and last available context of all four old
rows, then the remaining contexts. This changes only the order of the same
obligations and makes early rejection substantially cheaper. It does not
sample away the other invariant contexts.

## Blank-window specialization

The blank-window domain starts with the single all-zero radius-7 window at
state 0, then applies the same conservative transfer operation, still
admitting arbitrary newly exposed bits. The resulting invariant covers the
actual blank run and, more strongly, every initial tape that is zero on the
initial 15-cell window. Its exact count is **996,949** contexts.

Only the following nine states have fewer contexts than in the all-tape
domain:

```
0, 4, 40, 54, 66, 94, 97, 113, 198
```

Pairs not touching those states have identical nontrivial obligations and
were already rejected by the all-tape search. The additional runs therefore
test only pairs touching this exact independently recomputed set. Both
specialized families completed without a survivor. The hardcoded list in
the two C++ specializations is checked against a freshly computed Python
domain by `audit_results.py`; it is not an assumed reachability fact.

## Finite-interface discovery domain

A further experiment records radius-7 windows on every transition of the
accepted machine through **12,334 finite primitive interfaces**, comprising
two finite register/spare/gap assignments at all source occurrences and
decrement guards, plus its exact blank initialization. The startup reaches
the accepted root frame after **312,909** transitions. Across all interfaces
and startup there are **6,434,657** recorded transitions and **87,157**
distinct state/window contexts. Every working state and both of its rows
occur in these observations.

This domain is a **finite observation set**, not an inductive invariant or
an unbounded runtime proof. Its purpose is candidate discovery: it retains
source-frame restrictions that an arbitrary-tape abstraction loses. Every
survivor would still need complete finite-interface screening, the pinned
unbounded symbolic primitive checker and exact startup verification before
any new consistency claim.

The equal-head family completed all 23,653 pairs and 17,985,362,752
assignments without a survivor. The shifted-head family also completed all
41,167 pair-shifts and 31,302,728,128 assignments without a survivor. Their
recorded runtimes were 81.2 and 184.3 seconds. The compressed exact interface inputs,
their manifest and metadata, the source-site file, the context collector and
the two search programs are included. The replay driver regenerates the
observation set rather than treating it as an invariant certificate.

### Longer observed contexts: radius 15

The same finite executions were also collected with fifteen cells on each
side of the head. This gives **522,379** distinct state/window contexts. The
separate wide search programs use disjoint 64-bit fields for the 31-bit
window, head and state; they do not reuse the narrower program's bit packing.
The 97-transition join bound is unchanged.

| Radius-15 family | Status | Pair specifications | Rejected complete assignments | Seconds |
| --- | --- | ---: | ---: | ---: |
| Equal heads | Complete, no survivor | 23,653 | 17,985,362,752 | 195.005 |
| Shift ±2 | Time limit, no survivor found | 30,200 started | 22,962,865,366 | 300.004 |

The shifted family has 41,167 eligible pair-shifts in total. Its first
30,199 pair-shifts completed; the final started pair was only partly
enumerated. Thus **10,968 pair-shifts remain partly or wholly unsearched**
in this wider family. Its raw `TIME_LIMIT` receipt is retained and the
accounting audit checks the prefix count without labelling the family
complete. All of these wider contexts remain finite observations, so their
role is still discovery rather than an inductive runtime certificate.

## Implementation checks and limits of review

The equal-head independent checker is a byte-exact copy of the repository's
`check_joint_fold.py`, SHA-256
`82d0b364dfdbc7433a58c3c3e7166ec6a32ac9268e0e516f5f113f1287f44031`.
The shifted checker is copied from `k219-shifted-fold/code/check_shifted.py`
with only the import path changed to the included checker. Its imported
checker byte pin is retained.

The C++ synthesis is tested on two six-state synthetic controls. A separate
Python driver exhaustively checks **every one of 576 complete two-action
assignments** for each control using the repository diagram checkers. The
entire survivor sets agree: six equal-head assignments and one shifted-head
assignment. Known positive diagram receipts and an early-halt negative
control are included. The control-specific C++ variants change only
survivor collection and accounting so that all control successes are saved.

`audit_results.py` independently recomputes both invariant domains, verifies
the narrowed-state set, enumerates the four primary families and checks all
stored counting identities. This is an independent implementation of those
checks, authored within the same research session. It is not a second
execution of every rejected candidate, a separate human review, or a
proof-assistant certificate. No claim of machine minimality follows.
Individual rejection trajectories are not retained in this packet; rerunning
the supplied search is the way to replay those decisions. The stored
accounting audit alone does not do that replay.

## Reproduction

Requirements are Python 3 and a C++20 compiler such as `g++`. Run from this
packet's directory and choose new output directories. The defaults allow
600 seconds per search; increase `--seconds` on a slower machine. A
`TIME_LIMIT` result is an incomplete run.

First replay the small controls and inspect the independent accounting:

```sh
python3 -B code/reproduce_controls.py --output /tmp/k218-fold-controls
python3 -B code/audit_results.py
```

Run any primary family individually:

```sh
python3 -B code/reproduce.py --family equal --output /tmp/k218-equal
python3 -B code/reproduce.py --family shifted --output /tmp/k218-shifted
python3 -B code/reproduce.py --family blank_equal --output /tmp/k218-blank-equal
python3 -B code/reproduce.py --family blank_shifted --output /tmp/k218-blank-shifted
python3 -B code/reproduce.py --family observed_equal --output /tmp/k218-observed-equal
python3 -B code/reproduce.py --family observed_shifted --output /tmp/k218-observed-shifted
python3 -B code/reproduce.py --family observed_equal_wide --output /tmp/k218-observed-equal-wide
python3 -B code/reproduce.py --family observed_shifted_wide --output /tmp/k218-observed-shifted-wide
```

`--family all` runs the eight primary-table families. The replay driver checks
the literal input hashes and never treats a filter hit as a proof. The
standalone C++ programs use a compact encoding specialized to the stated
radius; the driver passes radius 7 to the original programs and radius 15 to
the separate wide programs. Changing either value requires reviewing the
configuration encoding and its validation. The wide shifted replay defaults
to a larger time budget than the recorded 300-second experiment, and may
therefore complete more of that family on the replaying machine.

Alternate accepted tables are included for equal-head replay:

```sh
python3 -B code/reproduce.py --family equal --seed row157 --output /tmp/k218-row157-equal
python3 -B code/reproduce.py --family equal --seed contextual --output /tmp/k218-contextual-equal
python3 -B code/reproduce.py --family equal --seed contextual_row157 --output /tmp/k218-contextual-row157-equal
```

## Provenance

The four native input machines, source sites, mathematical calibration and
the two diagram checkers come from the frozen ProveIt snapshot. The new
contribution here is the compiled all-pairs two-action synthesis, its
blank-window and observed-interface specializations, replay tooling and
recorded executions. The demand-driven pruning idea already appeared in
the repository's selected-pair K219 experiments; this packet extends its
scope and implementation, rather than claiming the pruning argument as new.

The finite-frame data and helper implementation were shared by the parallel
relay/bootstrap investigation in this research session. They are retained
as finite discovery inputs. The context collector's portable header is the
unchanged helper prefix of that implementation, excluding its unrelated
search entrypoint. `manifest.json` binds the delivered files and explains
the small portability edits. The upstream attribution and license are in
`inputs/`.
