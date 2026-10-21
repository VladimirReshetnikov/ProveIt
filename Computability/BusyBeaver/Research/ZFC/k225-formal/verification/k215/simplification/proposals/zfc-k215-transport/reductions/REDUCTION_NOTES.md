# Reduction search: measured results and a next target

## Result and status

No 214-state machine was constructed by this work. The retained certified
machine remains K215. CM215 is an existing, materially different 215-state
alternative; its new local proof bridge is handled in the separate comparison
packet. These files contain reproducible search evidence, not an additional
correctness endpoint or a state-count lower bound.

The exact inputs are primary K215 source SHA-256
`17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba`,
primary native table
`9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2`,
and CM215 native table
`e5907f08e0752eada0e25bbf33680341e80e5fe94b52b409aea1ed039edda252`.
The first two were fetched at ProveIt commit
`65e00c64b611e16031189f56d0a6030c7775ef01`; the CM table was fetched by the
comparison investigation at `b6c7087477e51c017003bd729e712c8969733223`.
File hashes, rather than the moving default branch, identify the experiment.

## 1. A stronger source abstraction does not reveal another dead branch

The source analysis uses the three abstract natural-number classes
`0`, `1`, and `>=2`. Unlike the earlier componentwise product analysis,
this experiment retains the complete disjunction of nine-register abstract
stores at each primitive ordinal. There are 3^9 = 19,683 possible stores.

Increment maps 0 to 1, 1 to >=2, and >=2 to >=2. On a positive decrement,
1 maps to 0 and >=2 nondeterministically maps to 1 or >=2. The zero guard is
available exactly in class 0. These transitions contain the abstraction of
every concrete natural transition. Induction on concrete source steps thus
puts every concrete configuration in the computed abstract reachable set.

The fixed point from the calibrated seed (4,0,0,0,0,0,0,0,0) contains exactly
5,455,668 pairs of primitive ordinal and abstract store. The only unreachable
ordinals are 4672, 4673, and 4734. The only decrements whose input is always
zero are ordinal 4671 (CD1) and ordinal 4733 (CD6). These are exactly the
facts already found by the repository's earlier product analysis at
`candidate-k215/alternatives/rho6/research/machine/abstract_constants.py`
and its `abstract-cap4/result.json`. No novelty is claimed for those facts.
The new measured result is that this complete disjunctive refinement finds
no additional dead ordinal.

A direct dead-code splice is slightly better than replacing both decrements
by CB1, but still loses DAG sharing:

| Source | Primitive occurrences | Distinct source subtrees |
|---|---:|---:|
| Original K215 | 4,751 | 202 |
| Delete first inert loop | 4,748 | 203 |
| Delete second inert loop | 4,749 | 204 |
| Delete both | 4,746 | 205 |

The first splice replaces the node at path `110100101110` by its right
child, deleting ordinals 4671--4673. The second replaces the node at
`11110011` by its right child, deleting ordinals 4733--4734. The checker
verifies the opcode and register of every retained primitive and all 6,168
retained guarded edges. Targets of removed zero decrements are redirected
to their unchanged successors. All other ordinal edges commute with the
retained-ordinal bijection. The removed decrements preserve their zero
registers, and the other removed leaves are unreachable. This supplies the
ordinary stuttering argument for the pruned source.

The exact pruned source is supplied as research data. No physical binary
allocation or complete blank-machine candidate is claimed for it.
A smaller instruction word can need a larger decoder DAG.

Run:

```sh
node disjunctive_source.cjs sites215.json source_abstraction.json
```

This writes the receipt and `pruned-source.json`. Node uses only built-in
modules.

## 2. Native CM215 search

The native search methods deliberately extend the repository's existing
rho6 research methods to the later CM215 table. In particular, the ideas of
finite-window inductive domains, one-row rewrites, rewrite-closure folds,
independent-entrance deletion, and shifted-head folds are inherited methods;
the new contribution is the reported CM215 instantiation and independent
implementation.

For each control, the search constructs a finite-window invariant of radius
seven: the 15 tape cells centered on the head. It initializes control zero
with every 15-bit word, hence covers every initial tape. A transition writes
the center bit, shifts the window one cell, and admits either possible new
outside bit. Closure is an inductive overapproximation of all concrete runs
from control zero. There are 972,399 control/window pairs in the fixed point.

The bounded local diagram test uses at most 97 transitions on each side.
Every inspected tape cell must remain in the represented window. A join
requires identical whole represented tape and head position, with the
specified control map. Unvisited exterior cells are unchanged. An escape,
cycle, or fuel exhaustion means only that this proof search did not find a
diagram; it is not a semantic counterexample.

The exact final receipt is `cm215_search_final.json`:

- All 371,090 nonidentity single-row actions are tried: 430 rows, each with
  4*216-1 alternatives (two writes, two directions, 215 working targets or
  the halt, excluding the unchanged action). There are 483 passing local
  stuttering rewrites.
- No pair of states has intersecting action alternatives on both symbols
  after the proposed quotient map. Therefore the rewrite-closure fold
  family generates no 214-state table.
- The independent-entrance deletion search tries all 214 noninitial states.
  It changes each external incoming row independently and requires a join at
  a retained old control before executing any other changed entrance.
  First-failure pruning stops a state as soon as one entrance has no option.
  The run tries 186,620 actions and finds no complete deletion.

Three deletions have partial progress. Dropping 31 permits row 13/1 to become
1L81, 1L107, or 1L128, but entrance 20/1 has no bounded diagram. Dropping 40
permits 27/1 -> 0L302, but 54/0 fails. Dropping 52 permits 156/1 -> 1R155, but
165/0 fails. These are local partial options, not candidates.

The supplied toy machine has identical controls 1 and 2. It is a positive
control: the same code finds the known fold 1 <- 2 and a complete deletion
of state 2. This guards against an accidentally empty success condition.

Run, giving the existing CM215 native table:

```sh
node local_rewrite_search.cjs marker215.native.tm cm215_search_final.json 7 97
node local_rewrite_search.cjs positive-control.tm search_positive_control.json 2 8
```

These computations do not run or certify the complete unbounded TM behavior.
A successful local candidate would require independent replay and an explicit
transfer theorem before it was accepted.

## 3. A concrete next design target

The CM215 marker-selected endpoints have rows

```text
154 0 0 R 166       154 1 1 R 12
168 0 0 R 166       168 1 1 R 98
```

Their behavior differs only on the next one bit. The current selector first
consults the predecessor marker and only then decodes that next bit. A
compiler/allocation change can instead try the opposite decision order:
take the common zero successor immediately, and consult the predecessor
marker only on the one branch.

This is a concrete source-and-backend co-design target, not a new table.
It requires a joint rewrite of several rows and an invariant for the
reordered decoder paths. The one-row/quotient searches above do not include
that transformation. If a suitable existing helper realizes the delayed
marker read, deleting the dedicated helper would save a physical state.
The missing work is an actual allocation plus its complete local diagrams
and startup argument. No conclusion that such an allocation exists follows
from the shared zero row.

A proof-producing optimizer should score a proposal by its allocated binary
state count and the size of its transfer certificate. Counting source
primitives alone is misleading, as the measured dead-loop splice shows.

## Files and scope

Keep `local_rewrite_search.cjs`, `cm215_search_final.json`,
`positive-control.tm`, `search_positive_control.json`,
`disjunctive_source.cjs`, `source_abstraction.json`,
`sites215.json`, and `pruned-source.json`. Earlier radius-four and intermediate
receipts are exploratory and need not be included. The native primary table
is a convenience copy of the pinned repository input.

No new proof-assistant verification, unconditional nonhalting claim, state
minimality theorem, or 214-state construction is asserted here.
