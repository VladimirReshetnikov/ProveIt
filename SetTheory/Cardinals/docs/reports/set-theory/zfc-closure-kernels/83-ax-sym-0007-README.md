# A verified composition of two 246-state controls

This package **does not contain a machine with fewer than 246 working states**.
Its positive result is a new compatibility check: the archived 202-node source
reassociation and the archived alternate return detector can be installed
together. The resulting exact binary table passes the source, runtime, and
blank-initialization checks below.

The state count and 409,449-step initialization are inherited. The alternate
detector by itself already achieved that initialization time. Neither a new
state-count record nor a new initialization-time record is claimed here.

## Exact machine

| Convention | Start | Dispatch | Halt | Working states |
| --- | ---: | ---: | ---: | ---: |
| Canonical labels | 0 | 88 | 246 | 0 through 245 |
| Preserved old labels | 95 | 96 | 254 | 246 distinct labels |

The machine has one two-way infinite binary tape, initially all zero, and the
head starts at coordinate zero. Initialization uses the counted states.
Every transition writes a bit and moves one square left or right, including
the final transition into the separate halt label.

The files are:

- `machine/zfc_composed246.tm`, SHA256
  `27281e721b970201c223663be2ef2d10653c54a27e9266b81a4a106b22bcc8c3`.
- `machine/zfc_composed246_old.tm`, SHA256
  `29377d9d8abc876187cb3fdac430f9dc92999802a848c0c2403874763214951f`.
- `machine/renumbering.json`, the explicit state bijection.

Both tables contain exactly 492 rows. There is one halting row: old state 77,
read one, writes one, moves right, and enters old halt 254. All working states
and halt are reachable in the directed transition graph. Graph reachability
does not establish reachability on the actual blank run or state minimality.

## Reproduce the ordinary certificate

From this package directory:

```sh
python3 -B code/verify_composed246.py
```

No Python package installation, Lean, Rocq, network access, or compiler is
needed. Do not use Python's `-O` option: the assertions are the checks.
The run first verifies the imported-file hashes. It independently rebuilds
the old 246-state baseline from the pinned permutation252 table, installs
the 14 explicit changed rows, checks source equivalence, replays the four
block/list inductions and register/selector contracts, and checks all 8,391
guarded instruction cases. Finally it replays the complete blank prefix with
both sparse and dense tapes, compares every tape cell, and checks the exact
canonical renumbering with a further dense replay.

The fresh fast verification took approximately 2.05 seconds on this session's
host; timing is not a mathematical claim. Its result is in
`results/verification.json`. The complete prefix, including all 351 one-cell
coordinates and the usage count of every executed transition, is in
`results/bootstrap.json`.

For the stronger direct whole-frame replay:

```sh
python3 -B code/verify_whole_frame.py
```

This expands all nine primary registers as independent quantified natural
variables, the extra gap as another variable, and the spare suffix as an
arbitrary first block followed by an arbitrary finite block list. It uses
the four checked block/list induction rules but does not call a predeclared
register-operation oracle. All 8,391 cases and all 492 transition rows are
covered. The original direct run is retained as
`results/rotated_detector_full_symbolic.json`; the portable rerun writes
`results/direct_whole_frame.json`.

The portable direct rerun completed successfully: 8,391 cases, 2,036,033
symbolic rules, all 492 transition rows, and a minimum positive step bound
of 13. It took approximately 243 seconds on this host. The additional
`results/direct_checker_adaptation.json` verifies that the four substantive
functions have exactly the same Python abstract syntax as the prior direct
checker; only imports and its command driver were adapted.

## The 14 changes

All rows in this table use preserved old labels. Each triple is
`(write, direction, next state)`. Every other row equals the frozen prefix246
baseline with SHA256
`303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee`.

| Contribution | State/read | Before | After |
| --- | --- | --- | --- |
| Source reassociation | 178/0 | `(0,R,23)` | `(0,R,16)` |
| Source reassociation | 178/1 | `(1,R,208)` | `(1,R,206)` |
| Source reassociation | 208/0 | `(0,R,24)` | `(0,R,23)` |
| Source reassociation | 208/1 | `(1,R,206)` | `(1,R,70)` |
| Source reassociation | 218/0 | `(0,L,154)` | `(0,R,105)` |
| Source reassociation | 237/0 | `(0,R,218)` | `(0,R,208)` |
| Alternate detector | 13/1 | `(1,L,4)` | `(1,R,19)` |
| Alternate detector | 19/0 | `(0,L,29)` | `(0,L,58)` |
| Alternate detector | 19/1 | `(1,L,4)` | `(1,R,19)` |
| Alternate detector | 29/1 | `(1,L,4)` | `(1,R,29)` |
| Alternate detector | 41/0 | `(0,L,58)` | `(0,L,74)` |
| Alternate detector | 58/0 | `(0,L,74)` | `(0,L,29)` |
| Alternate detector | 58/1 | `(1,L,4)` | `(1,R,6)` |
| Alternate detector | 74/0 | `(0,L,84)` | `(0,R,84)` |

Disjoint changed-row sets alone do not establish correctness of their
composition. One change could alter the contexts in which the other is used.
The complete instruction replay is the compatibility check that closes this
particular issue.

## Source and runtime proof

The source fixture `sources/rotated202.json` has 202 DAG nodes and 6,460 leaves.
The checker proves, by complete finite graph comparison, that its guarded
leaf control-flow graph equals that of `sources/original203.json`. Their
ordered source normal forms also agree. It independently checks that the
original 203-node DAG expands to the literal `Prog254.v` program. The source
reassociation and these comparisons were already supplied by the prior
archive; this package replays them on the composed control.

The instruction language partitions into 2,601 increment cases, 1,931 zero
decrement cases, 1,931 positive decrement cases, 128 break cases, 1,799
continue cases, and one halt case. These are all 8,391 guarded cases, not
random samples. The physical register order is still
`(N,T,W,A,D,H,X,Y,L) -> (6,2,0,4,3,7,8,5,1)`.

All 42 literal transition rows supporting the imported register induction
proofs are unchanged. The four block/list induction rules, the three complete
register-operation contracts, and the nine marking-selector contracts replay
on the exact composed table. Combined with the guarded instruction replay,
these cover every one of its 492 literal rows. The direct whole-frame replay
offers an additional check of the composition without the register-operation
oracle; its literal step and case routines are unchanged from the attributed
prior `full_symbolic.py`.

For every accepted source instruction and corresponding well-formed tape
frame, the machine performs a finite positive number of literal steps and
reaches the prescribed successor frame, or the unique halt transition for
the halt instruction. Values, extra gap, and nonempty valid spare suffix are
unbounded parameters. The minimum recorded positive literal-step bound is
13. Consequently a source execution lifts by induction to a machine execution;
strictly positive durations ensure that infinitely many source instructions
cover unbounded machine time. The converse halting comparison follows by
decomposing execution into these certified instruction intervals. The source
equivalence therefore transports the inherited proof-search calibration.

This is an ordinary mathematical certificate argument. It does not constitute
a new end-to-end Lean theorem about this exact table, nor an arithmetized PA
proof. Those proof-status distinctions remain unchanged from the supplied
246-state material. The ordinary consistency comparison uses the prior
safe-root and original proof-search theorems; it is not a deduction of
unconditional nonhalting or of `Con(ZFC)` itself.

## Complete blank prefix

At exactly 409,449 transitions the machine is in old dispatch 96 (canonical
88) with head at -5. Its marker is at -6 and header is at 176, so the
header distance is 181, with extra gap parameter 141 above the minimum 40.
The source program counter is empty. The logical registers are
`(3,0,0,0,3,0,0,0,0)`; the physical register values are
`(0,0,0,3,0,0,3,0,0)`. There are 167 spare blocks, each of value one.
Exactly 351 cells are one and every other cell is zero.

This is exactly the known safe root of the existing alternate detector.
The truth/truth/empty-stack seed condition is inherited from the prior
proof-search calibration; the candidate counter starts at three and the
parameter register at three. The new source reassociation changes no cell
of this initialization endpoint. Independent sparse and dense interpreters
agree on the full tape, and the canonical dense interpreter agrees under
the explicit renumbering.

## Further fold search

The fresh conditional search considered 13,222 uniform or mixed-row state
merges that touch at least one changed state. It preserves the 42 macro
support rows and dispatch, records the baseline traces, and first replays
the cases affected by a changed row. Any survivor would have been rechecked
on all 8,391 cases. The run performed 407,920 affine case checks and found
no survivor. `results/composed_merge_results.json` records the complete
recipe list and the first rejected case for each recipe.

Reproduce the same finite family with:

```sh
python3 -B code/search_composed_merges.py
```

The portable rerun writes `results/composed_merge_rerun.json`. It completed
the identical 13,222 recipes and 407,920 case checks with no survivor.

This is a negative result for that explicit diagnostic family. A fuel or
unsupported-rule rejection does not prove machine inequivalence, impossibility
of deletion, or a 246-state lower bound. Larger simultaneous rewrites, source
changes, alternate register relations, and other transition models remain
outside the family.

The separate stochastic detector experiments and timed-out solver attempt
produced no valid seven-state replacement. Their rejected tables are not
included as consistency candidates in this package.

## Attribution and proof boundary

Mira-Cult designed the original compact calculus and 254-state machine;
Jeff Ketchersid supplied the verification and symbolic framework; Andrew
James Wade supplied the compiler framework; mira-emmy supplied the public
253-state reduction. The ProveIt permutation252, prefix250/prefix246, source
reassociation, and alternate-detector investigations retain their separate
credit. The contribution here is the exact composition and its fresh audits.
See `NOTICE.md`, the retained prior notice, and `sources/import_manifest.json`.
