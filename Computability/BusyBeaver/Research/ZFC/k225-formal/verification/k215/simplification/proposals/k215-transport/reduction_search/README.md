# Completed bounded searches below 215 states

## Outcome and status

**No 214-state candidate was constructed.** This packet supplies a completed,
reproducible finite search with explicitly limited proof templates. It is not
a proof that 215 states are necessary, and failed joins are not semantic
counterexamples to the proposed tables.

The inputs are fourteen literal 215-state tables at ProveIt commit
`b6c7087477e51c017003bd729e712c8969733223`. Their repository paths, local paths,
and SHA-256 digests are in `inputs.json`. The list includes primary K215,
conditional-marker CM215, commands120, composed, reencoded, zero-spare,
zero-spare-z201, zero-spare-transfer, MP-first transfer, both rho6 orders,
zero-spare MP-first, direct transfer ST215, and rebalanced K215R. This is a
selected literal-table inventory; no completeness claim is made for all
tables or all graph-isomorphism classes in the repository.

Two initial domains were considered: all binary initial tapes, and initial
tapes whose radius-seven window is zero. The latter contains the blank tape.
The domains are then closed under all possible incoming exterior bits, so
every result uses a sound overapproximation of reachable tape windows.

| Search family | Literal inputs / initial domains | Evaluated specifications | Survivors |
|---|---:|---:|---:|
| Inherited rows and one common branch | 14 / 2 each | 17,708,928 full-table fold specifications | 0 |
| Independently synthesized branches | primary K215 and CM215 / 2 each | 159,509,360 individual branch specifications | 0 complete two-branch candidates |

The second count measures **branch specifications**, not that many distinct
214-state machines. The first counts evaluations in both domains separately;
the literal candidate set per domain has 8,854,464 specifications, with
possible duplicate machines under different presentations/specifications.

Both families consider all 46,010 ordered pairs of different working states
for each input. The common bounds are radius 7 (15 tape cells) and at most 97
transitions on each side of a proposed common-endpoint diagram.

## Family A: inherited rows and one common branch

For each ordered pair `(keep, drop)`, remove `drop` and map every successor
reference to it onto `keep`. All states other than the keeper retain their
mapped original rows.

For each read symbol, try either mapped old action from the keeper or the
dropped state. Deduplicate identical actions before taking the two-branch
Cartesian product. If exactly one mapped branch agrees, also try every
possible action on the other branch: both writes, both directions, and all
remaining working targets plus the halt. For 215 states, this is 860 possible
actions on the free branch; the two already inherited actions are omitted
from the additional enumeration.

The full-table specification count for either initial domain is:

| Input | Specifications |
|---|---:|
| primary | 632,584 |
| marker | 630,872 |
| commands120 | 632,584 |
| composed | 632,584 |
| reencoded | 641,144 |
| zero_spare | 634,296 |
| z201 | 634,296 |
| zero_transfer | 630,872 |
| mp_first | 629,160 |
| rho6_120 | 636,008 |
| rho6_210 | 636,008 |
| zero_mp_first | 630,872 |
| direct_transfer | 620,600 |
| rebalanced | 632,584 |

`verify.py` independently recomputes these counts from the input tables by
combinatorial enumeration; it does not trust the C++ counters for them.

## Family B: synthesizing both branches

The second family drops the requirement that either branch be inherited.
For every keeper/drop pair, synthesize the read-zero action from all 860
possibilities. Require a common-endpoint diagram for every inherited context
at both old roles reading zero. During this new block, the opposite keeper
branch may not be read before the join. The modified zero branch may be used
more than once. If there are no successful zero actions, skip the one-action
enumeration for that pair.

Otherwise independently synthesize the read-one action with the corresponding
opposite-branch restriction. Any combination of accepted zero and one actions
would then be sent through the joint full-table filter. A syntactically
unchanged mapped row is a valid one-step join and needs no simulation.

There were no pairs with both a successful zero action and a successful one
action. The exact counts are:

| Input | Initial domain | Branch action evaluations | Complete candidates |
|---|---|---:|---:|
| primary | all tapes | 39,883,360 | 0 |
| primary | zero window | 39,883,360 | 0 |
| marker | all tapes | 39,871,320 | 0 |
| marker | zero window | 39,871,320 | 0 |

This family permits a broader choice of keeper rows than Family A, while its
opposite-branch restriction excludes some interacting two-row solutions.
Neither family contains every possible one-state reduction. A program that
must alternate between the two new keeper branches before rejoining can
escape Family B even when its correctness has a short proof.

## What the finite-window filter checks

The abstract state is `(control, window)`, with a 15-bit tape window centered
on the head. Write and move update that window exactly. The newly exposed
boundary bit is allowed to be either zero or one. Saturating this finite
transition system gives an inductive overapproximation of original reachable
configurations. The original program's halt is included as a terminal
control. In the all-tapes domain, every initial window occurs; in the second
domain, the initial window is zero.

For a changed row, compute positive old paths with at most 97 steps while
no read occurs outside the known window. Search the corresponding new path
for a positive common endpoint: mapped old/new state, equal head offset,
and equal entire window. Outside the window, neither run has written, so
equal window data also means equal whole tapes. If the new run halts,
require a halting old prefix inside the same bound. No terminal-tape equality
is required when both runs halt.

The unchanged mapped rows are one-step diagrams. The current filter also
rejects a detected repeated new configuration before a join. A path may
finish just beyond the window after a final in-window read; it may not read
outside before finishing or joining.

An accepted full set of such positive diagrams supports the usual
well-founded finite-run / productive infinite-run simulation argument.
This C++ program remains a discovery implementation: any future real-machine
survivor must be independently rechecked against its literal full table.
This packet contains no real-machine survivor.

On failure, the implementation may have encountered an abstract context
that no actual computation reaches, may need a larger window or a longer
join, or may need a different state/tape relation. Therefore the empty
survivor sets are evidence about these bounded proof templates, not a
214-state impossibility theorem and not a proof of inequivalence for each
rejected machine.

## Independent controls

Two small synthetic inputs exercise the discovery implementation:

* `mergeable.tm` has two duplicate terminal roles. Both families find folds
  merging those roles.
* `incompatible.tm` dispatches according to the first input bit to a forever
  right-moving role or a halting role. Neither family finds a fold of those
  two roles; the two behaviors cannot be uniformly identified on all tapes.

Every surviving table in either positive-control search is freshly checked
by the **unchanged** ProveIt `check_joint_fold.py` included in `reference/`.
There are 10 surviving inherited-family control specifications and 288
independently synthesized-branch control specifications. Of these, 2 and
32, respectively, merge the explicitly designated duplicate roles. Both
incompatible-control searches have zero survivors. These controls validate
nonvacuous search behavior; they do not turn the real negative results into
proof-assistant theorems.

## Reproduction

Requirements: Python 3.10+, a C++17 compiler (`g++` or `c++`), and the standard
libraries. No network, optimizer, SAT solver, or repository checkout is used.
No executable binary is shipped. Existing source files and receipts are read
only. A requested work directory must be new.

Audit every input and stored receipt, compile the search, and freshly execute
and independently verify all controls:

```sh
python3 verify.py --work /tmp/k215-fold-audit
```

Replay primary K215's all-tape Family A search as well:

```sh
python3 verify.py --replay inherited --name primary --domain all \
  --work /tmp/k215-fold-primary
```

Replay all 28 Family A searches:

```sh
python3 verify.py --replay inherited --work /tmp/k215-fold-inherited
```

Replay both families for all recorded inputs/domains:

```sh
python3 verify.py --replay full --work /tmp/k215-fold-full
```

The full replay usually takes a few minutes; runtime depends on the host.
Each newly computed record must match its stored record exactly except for
elapsed time. A default audit verifies stored negative-search receipts and
runs the controls; it does **not** silently claim to rerun the large searches.
The resulting `verification.json` explicitly lists every freshly replayed
large search.

`results/` contains all 32 exact search receipts. `verification.json` records
the packaging audit, independent controls, and one fresh primary replay.
The executable implements a finite search, so its source and pinned inputs
are the reproducible specification of the search boundary.

## Attribution and possible next steps

The numerical calculus, machine candidates, command implementations, source
allocation, and original window-diagram proof method are inherited from the
ProveIt repository and its acknowledged upstream contributors. The fourteen
tables are copied without modification. `reference/check_joint_fold.py` is
copied unchanged from
`candidate-k215/alternatives/rho6/research/machine/folds/check_joint_fold.py`
at the pinned commit. The original licenses and notices are retained in
`licenses/`.

This packet contributes a compact C++ implementation, the independently
synthesized-branch search mode, complete fresh coverage of the stated
fourteen-input/two-domain suite, and reproducible controls and accounting.
It makes no global priority claim for these algorithmic templates.

The best remaining targets suggested by these specific failures involve
more than an isolated merged control with otherwise fixed rows: coordinated
predecessor/keeper rewrites; source reassociation followed by allocation;
or a representation relation that encodes the former control role in a
nearby tape marker and allows the two new branches to interact before
rejoining. Such searches should carry an explicit proof certificate from
their start, so a promising 214-state table can be validated without
rebuilding the ZFC calibration.
