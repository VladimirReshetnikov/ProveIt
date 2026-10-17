# Compiler and source-boundary experiments

## Result and scope

No table with fewer than 252 working states was obtained here. The retained
machine and logical calculus were not edited. These experiments enlarge the
invariant and simulation interfaces used to search for a reduction; their
negative results concern the declared finite families only.

All source references are pinned to ProveIt commit
`43026ff42f0939f09b9e95495248cfadcad38e38`. The literal register program
`Prog254.v` has SHA-256
`1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746`.
The old-label 252-state table has SHA-256
`939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713`.
The attributed source program and register engine are due to Mira-Cult,
Jeff Ketchersid, and Andrew James Wade; the table also incorporates
mira-emmy's public253 reduction and ProveIt's physical permutation.

## 1. Explicit small values and residue tails

`refined_phase.py` uses the atoms

```
{0}, ..., {cap-1}, {cap+j+k*period : k>=0}, j=0,...,period-1.
```

Each register is an arbitrary union of these atoms. Joins are unions. INC
and guarded DEC use the best atomwise overapproximations, so counters remain
unbounded. A monotone worklist computes a source-control invariant. A
separate pass through every final edge checks initial inclusion and the
postfix condition; this is a finite certificate check, not a Lean proof.

All **24** combinations of caps `2,3,4,8,16,32` and periods `1,2,4,8`
stabilized with exactly the existing six excluded conditional cases:
`8202,8203,8204,8358,8359,8360`. No additional source guard was excluded.
The complete measurements and the selected invariant are in
`refined_phase_results.json`.

## 2. Full finite relational abstraction

`joint_phase.py` retains an arbitrary subset of all **3^9 = 19,683** tuples
over `{0,1,>=2}` at each of the 6,460 source controls. This retains every
nine-register correlation expressible by that quotient, rather than taking
a Cartesian product of separate register masks. Tail decrement is
nondeterministic: `>=2` can become `1` or remain `>=2`.

Encode an abstract tuple by its base-three integer and store sets as integer
bitsets. Updating register r shifts the appropriate bitsets by `3^r`.
No carry can cross a coordinate because the top coordinate class is handled
separately. Delta propagation computes the exact reachable set in this
finite nondeterministic abstract graph. Every concrete natural-valued source
run projects into that graph, by induction on source steps.

The completed run took 2,074,807 worklist pops, reached **7,725,677** abstract
control/tuple pairs, and had at most 6,561 tuples at one control. Its final
postfix check again excluded exactly the same six cases and retained 8,384
nonhalting transfer edges. The maximum number of tuples at a control is a
measurement of this abstraction, not a bound on concrete register values.

`joint_phase2_results.json` contains all 6,460 final bitsets in hexadecimal,
along with the measurements. Its uncompressed size is about 29.5 MB, but it
compresses well in the requested archive. It supplies no additional dead
branch and no lower bound on the size of a consistency machine.

## 3. Targeted delimiter rebracketing

The current 203-node shared decoder DAG has depth 34 and maximum consecutive
zero run seven. Exactly 18 unfolded leaves contain seven consecutive zeros;
all are decrement sites in the AX emission region. They arise from 16
distinct seven-zero spine roots. A source layout with maximum zero run six
is a possible prerequisite for eliminating one delimiter-counting state,
but the prerequisite alone proves neither the binary runtime nor startup.

All **238** legal single closed rotations or commuting-increment operations
from the attributed source27 rotation generator were inspected. Of these,
179 keep maximum zero run seven and 59 increase it to eight. None reduces
it to six. These are exactly the source27 generator's operations, not all
possible program-preserving transformations.

`delimiter_rebracket.py` additionally runs a deterministic beam of width 12.
Each accepted move must strictly reduce the number of leaves containing a
seven-zero run, have source depth at most 39, and have at most 300 states
in the *graph-reachable* emitted table. The score uses the actual emitted
transition graph, not a fixed compiler-overhead estimate. This graph count
can exceed a later context-sensitive pruning count and is therefore only a
conservative search heuristic. It must not be presented as an optimal
compiled state count or as a lower bound.

The beam evaluated **18,561** distinct layouts in nine rounds. Its best
surviving frontier in round eight had three offending leaves, graph count
300, depth 37, and 207 shared source nodes. The ninth frontier was empty;
no zero-run-six layout was retained and no new binary table was validated.
The requested cap was 12 rounds, but the frontier exhausted earlier. No
random generator is used, so there is no random seed. The code imports the
standard `random` module but never invokes it. The permanent beam record is
`delimiter_rebracket_results/results.json`.

An earlier progress message mistakenly reported 21,361 layouts. The actual
record and sum of per-round evaluations are **18,561**; that is the number
to use in the report.

## 4. Positive source blocks as a larger target boundary

The ordinary strict instruction checker demands the source's immediate
successor frame. `reference_block_folds.py` permits an exact successor after
any finite positive source prefix whose behavior is uniformly determined
by the entry phase masks and current affine register offsets.

For each of 8,385 feasible conditional cases, the construction starts at its
actual source leaf and selected source branch. It then follows the exact
zero-padded program decoder and INC/DEC/CB/CC path arithmetic. It continues
through increments and any decrements decided by the initial unbounded
register bounds plus the accumulated offsets. It stops at an undecided
guard, a source halt, a repeated complete symbolic state, or the requested
64-step limit. Each live target records:

* a positive number of actual source instructions;
* the exact physical PC and accumulated carry/gap change;
* the nine-component affine change to the initial primary vector;
* the complete left/right dispatch-frame shape.

The whole frame is still compared. The spare suffix is existential only
through the separately justified `multieffect.py` register-box relation.
No primary register, PC, marker, header, or gap condition is forgotten.
Unknown guards are rejected, not guessed. A halting alternative is admitted
only when an exact finite source prefix reaches CH. In the nonhalting mode
of the old executor, arrival at terminal254 appears as a missing-row lookup
after the actual final write/move; the wrapper recognizes only that exact
terminal and only when the source halting prefix has been established.

The 64-step source cap did not bind in this run. The live frontier sizes
range from one to thirteen; 8,383 cases stop at an unknown subsequent guard,
and two encounter a source halt (including CH itself). There are six cases
with thirteen possible live targets. Every unchanged binary baseline case
passes: 8,384 at its first source successor and the remaining case at halt.

The complete family of **55,471** uniform state deletions that preserve all
55 register-box support rows was tested. There were **127,788** candidate
case checks and no survivor. No candidate matched a target requiring more
than one source instruction before its first rejection. Final rejection
counts were:

| Checker stop | Recipes |
|---|---:|
| Symbolic fuel exhausted | 33,289 |
| Undetermined sequential register guard | 18,001 |
| Unknown affine run length | 2,877 |
| Unsupported box operation | 1,122 |
| Unexpected terminal lookup | 182 |
| **Total** | **55,471** |

Fuel was 1,000 symbolic rules. The source/reference progress is at least
one, and every accepted binary trace has at least one literal transition.
Those positive clocks are essential to the unbounded simulation theorem:
neither machine may remain forever at a zero-progress correspondence while
the other eventually halts. The accompanying ordinary proof is in
`proof_audit/compositional_box_simulation.md`, under its adaptive-block
extension. No altered table or new bootstrap passed this experiment.

The final data are `reference_block_halt_results/results.json` and
`reference_block_halt_results/journal.jsonl`. The journal SHA-256 is
`1167e5fb920c362b0e7b230936c1e9c496573fa4de206f78fc718a030c1cf1bc`.
The earlier `reference_block_results` run did not yet admit early binary
halting at a later source CH; the final extended run reproduced its entire
journal byte-for-byte. These are **55,471 distinct recipes**, not 110,942.
The earlier duplicate journal can be omitted from the delivery.

## Reproduction

Use Python 3.12 (only the standard library is required), with assertions
enabled. Run from the delivered archive's root, preserving its directory
layout. The outputs may be placed in another writable directory.

```
python compiler_experiments/refined_phase.py --output /tmp/refined-phase.json
python compiler_experiments/joint_phase.py --cap 2 --output /tmp/joint-phase.json
python compiler_experiments/delimiter_rebracket.py --output /tmp/delimiter-layout --width 12 --rounds 12
python compiler_experiments/reference_block_folds.py --output /tmp/reference-blocks --block-limit 64 --seconds 600
```

Wall times vary by host. No network, Lean build, Coq build, external Python
package, or Git mutation is needed. These paths deliberately refer to the
delivered pinned snapshots rather than fetching an unpinned current branch.

## Exact dependency inventory

The two phase scripts import the pinned
`upstream/Computability/BusyBeaver/Research/ZFC/permutation252_phase_analysis.py`;
that module imports the pinned `candidate252_independent_audit.py`.
They read `upstream/lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v`.

The delimiter script also needs the old-label table and these pinned host
files under `upstream/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/`:

* `code/27-variant-experiments-machine_search-grammar_search-dag_tools.py`
* `code/27-variant-experiments-machine_search-grammar_search-rotate_search.py`
* `data/27-variant-experiments-machine_search-grammar_search-decoder_entries.json`

The reference-block script additionally needs the delivered files
`binary_experiments/common.py`, `multieffect.py`, `strict_affine.py`, and
`Prog254.v`. `common.py` uses the same pinned old-label table. Its local
`Prog254.v` copy may differ only in final whitespace; the source-block script
checks the hash of the exact upstream snapshot and compares every one of
its 8,391 source cases to the local decoder-derived cases.

The scripts and local mathematical explanations are new to this session.
The imported generator, phase checker, box checker and program data retain
their upstream provenance and license notices. Formal correctness of the
new Python interpreters/checkers has not been established in Lean or Coq.
