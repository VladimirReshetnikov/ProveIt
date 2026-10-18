# Binary reduction investigation

These experiments read the frozen old-label table from ProveIt commit
`43026ff42f0939f09b9e95495248cfadcad38e38`. The table has SHA-256
`939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713`.
Attribution remains Mira-Cult's original machine, Jeff's verification,
Wade's compiler, mira-emmy's public 253-state reduction, and ProveIt's
register permutation. `strict_affine.py` is the attributed, unchanged
closure-kernel source 27; its original SHA-256 is
`da3cc5f3f5f4d5ebde71c9f353c9ddead010d9c8529d8ae97b6e9ccfe1ba21ce`.

## New semantic relation

`multieffect.py` replaces the single-effect oracle restriction by a vector
of nine integer offsets. A plain box denotes the original symbolic register
vector plus those offsets, followed by an existentially quantified finite
valid spare suffix. A marked box retains both the selected index and the
offset vector. The original four register-box contracts implement every
macro invocation; all 55 support rows stay literally fixed.

Increment adds one to the selected offset. A positive decrement subtracts
one and appends a zero spare block. These operations can cancel on primary
registers while changing the spare suffix; the weaker frame relation admits
that exact concrete behavior. The tape to the left of the register file,
including marker, program counter, gap, and head alignment, is still compared
exactly by the original symbolic executor.

The oracle checks a decrement against the **current** register value. In
the universal run, the only initial restrictions are nonnegativity and the
original source instruction's zero/positive guard. A branch is accepted only
when those restrictions and the current offset determine it. An unknown
guard causes a diagnostic rejection. No tested concrete register values are
used to choose a branch. The companion proof sketch is
`proof_audit/compositional_box_simulation.md` (from the archive root).

## Completed computations

| Experiment | Recipes | Candidate case checks | Surviving candidates |
|---|---:|---:|---:|
| Universal affine-offset uniform folds | 55,471 | 127,868 | 0 |
| Source-interval affine-offset uniform folds | 55,471 | 127,788 | 0 |
| Shorter delimiter plus one extra counter-row edit | 14,042 | Recorded first failures | 0 |
| Complete two-incoming target family, original oracle | 2,898,046 assignments | 558,510 | 0 |

The universal baseline passes all 8,391 cases. The interval baseline passes
the 8,385 source guards admitted by its inductive fixed point. That analysis
uses exact singleton values 0 through 31 plus an unbounded tail >=32;
each resulting set is safely widened to its interval hull before checking
the binary instruction. Its source masks exclude the same six cases as
the earlier invariant, and all 8,384 enabled nonhalting transfers close.

The universal run records 9,780 calls that mark a register after an earlier
effect. Thus the richer relation was exercised, even though no uniform fold
passed all cases. Of its first failures, 22,923 are undetermined new guards;
the root investigation separately replays that subset with exhaustive guard
splitting. Fuels and unsupported symbolic rules are limits of the diagnostic.

## Completed two-incoming search

The unchanged upstream lazy driver now covers all 2,898,046 assignments in
its 46-state family. It evaluates 185,033 partial nodes and performs 558,510
completed affine case checks, with no full-recheck survivor and no candidate
blank run. The saved frontier is empty. The observed run took 97.33 seconds;
its 600-second allowance therefore did not truncate the family. This extends
the prior incomplete result by its 989,497 remaining concrete assignments.
The driver independently rechecks the original 8,391 cases and exact whole
82,552-transition bootstrap before searching.

`audit_lazy_partition.py` reconstructs the family from the frozen table and
replays every branch and pruning weight in the full ledger. It verifies
737 branch entries and 184,296 prune entries, per-source totals, all
2,898,046 assignment weights, and the empty frontier. It does not independently
rerun the symbolic Turing-machine traces. The full ledger has 27,365,620 bytes
and SHA-256
`10f2ccf25867473334e4748199d5f3ae1541f3cde0c96bed8e3bca3903d52f28`.

## Delimiter finding

The return chain `(4,6,9,13,19,29,41,58,74)` recognizes nine consecutive zeros,
then state 84 scans right to the marker. The source decoder has maximum
zero-run length seven, attained at 18 of its 6,460 leaf paths. Transient
instruction phases require extra headroom. Deleting 74 by redirecting it to
84 fails source case 57: zero decrement of logical register 1 at path
`111010010010000000`. The subsequent search also changes one action of a
remaining counter state in `{9,13,19,29,41,58,84}` to any of four write/move
choices and any retained target; all 14,042 nontrivial recipes fail.

An actual grammar rewrite reducing the maximum zero-run might permit a
shorter dispatcher, but it must include the transient phases and preserve
source semantics. The existing backend's conservative minimum threshold nine
would also need a justified adjustment.

## Reproduction

The following scripts expect the pinned `upstream/` source subset next to
`binary_experiments/`, as used by this research packet:

```sh
python3 binary_experiments/multieffect.py
python3 binary_experiments/multieffect_fold_search.py
python3 binary_experiments/multieffect_phase_search.py
python3 binary_experiments/delimiter_repair_search.py
python3 upstream/Computability/BusyBeaver/Research/ZFC/permutation252_lazy_context_search.py \
  --repo upstream \
  --output binary_experiments/lazy_context_reproduced_results.json \
  --scratch binary_experiments/lazy_reproduction_tmp \
  --seconds 600
python3 binary_experiments/audit_lazy_partition.py \
  --manifest binary_experiments/lazy_context_complete_results.json \
  --journal binary_experiments/lazy_context_complete_nodes.jsonl \
  --output binary_experiments/lazy_context_partition_audit.json
```

The source-interval script also imports
`compiler_experiments/refined_phase.py`. Results and full per-recipe
journals are named `multieffect_fold_results.*` and
`multieffect_phase_results.*`. The delimiter ledger is
`delimiter_repair_results.json`. The complete two-incoming manifest, ledger,
and independent replay are `lazy_context_complete_results.json`,
`lazy_context_complete_nodes.jsonl`, and `lazy_context_partition_audit.json`.
Its manifest retains the original execution command as provenance and gives
the delivered journal location relative to the archive root. None of these computations produced an
altered machine ready for a new consistency theorem.
