# Conservative successor preparation

The v2 and v3 frozen source snapshots differed in exactly one module,
`DiophantineConsistency.PRAWitnessCalculus`. Their declared project import
graphs and order were identical. The [declared-graph survey](../../reviews/fresh-project-successor-plan/v2-v3-declared-plan.json)
finds 86 reverse-reachable modules, including the target, and 1,124 other
modules. It is only a planning result: it does not authenticate compiler
dependencies or establish a proof replay.

`prepare.py` can prepare a selective successor **only after** a completed
matched parent pair and a separately observed successful coordinator exit. It
requires caller-supplied SHA-256 pins for both frozen manifests, the parent
pair state, and the coordinator observation. It re-runs the pinned parent
comparator, checks both process logs and both actual recorded builder exits,
and requires each parent's recorded direct imports to agree with its declared
project graph. It then computes the complete reverse dependency closure of
changed source bytes, import lists and workspace paths, and recursively verifies
the full project ancestry of each proposed unchanged seed.

Each sibling's unaffected artifacts and companions are copied from its own
parent into its own new tree: no links and no cross-sibling object borrowing.
Sibling inventories must match; all copied files are rehashed and no affected
artifact is copied. Parent state and source snapshots are checked before and
after, as are the new snapshot against current workspace bytes and Git-tracked
HEAD. Space for both copies plus a 4 GiB reserve is required. Failure can leave
a partial output directory with no `PREPARED_NOT_REBUILT` receipt; preserve it
as failed evidence and use a new directory for a new attempt.

The result is **only prepared seed trees**, not a rebuilt or checked theorem.
A separate successor builder must compile all affected modules in dependency
order, independently verify `lean --deps` against source imports and freshly
built or authenticated seed outputs, guard source and package inputs, and
recheck current workspace sources at the end. It must be run for each sibling
and compared independently. A further source or configuration drift requires
a newly frozen snapshot and a recomputed plan. Existing package-transitive,
dynamic-loading, and possible transient-mutation limits remain inherited.

Run `PYTHONDONTWRITEBYTECODE=1 python3 test_prepare.py` for toy graph, hidden
direct-import, parent terminal-observation, companion and sibling-isolation
checks. `test_real_prepare.py` also constructs and compares a real-Lean toy
parent pair, prepares sibling seeds, confirms affected modules are excluded,
and rejects an unobserved parent exit. These tests do not exercise the
unfinished 1,210-module parent pair or an actual selective successor build.
