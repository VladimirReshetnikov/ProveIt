# Opt-in integration contract

## What is ready

The package supplies a complete bounded local query under uncapped execution,
positive certificates, and a snapshot/commit bridge. It does not replace an
exact recognizer, identify knottedness on failure, change current defaults, or
provide an integrated global-budget implementation.

The algorithmic distinction is essential: a selected *core region* restricts
which triangles may be tried. All transitions and independence checks still
use the full `D(core) union alpha(D(core))` read/write footprint. The ambient
state is never cut down to an arbitrary tangle on the core.

## Proposed call sequence

1. Start at a stalled, RI/RII-exhausted production diagram. Keep the existing
   exact fallback and its global budget intact. Allocate a separate explicit
   allowance for this experimental local stage.
2. Call `production_adapter.snapshot(state)`. It records live crossing labels,
   maps live original dart IDs to compact immutable episode IDs, and validates
   a classical one-component state.
3. Call `kernel_unlock(snapshot.diagram, depth, ...)` with cooperative deadline
   checks and appropriate trial and region caps. Keep `SearchExhausted` distinct
   from a completed bounded negative result. Neither can produce KNOTTED.
4. On success, call `commit_verified(state, snapshot, witness, path, check=...)`.
   It replays the positive certificate, checks the exact final state, rejects
   stale production input, derives cyclic triangles from verified keys, and
   commits pairings plus original-label path entries transactionally.
5. Feed the returned original-label terminal face to the existing RI/RII stage.
   Record the RIII triangles in the production's fixed-input-dart trace format.
   Then restart the existing policy under the remaining global budget.
6. Recheck the complete trace with the existing production replay routine, not
   only this package's verifier, before accepting an integration change.

`commit_verified` does NOT delete crossings, change `state.alive`, update
`state.remaining`, or charge the production's old per-move trial counters. New
subset trials, candidate scans, region counts, and elapsed time must be
accounted for explicitly rather than silently relabeling them as old trials.

The transaction uses a full live-pairing journal. An exception during mutation
restores that journal and truncates `path` to its original length. Search uses
immutable isolated data and therefore has nothing to roll back in production.

## Required acceptance checks in the actual checkout

Run the complete maintained Python suite. Add end-to-end tests covering original
input dart IDs after deletions, source-reduction restarts, connected-sum factors,
ambiguous triangle faces, injected exceptions, stale snapshots, exhausted local
and global budgets, and the current JSON evidence schema.

Measure paired full-recognition times on the repository's actual hard corpus,
with the same complete backend, same global budget, fresh input construction,
one warmup, randomized arm order, and an identical control. Include failures,
inconclusive runs, and regressions. The supplied pure-state kernel benchmark is
not a substitute. Do not enable the new mode by default on theoretical node
counts alone.

## Public result semantics

- `FOUND_UNLOCK`: at most the supplied number of RIII moves followed by a legal
  RI/RII opportunity. A certificate is available. It is not by itself an unknot
  certificate unless a complete certified reduction reaches the empty diagram.
- `NO_BOUNDED_UNLOCK`: complete local exhaustion with no bounded witness; not a
  knot-type verdict.
- `UNKNOWN`: resource exhaustion; even the bounded subproblem is inconclusive.

For a complete recognition theorem, separately establish actual-run unlocking
budget `g` and residual core size `r`. The article proves the conditional bound
`poly(N,g) 2^O(g) + 2^O(r)`, not a uniform polylogarithmic gap/core theorem.

## What was not done

No online commits, pull requests, or library uploads were made. A full repository
checkout could not be obtained in the working environment. The production
snapshot/commit adapter was tested with compatible mutable objects and pinned
operation semantics, not imported into the full live recognizer. No production
performance gain, regression pass, Lean formalization, or global novelty claim
is asserted.
