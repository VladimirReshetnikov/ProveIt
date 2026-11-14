# Joint cyclic state-merger search

This is a bounded negative search artifact. It does not prove a state lower bound and does not establish a new consistency machine.

## Question tested

For each of 41 supplied 194-state tables, can two noninitial working controls be identified, with both rows of the surviving control replaced, so that every former one-step transition is simulated in at most 120 transitions of the final modified table, within an eleven-cell window?

The input selection contains 38 filed constructions labelled supported or supplementary by the current comparison, plus incoming QH, F_AD, and R_AD. These labels attribute supplied evidence; this search does not independently prove their PA consistency calibration. `inputs.json` identifies the frozen inputs. Native tables use start 74; a contiguous dense table uses start 0. Each has one distinct terminal label.

## Difference from the earlier local search

The inherited common-action search follows the original table after a proposed first action and rejects a continuation that revisits either changed endpoint. Here the final quotient table is executed, and the surviving merged state can be revisited any number of times within the stated bound. Its two rows are synthesized jointly. In particular, a detour may change the current symbol and then return to the merged state to use its other row.

This comparison is with that specific inherited search implementation; no claim of first priority for cyclic detours is made.

The method still compares against exactly one original transition at a time. It permits no added helpers, no simultaneous identification of three controls, no larger changed set, no head-displacement relation at matched boundaries, and no source change. These are substantial restrictions.

## Exact finite model

For radius K=5, a window is a bit string on offsets -5 through +5. Start with every such window at the designated original start control. Close the finite abstract transition relation under the original table: after writing and moving, the newly entering boundary bit may be either zero or one. Every actual blank-tape window is therefore included by induction. This all-tape overapproximation does not rely on interpreting the arithmetic source or on a finite sample run.

For each unordered pair a,b other than the start, choose a as the removed state and b as keeper. Redirect every target a to b. Replace both rows of b. The working-target pass enumerates every replacement write bit, direction, and surviving original working target. The terminal-target pass adds every possibility with at least one transition to the original halt label. Unused row actions need not be enumerated specially: any working-target choice has the same effect on those contexts. A terminal first action can simulate a former action only if that former action was already terminal, so the terminal pass restricts pairs to those containing a direct halt predecessor.

For every original reachable abstract window at a or b, compute the old one-step target configuration and map its state through the quotient. Starting from the keeper and the same complete window, run the final modified table. Accept the case only if that target state, head position, and full eleven-cell tape are reached after a positive number of transitions at most 120, without leaving the window. Returning to the keeper is allowed. Exact repeated local configurations are rejected as loops. Halting before the target is rejected.

An accepted merger would supply a uniform finite positive simulation. The original abstract window invariant and induction over old steps would then give a PA-formalizable preservation of blank halting. No accepted merger was found in the recorded runs.

## Pruning and coverage

The two unknown rows are treated asymmetrically for efficiency, not for semantic restriction. Fix the read-zero row first. Run every read-zero case until it succeeds, fails, or requests the unknown read-one row. A failure rejects that first row. For a surviving first row, enumerate the read-one row and check all suspended cases plus all original read-one cases. A read-zero case that finished without requesting the other row is independent of that row's subsequent choice. Every accepted pair is rechecked against all cases in the final table.

The working-target pass tests all 18,528 unordered noninitial state pairs per 194-state table. Across 41 tables this is 759,648 pairs. Counts of partial survivors in the logs describe pruning, not distinct successful machines or all possible Turing machines.

## Reproduction

Python 3 and a C++17 compiler are sufficient. No network or proof assistant is required.

```
python3 replay.py --output /new/replay-directory
```

This compiles both search programs, checks positive controls, and reruns both passes on every frozen input using two parallel workers by default. It takes several minutes, depending on hardware. `--jobs 1` runs sequentially. `--quick` checks only the two positive controls and the integrity of recorded input/result bindings; it does not replay the negative frontier search.

The positive working-target fixture has two identical working controls and must produce their exact merge. The terminal fixture has two identical direct-halting controls and checks the separate terminal-target pass. They demonstrate that the search accepts valid reductions; they do not by themselves establish the implementation's general correctness.

## Provenance

The finite-window abstract semantics and motivation derive from the supplied PA194 `search/action_merge.cpp` and later PA194N physical-search artifacts. The new element here is simultaneous synthesis of both keeper rows with repeated execution of those rows permitted. The table inputs come from the current ProveIt snapshot and census; original licenses are retained. No claim of a new Lean or Rocq theorem is made.
