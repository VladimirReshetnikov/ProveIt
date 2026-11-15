# Startup-compatible reduction experiments

## Result and scope

This subtask did **not** establish a blank-start machine with fewer than 194
working states. It investigated repairs of the previously known 193-state
runtime core, including combinations of row edits and the two new symmetric
witness designs constructed in the present research session. The exact
counts are recorded in `SUMMARY.json`; none is a lower bound on possible
consistency machines.

The starting repository commit was
`3c3bf00e3132d31d328a7bcfe79761ef238eced3`. The primary native 194-state table
has SHA-256
`e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54`.
The known core identifies 301 with 88 and replaces the rows

```
88 0 0 L 51
51 0 0 R 122
```

Its 386-row table is `core193.native.tm`, SHA-256
`50f7be44afb63293365270a83111299247d12d140614e4b4c9a52786163acb53`.
The primary start 74 reaches an outward ray in state 35 at time 92.

## Why the obvious reduction breaks startup

On an already well-formed register file, replacing `51:0`'s target 16 by
122 preserves first-register marking: the next cell is 1, and both 16 and
122 have transition `(0,L,1)` on 1. During the blank initialization, however,
the same command is invoked on an unfinished blank suffix. State 16 on 0
writes a new 1, whereas state 122 on 0 does not. In the reduced table the
first failed attempt to extend that suffix occurs at step 86, with state 51
at head position 12 and ones only at positions -3 and 1. The resulting
execution reaches `35:0 = (1,R,35)` in the blank exterior. A runtime
preservation argument therefore cannot supply the missing initializer.

## Searches performed

1. The 4,780 abstract source outcomes for the primary table were independently
   replayed. Only arithmetic-box internals were absent from the abstract
   source traces; there was no unused ordinary controller row to freely
   repurpose.
2. A finite physical-register screen varied every one-step replacement of
   either row of states 0, 64, 74, 94, 66, 198, 113, 16, 40, 54 and 97. The
   tests checked marking, increment and both decrement cases, using fixed
   zero/positive cases and reproducible random complete register files.
   Different well-formed spare suffixes were allowed. The 3,093 survivors
   were filtered through every abstract source contract whose original
   execution touched the changed row. Twenty-eight edits survived.
3. Every blank start of each of these 28 edited cores was classified:
   5,404 simulations, 57 halts and 5,347 outward rays, with no limit reached.
4. All 15,120 combinations of these alternatives, with at most one
   replacement for each affected row, were screened from all 193 starts.
   Among 2,918,160 runs, there were 24,060 halts, 2,882,220 rays and 11,880
   bounded limits. No complete frame was found at the twenty early scheduler
   sites 25 through 44. These combination edits were search proposals, not
   individually proved simultaneous runtime transformations.
5. A second search combined the preceding alternatives with the repository's
   recorded neutral controller edits. It tested 12,167 distinct pairs with
   at least one edit at 16:0, 24:0, 35:0 or 45:0, the default startup failure
   path. Starting at 74 and allowing header length at least 38, it found no
   complete frame at sites 25 through 44. Outcomes were 8,891 rays, 2,818
   outward drift patterns, 105 exact cycles and 353 bounded limits.
6. The same 301-to-88 reduction was applied to the new PA194H5XS and
   PA194JH5XS tables. In each resulting 193-state table all 193 blank starts
   were classified as two halts and 191 rays, with no limit reached.

The physical-register tests are finite evidence, not universal arithmetic
box proofs. Abstract source checks retain the oracle interface. Accordingly,
the neutral-row search is a candidate-generation method, and no new
unconditional source-to-machine theorem is claimed for all its edits.
The header-38 acceptance condition in the second search is deliberately
permissive. It is not a proved minimum header for the primary source grammar:
the primary core's abstract check at 38 fails at site 3247 on the positive
decrement branch, and at 39 it fails at site 3248. Header 40 passes all
4,780 abstract source outcomes. Allowing these additional short headers broadens the
unsuccessful startup screen rather than asserting that they are sound seeds.

## Exact stopping criteria

The frame recognizer checks the entire finite support, arbitrary translation,
the source path, the padding, and at least ten complete unary register
blocks. It deliberately allows arbitrary first-nine register values, a
larger set than the sound startup theorem permits. Failure to find a frame
in this larger set therefore does not miss a sound seed within the stated
site and header scope.

A `limit` is inconclusive: it means 200,000 transitions were exhausted, the
head left the interval [-20,000,20,000], or the finite support exceeded
20,000 ones. No divergence claim is made for these runs.

A ray is recognized when a cyclic chain of 0-transitions moves monotonically
into an entirely blank exterior. The added drift criterion is also exact:
the same state is reached twice on a fresh blank exterior boundary, the
second boundary is farther outward, and the intervening trace never crosses
the first boundary toward the old tape. The finite excursion can then be
translated and repeated indefinitely. Exact cycles compare the state,
absolute head, and the complete finite set of ones; sampling every 128
transitions only delays detection.

## Files and attribution

`explore.py`, `append_search.py`, `box_row_search.py` and
`filter_neutral.py` contain the new candidate-generation and filtering work.
The exact baseline input tables and source arrays are supplied alongside
them. `symbolic_runtime.py` is inherited from the primary PA194 packet.
The startup search sources are adapted from
`pa_sub194_research_2026-11-13/research/reduction/search_startup.cpp`.
The existing neutral-row input table came from the same packet.

`search_startup_multi.cpp` adds simultaneous row edits to the repository tool.
`search_startup_all38.cpp` further adds exact cycles and outward-drift
detection, permits a header of at least 38, and retains every blank start.
`search_startup_root38.cpp` uses the same detection and header rules with
start fixed to 74. The original single-edit replay used the unmodified
repository search tool, retained here as `search_startup_single.cpp`.
The generated edit lists, native tables and unabridged final logs are retained.
Compiled local executables and exploratory stdout files are not necessary
for the research deliverable.

## Reproduction

Python 3 and a C++17 compiler suffice. From this directory, run
`python3 verify.py` for hash/reconstruction checks, the four header checks,
all single-edit startups, and both new-design core startup classifications.
Run `python3 verify.py --full` to add the two broad startup screens; it takes
approximately two minutes on the original machine, but timing depends on
hardware. Compilers and generated edit lists are placed in a temporary
directory. The fixed receipt logs are not overwritten.

To regenerate the earlier candidate screens, run `python3 append_search.py`,
`python3 box_row_search.py`, and `python3 filter_neutral.py`, in that order.
Those exploratory scripts write their own result JSON files beside the source.
The full raw 3,093-candidate physical-screen output is reproducible rather
than duplicated in this release. Its 28 surviving candidates are retained
as the small input `box_source_neutral.json`.
