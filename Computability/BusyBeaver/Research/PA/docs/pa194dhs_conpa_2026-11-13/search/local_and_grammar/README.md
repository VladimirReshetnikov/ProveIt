# Additional searches around PA194 and PA194DHS

These experiments did not yield a machine below 194 working states. Their
negative results concern precisely the finite filters and timed search budgets
specified here. They are not state lower bounds. The accepted PA194DHS machine
is certified separately; its correctness does not depend on these experiments.

## Finite screens

| Input | Method | Window radius | Local step bound | Candidates |
|---|---|---:|---:|---:|
| Primary PA194 | Common-action pair contraction, all initial tapes | 4 | 80 | 0 |
| Primary PA194 | Common-action pair contraction, blank-start abstraction | 6 | 120 | 0 |
| Top-only-Shift PA195 experiment | Common-action pair contraction, blank-start abstraction | 6 | 300 | 0 |
| New PA194DHS | Common-action pair contraction, blank-start abstraction | 7 | 300 | 0 |
| New PA194DHS | Incoming-edge bypass, all initial tapes | 7 | 300 | 0 |

The pair filter allows every working control except the start as a merge
endpoint. A trial row action writes either bit, moves either way, and targets
an existing working control. For every abstract local context, its bounded
continuation must reproduce the old transition's complete window, head and
control. It may not visit another modified control before reaching that
endpoint. This is a sufficient and incomplete rule. Radius r means a window
of 2r+1 cells. Newly exposed boundary bits are arbitrary; consequently the
blank-start window closure is an overapproximation, not a finite run test.

The incoming-edge filter removes a non-self-looping control only when each
incoming row can separately be replaced by a first action whose unchanged
continuation simulates that incoming row followed by one removed-control
transition. It forbids intermediate visits to the removed control or any
rewritten incoming row. Its finite context and time bounds leave many other
machine transformations outside the search.

The added `pair_join.cpp` experiment permits the replacement to meet a later
configuration of the old computation, rather than only its immediate
successor. The old prefix and replacement path must avoid rewritten controls
until their common endpoint; both preserve the complete window. No candidate
was returned for DHS at radius 4 (old-prefix bound 40, replacement bound 120),
DHS at radius 6 (bounds 80 and 240), or top-only PA195 at radius 6 (bounds 80
and 240). The latter two abstract closures contain respectively 274,589 and
268,907 state/window pairs. These are additional bounded exploratory screens.

A separate exhaustive screen tries all 7! orders of the six logical heads
and the diagonal-vacuity head, with the latter's parameter independently
chosen from D, H and A. The seed parenthesization is fixed. All 15,120 cases
were evaluated. The minimum fitness is 59 (135 fixed controls + 59 = 194);
only the unchanged DHS case scored at most 60. The CSV records each case.
Fitness is a compiler filter and is not a replacement for physical or logical
validation of a newly generated machine.

## Timed grammar searches

The precise completed counts and seeds are in `SUMMARY.json`; full progress
logs are in `recorded/`. The DHS runs optimize a 135-control fixed part, so
fitness 58 would be a prospective 193-state table. The top-only run has a
136-control fixed part, so fitness 58 would be a prospective 194-state table.
All three runs remained at fitness 59. Their proposal counts count mutation
slots, including skipped mutations, repeated trees, and rejected proposals.
They do not count distinct grammars or verified Turing machines.

`reassociate.cpp` rotates shared subtrees, retaining the input macro sequence.
The top-only input is fully expanded to 190 tokens. The DHS reassociation
input may retain atomic two- and four-increment macros; it performs no
position-based parameter mutation. `ordered_search.cpp` additionally changes
head order and local parameter names, using a fully expanded 190-token seed.
Every candidate requires separate source, startup, physical and mathematical
verification before it could be accepted.

The fold evaluator includes fixed controls 41, 330 and 331 as possible
endpoints, in addition to AX readers. It requires pure incoming bit-preserving
right moves and checks all selected two-cell folds simultaneously. Fixed
controls absent from an input supply no candidates.

An earlier exploratory top-only run mixed opaque increment macros with
position-based mutations. It was discarded after the indexing mismatch was
noticed and is not part of these reported results. The normalized top-only
run included here does not have that mismatch.

## Source invariant inspection

The new DHS Boolean abstraction has 263,236 reachable (source-site, mask)
pairs and reaches all 3,650 source sites. Exactly two decrement sites are
always zero: site 26 tests X and site 3553 tests D. Both are already used by
the construction's zero-test specializations. There are no always-positive
decrement sites in this abstraction. `recorded/source_invariants.json`
records this inspection; the machine package independently recomputes and
checks the Boolean closure and its preservation theorem's finite hypotheses.

## Replay

From any working directory, with Python 3 and a C++17 compiler:

```sh
python3 run_searches.py --output /new/temporary/directory
python3 run_searches.py --output /another/new/directory --grammar
```

The first command replays the finite local screens and the 15,120-case order
screen. The second adds two 600-second runs and one 120-second run. For a
short smoke run, use `--grammar-seconds 1 --top-seconds 1`. Timed proposal
counts depend on processor speed and system load. All inputs are frozen;
no repository checkout or network access is required.

The files derive from earlier supplied research implementations, with the
specific local modifications listed in `PROVENANCE.json`. Original license
notices are retained in `licenses/`. No binary executable is included.
