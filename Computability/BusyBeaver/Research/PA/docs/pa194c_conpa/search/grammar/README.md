# Additional searches for a 193-state allocation

These are completed, optional heuristic searches. None found the target of
59 effective AX readers with zero scanner penalty and 134 fixed controls.
The initial score 60 remained best in all three runs. These results establish
no lower bound and do not certify any additional machine.

`start194.txt` encodes the actual accepted PA194 grammar and its 134 fixed
controls; `start194C.txt` changes the six controller rows to the cached-head
protocol. Both inputs use the same 190-token AX word and parameter roles.
`leaf_attrs.txt` records the scanner attributes of the inherited macro leaves.

`screen.cpp` is inherited from the PA194/PA195 research packets. The two new
search variants are based on their compatible-fold and plateau searches:
`search193.cpp` rotates all occurrences of a selected DAG subtree together;
`search193_occ.cpp` additionally rotates an individual occurrence with 35%
probability, allowing new sharing patterns. The latter uses a warmer
annealing schedule and admits pool scores through 62 instead of 61.
Both compact their interning pools every 10,000 proposals. The dormant
parameter-renaming code is not activated in these runs.

The screen first computes a maximum matching of eligible history-bit folds.
When its effective-reader estimate is at most 64, it checks simultaneous
compatibility of selected folds by explicit two-cell executions (at most 20
steps) and finds a maximum compatible subset within that implemented family.
The objective adds penalties for scanner zero runs, transient increment paths,
source depth, and forbidden leaf positions. Zero penalty is only a screening
condition. A positive numerical hit would require source-CFG equality and the
complete independent physical and startup checks before acceptance.

From this directory, using a C++17 compiler:

```sh
g++ -O3 -std=c++17 search193.cpp -o search193
g++ -O3 -std=c++17 search193_occ.cpp -o search193_occ
./search193 start194.txt leaf_attrs.txt replayA 600 2026111405
./search193_occ start194.txt leaf_attrs.txt replayB 600 2026111406
./search193_occ start194C.txt leaf_attrs.txt replayC 600 2026111407
```

`runA.log`, `runB.log`, and `runC.log` contain the completed original logs.
The CSV files contain only a header because there were no target hits.
`results.json` records the exact proposal counts and file hashes. Counts
include repeats and no-op proposals; they are not counts of distinct machines.
Wall-clock limits make final proposal counts dependent on the machine.
Saved intermediate pool grammars are omitted because they are unverified
search seeds, not additional constructions.

The supplied original licenses remain under `../../construction/licenses/`.
See the package provenance and inherited PA194 provenance for source credits.

## Final freshness supplement

`fresh_frontier/` adds the new 68-reader/eight-fold starting allocation,
its source and startup audit, and two supplementary search attempts. Their
600-second budgets were interrupted before completion. The last recorded
progress is 11,512,000 / 11,484,000 proposals at 571.320 / 571.352 seconds,
with no target hit; accepted counts were not recorded. The partial logs and
explicit interrupted-status receipts are included without extrapolation.
