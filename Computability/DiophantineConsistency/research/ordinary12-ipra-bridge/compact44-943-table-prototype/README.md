# Original compact44 ordered 943-row table

`Compact943Data.rows` is a Lean literal list of 943 quadruples. Lean proves
its length is exactly 943, checks all four fields against the 8/9/8/9-bit
bounds, and exposes `row_bounds` for each external `Fin 943` index. The
length and aggregate width checks report no axioms; the indexed theorem
reports `propext` and `Quot.sound`.

The fail-closed [ordered-row checker](check_rows.py) separately hashes the
retained original `36-small-tuple/coefficients/wang943_tiles.json` and
compares every source-list row in order and with strict source syntax. Its
pinned JSON SHA-256 is
`66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f`, the
hash recorded by the compact44 recipe. It checks the source/data relation
externally; it is not a Lean semantics theorem about JSON. The
[controls](observations/checker-controls.json) record normal exit 0 and
optimized-mode and modified-first-row exits 1.

The list alone does not prove its relationship to the selected K coefficient,
bind the other compact44 ports, establish correspondence to K215 actions or
all-model machine simulation, calibrate the checker, prove existence of an
iPRA proof, or establish consistency equivalence. The external `Fin 943`
index type must not be confused with an arbitrary internal nonstandard range.

## Evidence

Exploratory session 10313 [exited 0](observations/attempts.txt), and its
[log](observations/attempt02.log) reports the three theorems without warnings
or `sorryAx`. The [paired replay](replay.py) pins source, checker, original
JSON and the independently audited 24-module window-model provider; it runs
the exact ordered-row checker before and after two matched suffix compiles,
checks direct imports and compares objects. It does not rebuild the inherited
chains; the parent audit has no complete axiom inventory, and Foundation
outer-wrapper and package-transitive/dynamic ancestry limitations remain.
Resource sampling is not a continuous whole-process-tree hard quota.

Outer session 58981 [exited 0](evidence/terminal.txt), printing receipt
SHA-256 `d2b5c30ae68b12c502e7621ef4a26840bb25ce9d9865a5b1fd8d9c4be3625650`.
The [receipt](evidence/receipt.json) records both compiler and direct-import
checks exiting 0 and matching objects. [Author](evidence/author.log) and
[peer](evidence/peer.log) logs have no warnings or `sorryAx`. Independent
review of this new packet remains required. When the pinned temporary parent
remains available and the Lean slot is free, reproduce with:

```
python3 -I -S replay.py --output /tmp/ipra-compact943-table-pair-new
```
