# Local compact decoder for the ordered 943-row table

`Compact943Decoder.tileValue` uses the indexed Lean `Fin 943` table and the
compact44 recipe's value formula. `tileValue_bounds` proves each value is
strictly between 0 and the model's internal 2⁴¹. `count_bound` proves that
if each model selector `fᵢ ≤ 1`, their sum is below 2¹⁰. This uses the
**external fixed finite type** `Fin 943`, not an arbitrary internally
nonstandard index range.

Under the explicit hypotheses `∀i, fᵢ ≤ 1` and `W < 2⁴¹`,
`Compact943Decoder.decode_iff` proves the local aggregate no-carry relation
is equivalent to either all selectors and W being zero, or exactly one
selector being 1 and W equaling that row's value. It instantiates the
audited finite-sum decoder and derives the value and count bounds from the
indexed table and the stated selector bound. It does not assume all payload
additions are globally carry-free.

The table's exact comparison to the retained original JSON is an external
ordered-row check, not a Lean theorem about JSON. This result does not prove
that the actual graph supplies the selector and W bounds or aggregate
no-carry relation; it does not bind the literal's K or full four-port tuple,
prove K215 simulation, calibrate the checker, produce an iPRA proof, or prove
consistency equivalence. It is a conditional model-level theorem in
classical Lean metatheory.

## Evidence

Exploratory author session 79230 [exited 0](observations/attempt01.txt), with
[no warnings or sorryAx](observations/attempt01.log). The [paired replay](replay.py)
pins the independently audited local-iff, ordered-table and tile-bound
parents, verifies matching provider ancestry and exact added seed objects,
re-runs the table's external ordered-row check, and compiles the suffix over
fresh author and peer overlays with direct-import checks. It does not rebuild
the inherited chains. The window parent audit has no complete axiom inventory,
and Foundation outer-wrapper and package-transitive/dynamic ancestry
limitations remain. Resource sampling is not a continuous whole-process-tree
hard quota.

Outer session 31869 [exited 0](evidence/terminal.txt), printing receipt
SHA-256 `e0b721312d13d88ed5fadc7b83d2e8d1e95dd5a73ae559e8c40386f9b171bb4d`.
The [receipt](evidence/receipt.json) records both compiler and direct-import
checks exiting 0 and matching objects; [author](evidence/author.log) and
[peer](evidence/peer.log) reports have only `propext`, `Classical.choice` and
`Quot.sound`, with no warnings or `sorryAx`. Independent review of this new
suffix remains required. When the pinned temporary parents remain available
and the Lean slot is free, reproduce with:

```
python3 -I -S replay.py --output /tmp/ipra-compact943-decoder-pair-new
```
