# Compact44 tile-payload value bounds

`CompactTilePayload.value_bounds` proves in an arbitrary model of `IΣ₁` that,
for model naturals w,n,e,s with the explicit bounds

```
w < 2⁸,  n < 2⁹,  e < 2⁸,  s < 2⁹,
v = w + 2⁸n + 2¹⁷e + 2²⁵s + 127·2³⁴,
```

one has `0 < v < 2⁴¹`, with the last power interpreted by the model's
internal exponential. This is the tile-value formula in the retained
compact44 recipe: its high seven fixed bits represent four occupancy and
three anchor bits. The proof builds the 17-, 25- and 34-bit field bounds
using discrete successor bounds; it does not use unbounded computation of a
large fixed coefficient.

The theorem is conditional on the four label bounds. It does not identify
w,n,e,s with any of the actual 943 rows, prove the recipe generates the
selected literal coefficients, derive no-carry from the graph, simulate the
machine, calibrate its checker, prove existence of an iPRA proof, or establish
consistency equivalence. It is a conditional model-level result in classical
Lean metatheory.

## Evidence

Exploratory session 31346 exited 1 because its first loose bound used a false
arithmetic equality; its exact [source](observations/attempt01.lean) and
[log](observations/attempt01.log) are retained, and `sorryAx` is not evidence.
Corrected session 41159 [exited 0](observations/attempts.txt) with [no warnings or sorryAx](observations/attempt02.log).
The [paired replay](replay.py) rechecks the independently audited 24-module
window-model parent and compiles this suffix over matched author and peer
providers, checking direct imports and matching objects. It does not rebuild
the inherited chains; the parent audit has no complete axiom inventory, and
Foundation outer-wrapper and package-transitive/dynamic ancestry limitations
remain. Resource sampling is not a continuous whole-process-tree hard quota.

Outer session 91474 [exited 0](evidence/terminal.txt), printing receipt
SHA-256 `74d5ee9ae9b318f4798fdd4efe8278cc0b8318f0d29147ec9bd0c39a0ce28fbd`.
The [receipt](evidence/receipt.json) records both compiler and direct-import
checks exiting 0 and matching objects; [author](evidence/author.log) and
[peer](evidence/peer.log) reports have only `propext`, `Classical.choice` and
`Quot.sound`, with no warnings or `sorryAx`. Independent review of this new
suffix remains required. When the pinned temporary parents remain available
and the Lean slot is free, reproduce with:

```
python3 -I -S replay.py --output /tmp/ipra-compact-tile-payload-pair-new
```
