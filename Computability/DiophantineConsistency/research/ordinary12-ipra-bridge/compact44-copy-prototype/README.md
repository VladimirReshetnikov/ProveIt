# Compact44 empty and selected copy cases

`CompactCopy.empty_copy` and `CompactCopy.selected_copy` prove two elementary
arithmetic implications in every model of `IΣ₁`:

```
W < A,  A ∣ W                         imply  W = 0;
0 < v < A,  W < A,  A ∣ (A − v + W) imply  W = v.
```

They work for arbitrary model naturals A, v, W; in the compact44 application
A would be the internal `2⁴¹`. No global carry-free payload assumption is
used. These implications cover the empty and selected copy arithmetic once
their bounds and divisibility premises have been obtained. They do not derive
those premises from actual selector sums or the 51-bit mask.

This is a conditional model-level result in classical Lean metatheory. It
neither identifies a unique selected tile nor binds the compact44 payload,
simulates the 943-tile machine, calibrates the checker, proves existence of
an iPRA proof, or establishes the final consistency equivalence.

## Evidence

Exploratory sessions 4040 and 45517 exited 1 on local inequality/normalization
issues; their exact sources and logs are retained under `observations/`, and
their `sorryAx` reports are not proof evidence. Corrected session 21439
[exited 0](observations/attempts.txt) with [no warnings or sorryAx](observations/attempt03.log).
The [paired replay](replay.py) rechecks the independently audited 24-module
window-model parent and compiles this suffix over the matched author and peer
providers, checking direct imports and matching objects. It does not rebuild
the inherited chains; the parent audit has no complete axiom inventory, and
Foundation outer-wrapper and package-transitive/dynamic ancestry limitations
remain. Resource sampling is not a continuous whole-process-tree hard quota.

Outer session 64112 [exited 0](evidence/terminal.txt), printing receipt
SHA-256 `92b2822864ae357cbeed9daa14b795edf891b5e0f80f5156c4bc087b87ac1be4`.
The [receipt](evidence/receipt.json) records both compiler and direct-import
checks exiting 0 and matching objects; [author](evidence/author.log) and
[peer](evidence/peer.log) reports have only `propext`, `Classical.choice` and
`Quot.sound`, with no warnings or `sorryAx`. Independent review of this new
suffix remains required. When the pinned temporary parents remain available
and the Lean slot is free, reproduce with:

```
python3 -I -S replay.py --output /tmp/ipra-compact-copy-pair-new
```
