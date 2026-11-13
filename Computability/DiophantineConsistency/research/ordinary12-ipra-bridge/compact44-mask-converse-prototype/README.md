# Compact44 prescribed low-mask converse cases

`CompactSelectorConverse.zero_mask` and `CompactSelectorConverse.one_mask`
prove in every `IΣ₁` model, with internal exponential and the existing
bitwise `NoCarry` predicate,

```
NoCarry(0,       2⁵¹ − 2)
NoCarry(1+2⁵¹,   2⁵¹ − 2).
```

These are the two intended aggregate values for an empty cell and a valid
single-selected copy cell. The second proof checks model bit positions below
and above the 51-bit boundary without assuming arbitrary high payload sums
are carry-free. The theorems do not establish that a particular selector sum
has either of these values; a separate finite-sum composition is needed.

These are conditional model-level building blocks in classical Lean
metatheory, not a binding of the 943-entry compact44 table, an all-model
machine simulation, checker calibration, proof existence in iPRA, or the final
consistency equivalence.

## Evidence

Exploratory session 70332 exited 1 on a bit rewrite and had a linter warning;
session 34977 exited 0 but still warned. Both exact sources and logs are
retained under `observations/`; the first `sorryAx` is not proof evidence.
Corrected session 11492 [exited 0](observations/attempts.txt) with [no warnings or sorryAx](observations/attempt03.log).
The [paired replay](replay.py) rechecks the independently audited 24-module
window-model parent and compiles this suffix over matched author and peer
providers, checking direct imports and matching objects. It does not rebuild
the inherited chains; the parent audit has no complete axiom inventory, and
Foundation outer-wrapper and package-transitive/dynamic ancestry limitations
remain. Resource sampling is not a continuous whole-process-tree hard quota.

Outer session 92825 [exited 0](evidence/terminal.txt), printing receipt
SHA-256 `3be33d52186afef78605cfa08d2f73e95b56e5577b7c229e46d7a6a8e13a8a52`.
The [receipt](evidence/receipt.json) records both compiler and direct-import
checks exiting 0 and matching objects; [author](evidence/author.log) and
[peer](evidence/peer.log) reports have only `propext`, `Classical.choice` and
`Quot.sound`, with no warnings or `sorryAx`. Independent review of this new
suffix remains required. When the pinned temporary parents remain available
and the Lean slot is free, reproduce with:

```
python3 -I -S replay.py --output /tmp/ipra-compact-mask-converse-pair-new
```
