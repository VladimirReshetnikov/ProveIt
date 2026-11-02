# Finite selector extraction in an arithmetic model

For any external finite index type `ι` and model-valued function `f`,
`CompactSelectorSum.sum_le_one_cases` proves in an arbitrary `IΣ₁` model that
if `∑ i, f i ≤ 1`, then either every `f i` is zero or one index has value 1
and every other index has value zero. No separate Boolean hypothesis is
needed: the model order and finite-sum bound force it.

`CompactSelectorSum.selected_weighted` separately proves that, given the
single-selected-index predicate, `∑ j, a j * f j = a i` for arbitrary model
weights `a`. The index type is an external finite type; this does not assert a
selection over an internally nonstandard index range. It also does not bind
`ι` to the actual 943-entry compact44 language or establish its selector
sum, copy bound, machine simulation, checker calibration, iPRA proof, or
consistency equivalence. These are conditional model-level results in
classical Lean metatheory.

## Evidence

Exploratory attempt 01 failed because the available `sum_le_one_iff` is
specialized to standard naturals, while model elements are arbitrary; attempt
02 failed on a local rewrite. Their exact sources and logs are retained under
`observations/`, and their `sorryAx` reports are not proof evidence. Corrected
session 91796 [exited 0](observations/attempts.txt) with [no warnings or sorryAx](observations/attempt03.log).
The [paired replay](replay.py) rechecks the independently audited 24-module
window-model parent and compiles this suffix over matched author and peer
providers, checking direct imports and matching objects. It does not rebuild
the inherited chains; the parent audit has no complete axiom inventory, and
Foundation outer-wrapper and package-transitive/dynamic ancestry limitations
remain. Resource sampling is not a continuous whole-process-tree hard quota.

Outer session 66799 [exited 0](evidence/terminal.txt), printing receipt
SHA-256 `5a06980410fcf4f0305e4f9f1c5a9ba51b399ebe0bd93a99ea80722d84f52063`.
The [receipt](evidence/receipt.json) records both compiler and direct-import
checks exiting 0 and matching objects; [author](evidence/author.log) and
[peer](evidence/peer.log) reports have only `propext`, `Classical.choice` and
`Quot.sound`, with no warnings or `sorryAx`. Independent review of this new
suffix remains required. When the pinned temporary parents remain available
and the Lean slot is free, reproduce with:

```
python3 -I -S replay.py --output /tmp/ipra-compact-selector-sum-pair-new
```
