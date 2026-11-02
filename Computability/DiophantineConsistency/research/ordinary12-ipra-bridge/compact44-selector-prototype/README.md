# Compact44 low selector-count bound

`CompactSelector.selector_at_most_one` proves in every `IΣ₁` model that,
for model naturals `n,P`,

```
n < 2¹⁰  and  NoCarry(n + 2¹⁰P, 2⁵¹ − 2)  imply  n ≤ 1.
```

`NoCarry` is the existing internal bitwise predicate and powers are the
model's internal exponential. `P` is completely arbitrary: the theorem does
not require the full payload or its additions to be globally carry-free. It
uses the low 51-bit digit and the all-ones mask lemma, then reduces that
digit modulo 2¹⁰. The two inequalities and no-carry premise are explicit;
the theorem does not establish that the actual graph supplies them.

This is one local component of the proposed compact44 selector/copy decoder.
It does not identify a unique selected tile, prove the copy or empty-cell
cases, bind a compact44 payload, simulate the 943-tile machine, calibrate
the checker, prove existence of an iPRA proof, or establish the final
consistency equivalence. It is a conditional model theorem in classical Lean
metatheory, not an object-level iPRA derivation.

## Evidence

Exploratory attempt 01 exited 1 on one modulo rewrite; its
[source](observations/attempt01.lean) and [log](observations/attempt01.log)
are retained, and its `sorryAx` is not proof evidence. Corrected session
78212 [exited 0](observations/attempts.txt) with [no warnings or sorryAx](observations/attempt02.log).
The [paired replay](replay.py) rechecks the independently audited 24-module
window-model parent and compiles this suffix over the matched author and peer
providers, checking direct imports and matching objects. It does not rebuild
the inherited chains; the parent audit has no complete axiom inventory, and
Foundation outer-wrapper and package-transitive/dynamic ancestry limitations
remain. Resource sampling is not a continuous whole-process-tree hard quota.

Outer session 11053 [exited 0](evidence/terminal.txt), printing receipt
SHA-256 `b2c50f1f34070e10a13d28f3cc84fe473f4f0f8d3e1d2e38dbbac08f3ad012b3`.
The [receipt](evidence/receipt.json) records both compiler and direct-import
checks exiting 0 and matching objects; [author](evidence/author.log) and
[peer](evidence/peer.log) reports have only `propext`, `Classical.choice` and
`Quot.sound`, with no warnings or `sorryAx`. Independent review of this new
suffix remains required. When the pinned temporary parents remain available
and the Lean slot is free, reproduce with:

```
python3 -I -S replay.py --output /tmp/ipra-compact-selector-pair-new
```
