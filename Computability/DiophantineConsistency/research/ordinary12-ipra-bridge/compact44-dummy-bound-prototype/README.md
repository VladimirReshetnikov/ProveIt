# Local mixed-width low-mask bounds

For every model of `IΣ₁` and model natural `x < 2⁶⁷`, the three theorems in
`CompactDummyBound` prove, respectively,

```
NoCarry(x, 2⁶⁷−1) → x = 0,
NoCarry(x, 2⁶⁷−2) → x ≤ 1,
NoCarry(x, 2⁶⁷−4) → x ≤ 3.
```

The powers are the internal model exponential and `NoCarry` is the existing
model bitwise predicate. The first two cases specialize the existing
all-ones lemmas; the third peels two low bits and applies the all-ones lemma
to the remaining 65-bit part. The last case permits 0–3 and does not impose
an invalid Boolean bound on the compact44 dummy.

All three local digit-bound and no-carry hypotheses are explicit. The
finite recipe check identifies these patterns with the retained standard
compact44 MC, but this theorem does not prove the actual MC model-digit
identities or derive local no-carry from the graph. It also does not prove a
global carry bound, clean reset, machine simulation, checker calibration,
iPRA derivability, or the consistency equivalence. These are conditional
model-level results in classical Lean metatheory.

## Evidence

Exploratory session 12267 exited 1 on arithmetic rewrites and had a linter
warning; its [source](observations/attempt01.lean) and [log](observations/attempt01.log)
are retained, and its dummy-case `sorryAx` is not proof evidence. Corrected
session 66161 [exited 0](observations/attempts.txt) with [no warnings or sorryAx](observations/attempt02.log).
The [paired replay](replay.py) rechecks the independently audited 24-module
window-model parent and compiles this suffix over matched author and peer
providers, checking direct imports and matching objects. It does not rebuild
the inherited chains; the parent audit has no complete axiom inventory, and
Foundation outer-wrapper and package-transitive/dynamic ancestry limitations
remain. Resource sampling is not a continuous whole-process-tree hard quota.

Outer session 67152 [exited 0](evidence/terminal.txt), printing receipt
SHA-256 `7332c7a3e4fc13cfaa87308b25349d740ca8fb1c1864b6859640d13a4a294b15`.
The [receipt](evidence/receipt.json) records both compiler and direct-import
checks exiting 0 and matching objects; [author](evidence/author.log) and
[peer](evidence/peer.log) reports have only `propext`, `Classical.choice` and
`Quot.sound`, with no warnings or `sorryAx`. Independent review of this new
suffix remains required. When the pinned temporary parent remains available
and the Lean slot is free, reproduce with:

```
python3 -I -S replay.py --output /tmp/ipra-compact-dummy-bound-pair-new
```
